{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, DeriveFunctor, DeriveTraversable, DeriveFoldable, BangPatterns, Rank2Types, LambdaCase #-}
module Simulate.DEvalTypes where -- this module exists only to work around template haskell annoyances...

import Simulate.ProcDefs

import Data.Array.IArray (Array, (!))
import Data.Array.IO
import qualified Data.Array.IArray as IArray
import Data.Maybe
import Data.Either
import Data.Foldable (Foldable, foldMap)
import Data.Monoid (Sum(..))
import Data.IntMap (IntMap, insert, alter, delete, empty, lookup, fromList, updateLookupWithKey, size)
import Data.Map.Strict (Map, toList)
import Data.Int (Int64)
import Data.List (isSuffixOf, sortBy)
import Data.Word (Word8, Word16, Word32, Word64)
import Data.Bits (popCount,rotateL)
import Data.Bits.Lens (bitAt, bits)
import Control.Applicative
import Control.Lens

data Checked a = OK a | Bad deriving (Show, Eq, Functor, Traversable, Foldable)   -- Maybe like type for extra checking on simulation only, may not be used to make decisions

checked :: Lens' (Checked a) a
checked = lens (\case {OK x -> x; Bad -> error "BAD value"}) (flip (fmap . const))
{-# INLINE checked #-}

unCheck :: b -> (a -> b) -> Checked a -> b
unCheck _ f (OK x) = f x
unCheck z _ (Bad ) = z

toChecked :: Maybe a -> Checked a
toChecked (Just x) = OK x
toChecked Nothing  = Bad

newtype StackIndex = IxS Int deriving (Show, Eq, Ord, Ix, Enum)
newtype QueueIndex = IxQ Int deriving (Show, Eq, Ord, Ix, Enum)
newtype LoadIndex  = IxL Int deriving (Show, Eq, Ord, Ix, Enum)

newtype QueueBase = QB Int deriving (Show, Eq)
newtype LoadBase  = LB Int deriving (Show, Eq, Ord, Enum, Num, Real, Integral)

data CacheTag a = FourWay !(Maybe a) !(Maybe a) !(Maybe a) !(Maybe a) !LRU4
data LRU4 = LRU4 !QuadElem !QuadElem !QuadElem

tagLRU :: Lens' (CacheTag a) LRU4
tagLRU f (FourWay a b c d x) = fmap (\x' -> FourWay a b c d x') (f x)
{-# INLINE tagLRU #-}

type AH_Index = Word16

allocHeapSize :: Integral a => a
allocHeapSize = 512
allocHeapMax :: Integral a => a
allocHeapMax = 511
compactAllocRange :: Int
compactAllocRange = 64 -- 32
compactAllocMask :: Word64
compactAllocMask = 0-1 -- (1 `shiftL` compactAllocRange) - 1 

cacheIxSize,nWays :: Int
cacheIxSize = 128
nWays       = 4
initCTag :: CacheTag a
initCTag = FourWay Nothing Nothing Nothing Nothing (LRU4 H I J)

oldLRU4 :: LRU4 -> QuadElem
oldLRU4 (LRU4 a b c)
  | a /= H && b /= H && c /= H = H
  | a /= I && b /= I && c /= I = I
  | a /= J && b /= J && c /= J = J
  | otherwise                  = K

setLRU4 :: QuadElem -> LRU4 -> LRU4
setLRU4 x (LRU4 a b c)
  | x == a    = LRU4 a b c
  | x == b    = LRU4 b a c
  | x == c    = LRU4 c a b
  | otherwise = LRU4 x a b

dropLRU4 :: QuadElem -> LRU4 -> LRU4
dropLRU4 x r@(LRU4 a b c)
  | x == a    = LRU4 b c (oldLRU4 r)
  | x == b    = LRU4 a c (oldLRU4 r)
  | x == c    = LRU4 a b (oldLRU4 r)
  | otherwise = LRU4 a b c

data ReadState = FreeLine | NodeExt | FreshData | FreshFun | BlackHoled | Updated | SharedRead deriving (Show, Eq)

data RCMod = RCDec | RCNop | RCInc | RCtwInc deriving (Show, Eq, Ord, Enum)
type RCRef = (RCMod, RefValue)
type RCHRef = (RCMod, HeapRef)

rcNopRef :: RCRef
rcNopRef = (RCNop, CVRef VoidRef)

extraRCInc :: RCMod -> RCMod
extraRCInc = succ

extraRCDec :: RCMod -> RCMod
extraRCDec = pred

data RefCounter = Zero | One | Two | Three | Four | Five | Six | Many deriving (Show, Eq, Enum)

incRefCount :: RefCounter -> RefCounter
incRefCount Zero   = error "resurrecting dead"
incRefCount Many   = Many
incRefCount x      = succ x

decRefCount :: RefCounter -> RefCounter
decRefCount Zero   = error "already dead"
decRefCount Many   = Many
decRefCount x      = pred x

type CodeLine = IOArray Word32 Instruction
type CodeCacheLine = (Word32, CodeLine)

ccLineWidth :: Word32
ccLineWidth = 4
ccSize :: Word32
ccSize = 32  -- 16

type CodeMem = IntMap Instruction

newtype Stack a = Stack [a] deriving (Functor)  -- TODO change into array with offset

emptyStack :: Stack a
emptyStack = Stack []

newtype Fifo a = Fifo [a]  -- TODO make an array instead

emptyFifo :: Fifo a
emptyFifo = Fifo []

nullFifo :: Fifo a -> Bool
nullFifo (Fifo xs) = null xs

enFifo :: a -> Fifo a -> Fifo a
enFifo x (Fifo ys) = Fifo (x:ys)

deFifo :: Fifo a -> (Fifo a, a)
deFifo (Fifo xs) = let x = last xs in x `seq` (Fifo (init xs), x)

emptyQuad :: Quad (Maybe a)
emptyQuad = Q Nothing Nothing Nothing Nothing
  
safePeek :: Getter (Stack a) (Maybe a)
safePeek = to safeP where
  safeP (Stack []   ) = Nothing
  safeP (Stack (x:_)) = Just x

type Body a    = FB (Checked a)
type BodyArg   = NodeArg RefValue PrimValue
type FixedBody = Body BodyArg
data StackNode = StNode !(Maybe RefValue) !FixedBody deriving (Show)

stNRef :: Lens' StackNode (Maybe RefValue)
stNRef f (StNode r b) = fmap (\r' -> StNode r' b) (f r)
{-# INLINE stNRef #-}
stNBody :: Lens' StackNode FixedBody
stNBody f (StNode r b) = fmap (\b' -> StNode r b') (f b)
{-# INLINE stNBody #-}

type ReadRef   = (RCMod, RefValue)
type ReadBody  = Body (RCMod, BodyArg)
type StackRead = (TempTopRV, ReadBody)
type TempTopRV = (Maybe (PtrTag, HeapRef), Maybe CompactValue)
type PrimVals  = Quad (Checked PrimValue)
emptyPrimVals  = Q Bad Bad Bad Bad
data NodeShape = NodeS | RawS Arity | PrimS | EmptyS                              deriving (Show, Eq)  -- Arity is number of elements on primitive side   EmptyS is a node without body
data StackMeta = StMeta !RefNeed !RefStatus !NodeTag !NodeShape                   deriving (Show)
type MetaSTop  = (RefNeed, (RefStatus, ValStatus), Maybe NodeTag, NodeShape)
emptyMetaSTop  = (WeakRef, (NoNR,NoCV), Nothing, EmptyS)
data StoredSN  = MemStN !(RefNeed, Maybe RefValue) !NodeTag !FixedBody
data RefStatus = HasNR | NoNR                                                     deriving (Show, Eq)
data ValStatus = HasCV | NoCV                                                     deriving (Show, Eq)    -- compacted value status
data RefNeed   = NeedRef | OnlyRef | SkipRef | WeakRef                            deriving (Show, Eq)    -- WeakRef for when the need is not yet known, OnlyRef for lazily converting a node to just a ref

data RewriteAction = CantRewrite | ApplyRewrite Arity | SelRewrite NodeElem deriving Show

data HeapNode = HNode !NodeTag !FixedBody deriving Show

printHNode :: HeapNode -> String
printHNode (HNode t xs) = case plainTag t of
  Con (cn,0) | "Czh" `isSuffixOf` cn -> [toEnum $ fromIntegral c] where PVal c = xs^.elemAt A
  _                                  -> show (HNode t xs) ++ "\n"
data HeapPart = HNInit !NodeTag !(Triple (Checked BodyArg)) | HNRest !(Quad (Checked BodyArg)) deriving Show

data HeapState = HeapState {_ahBounds :: !(HeapAddr, HeapAddr), _nursery :: IOArray AH_Index (Checked HeapPart),
  _ahInfo :: IOArray AH_Index ReadState, _freeLines :: !Word64, _nextFreeAddress :: Maybe HeapAddr,
  _cTags :: IOArray Int (CacheTag HeapAddr), _cData :: IOArray Int (Checked HeapNode), _cInfo :: IOArray Int ReadState,
  _loadDeallocs :: !Int, _loadDelays :: !Int, _allocProfile :: Map Tag Int}

ahBounds :: Lens' HeapState (HeapAddr,HeapAddr)
ahBounds = lens _ahBounds (\s x -> s {_ahBounds = x})
{-# INLINE ahBounds #-}
nursery :: Lens' HeapState (IOArray AH_Index (Checked HeapPart))
nursery = lens _nursery (\s x -> s {_nursery = x})
{-# INLINE nursery #-}
ahInfo :: Lens' HeapState (IOArray AH_Index ReadState)
ahInfo = lens _ahInfo (\s x -> s {_ahInfo = x})
{-# INLINE ahInfo #-}
freeLines :: Lens' HeapState Word64
freeLines = lens _freeLines (\s x -> s {_freeLines = x})
{-# INLINE freeLines #-}
nextFreeAddress :: Lens' HeapState (Maybe HeapAddr)
nextFreeAddress = lens _nextFreeAddress (\s x -> s {_nextFreeAddress = x})
{-# INLINE nextFreeAddress #-}
cTags :: Lens' HeapState (IOArray Int (CacheTag HeapAddr))
cTags = lens _cTags (\s x -> s {_cTags = x})
{-# INLINE cTags #-}
cData :: Lens' HeapState (IOArray Int (Checked HeapNode))
cData = lens _cData (\s x -> s {_cData = x})
{-# INLINE cData #-}
cInfo :: Lens' HeapState (IOArray Int ReadState)
cInfo = lens _cInfo (\s x -> s {_cInfo = x})
{-# INLINE cInfo #-}
loadDeallocs :: Lens' HeapState Int
loadDeallocs = lens _loadDeallocs (\s x -> s {_loadDeallocs = x})
{-# INLINE loadDeallocs #-}
loadDelays :: Lens' HeapState Int
loadDelays = lens _loadDelays (\s x -> s {_loadDelays = x})
{-# INLINE loadDelays #-}
allocProfile :: Lens' HeapState (Map Tag Int)
allocProfile = lens _allocProfile (\s x -> s {_allocProfile = x})
{-# INLINE allocProfile #-}
  
instance Show HeapState where
  show (HeapState (t,_) _ _ _ _ _ _ _ ld lc ap)  = "heap: " ++ show t ++ " deallocs: " ++ show ld ++ " loadDelays: " ++ show lc
--        ++ "\n" ++ (concatMap ((++ "\n") . show) $ sortBy (\a b -> compare (snd b) (snd a)) $ toList ap)

data ExtState = ExtState {_heapMem :: !(IntMap HeapNode), _inputFifo :: Fifo HeapNode, _outputFifo :: Fifo HeapNode}

heapMem :: Lens' ExtState (IntMap HeapNode)
heapMem = lens _heapMem (\s x -> s {_heapMem = x})
{-# INLINE heapMem #-}
inputFifo :: Lens' ExtState (Fifo HeapNode)
inputFifo = lens _inputFifo (\s x -> s {_inputFifo = x})
{-# INLINE inputFifo #-}
outputFifo :: Lens' ExtState (Fifo HeapNode)
outputFifo = lens _outputFifo (\s x -> s {_outputFifo = x})
{-# INLINE outputFifo #-}

instance Show ExtState where
  show (ExtState m _ _) = "mem: " ++ show (size m)

  
type NodeCount = Word16
type EContCount = Word8

data CallFrame = CallFrame {_ecCount :: !EContCount, _callCont :: !Continuation, _callSavedCond :: !(Checked (CondValue QueueIndex)), _nodeCount :: !NodeCount}

ecCount :: Lens' CallFrame EContCount
ecCount = lens _ecCount (\s x -> s {_ecCount = x})
{-# INLINE ecCount #-}
callCont :: Lens' CallFrame Continuation
callCont = lens _callCont (\s x -> s {_callCont = x})
{-# INLINE callCont #-}
callSavedCond :: Lens' CallFrame (Checked (CondValue QueueIndex))
callSavedCond = lens _callSavedCond (\s x -> s {_callSavedCond = x})
{-# INLINE callSavedCond #-}
nodeCount :: Lens' CallFrame NodeCount
nodeCount = lens _nodeCount (\s x -> s {_nodeCount = x})
{-# INLINE nodeCount #-}

instance Show CallFrame where
  show (CallFrame ec c sc nc) = "CallFrame " ++ show ec ++ " " ++ show c ++ " " ++ show sc ++ " " ++ show nc

type ContData   = (Checked RefValue, Checked RefValue)

data ContMeta
  = NoEvalCont'
  | Update'
  | ApplyN' Word8
  | Select' NodeElem
--  | Setter' NodeElem   -- TODO consider adding setters 
  | ThenFetch' 
  | MaskFetch' Word8      -- same as above but selective with mask on alternative
  | WithCatch' 
  | WithPrim' PrimOp
  deriving (Show)

_ApplyN :: Prism' ContMeta Word8
_ApplyN = prism ApplyN' (\x -> case x of {ApplyN' n -> Right n; _ -> Left x})

data Continuation
  = ReturnNext
  | ReturnTo     StackResult NextFetch   CodeAddr
  | IntoCase     StackResult CaseTable   CodeAddr
  | IntoBigCase  StackResult AltOffset   CodeAddr
  | IntoWhen                 RelCodeAddr CodeAddr
  | ThreadFinish
  deriving Show

data NextInstr
  = NextIP
  | BranchTo  CodeAddr
  | DecideBr  CodeAddr RelCodeAddr
  | NextInstr Instruction
  | EvalLoad  Bool  -- Bool is already evaluated
  | Continue
  | Returning StackPops
  | EvalJump (EvalCont NodeElem QuadElem)  -- shortcut for internal combinator like single instruction, behaves like: Jump EvalFetched (EvalCont using only stacktop) (DropRQ,popSTop)
  | Unwinding StackPops
  | DummyNext   -- only used in stack fixup
  deriving (Show)

data RefSharing = NoSharing | MoreSharing

data LoadReq = PopChannel LoadIndex Channel | LoadRef LoadIndex RefValue | RewriteLoad EvalFun RefValue deriving Show

data CacheReq = CLoadRef LoadIndex HeapRef

data LoadState = LoadState {_loadReq :: Maybe LoadReq, _loadBuffer :: IOArray LoadIndex (Maybe (Maybe RefValue, HeapNode, RefSharing)), _lastLoadIx :: !LoadBase,
   _loadResult :: Maybe (Maybe RefValue, HeapNode), _rewriteLoadResult :: Maybe (RewriteAction, Maybe RefValue, Maybe (HeapNode, RefSharing)),
   _cacheReq :: Maybe CacheReq}

loadReq :: Lens' LoadState (Maybe LoadReq)
loadReq = lens _loadReq (\s x -> s {_loadReq = x})
{-# INLINE loadReq #-}
loadBuffer :: Lens' LoadState (IOArray LoadIndex (Maybe (Maybe RefValue, HeapNode, RefSharing)))
loadBuffer = lens _loadBuffer (\s x -> s {_loadBuffer = x})
{-# INLINE loadBuffer #-}
lastLoadIx :: Lens' LoadState LoadBase
lastLoadIx = lens _lastLoadIx (\s x -> s {_lastLoadIx = x})
{-# INLINE lastLoadIx #-}
loadResult :: Lens' LoadState (Maybe (Maybe RefValue, HeapNode))
loadResult = lens _loadResult (\s x -> s {_loadResult = x})
{-# INLINE loadResult #-}
rewriteLoadResult :: Lens' LoadState (Maybe (RewriteAction, Maybe RefValue, Maybe (HeapNode, RefSharing)))
rewriteLoadResult = lens _rewriteLoadResult (\s x -> s {_rewriteLoadResult = x})
{-# INLINE rewriteLoadResult #-}
cacheReq :: Lens' LoadState (Maybe CacheReq)
cacheReq = lens _cacheReq (\s x -> s {_cacheReq = x})
{-# INLINE cacheReq #-}

data StMapping = StTop StackIndex | StIndex StackIndex | StVoid deriving (Eq, Show)

data RenState = RenState {_loadBase :: !LoadBase, _stackMapping :: Array StackOffset StMapping, _stackForFree :: Fifo StackIndex, _hasSTop :: Bool, -- TODO make bitmasks of stackForPop and stackDropRef
  _refBase :: !QueueBase, _primBase :: !QueueBase, _condBase :: !QueueBase}

loadBase :: Lens' RenState LoadBase
loadBase = lens _loadBase (\s x -> s {_loadBase = x})
{-# INLINE loadBase #-}
stackMapping :: Lens' RenState (Array StackOffset StMapping)
stackMapping = lens _stackMapping (\s x -> s {_stackMapping = x})
{-# INLINE stackMapping #-}
stackForFree :: Lens' RenState (Fifo StackIndex)
stackForFree = lens _stackForFree (\s x -> s {_stackForFree = x})
{-# INLINE stackForFree #-}
hasSTop :: Lens' RenState Bool
hasSTop = lens _hasSTop (\s x -> s {_hasSTop = x})
{-# INLINE hasSTop #-}
refBase :: Lens' RenState QueueBase
refBase = lens _refBase (\s x -> s {_refBase = x})
{-# INLINE refBase #-}
primBase :: Lens' RenState QueueBase
primBase = lens _primBase (\s x -> s {_primBase = x})
{-# INLINE primBase #-}
condBase :: Lens' RenState QueueBase
condBase = lens _condBase (\s x -> s {_condBase = x})
{-# INLINE condBase #-}

newtype StackMask = StackMask Word8
emptyStackMask :: StackMask
emptyStackMask = StackMask 0
stMaskCount :: StackMask -> Int
stMaskCount (StackMask x) = popCount x
stMaskAt :: StackIndex -> Lens' StackMask Bool
stMaskAt (IxS i) = iso (\(StackMask x) -> x) StackMask . bitAt i
{-# INLINE stMaskAt #-}

firstStMaskBit :: StackMask -> Maybe StackIndex
firstStMaskBit (StackMask 0) = Nothing  -- minor optimization
firstStMaskBit (StackMask x) = fmap (IxS . fst) (x ^@? (bits . filtered id))  -- ugly, why doesn lens have elemIndexOf 

data RCState = RCState {_stackForPop :: !StackMask, _stackDropRef :: !StackMask, _rqToPop :: !QueueIndex , _rqLastIx :: !QueueIndex,  -- TODO consider tradeoffs between fifo's and bitmasks for stackForPop and stackDropRef
   _rcUpdates :: ![RCHRef], _dropRefs :: !(Fifo (NodeSize,HeapAddr)), _dropAHRefs :: !(Fifo (NodeSize,AH_Index)), _counters :: IOArray AH_Index RefCounter,
   _dropLoadRes :: Maybe (RefSharing, HeapNode)}

stackForPop :: Lens' RCState StackMask
stackForPop = lens _stackForPop (\s x -> s {_stackForPop = x})
{-# INLINE stackForPop #-}
stackDropRef :: Lens' RCState StackMask
stackDropRef = lens _stackDropRef (\s x -> s {_stackDropRef = x})
{-# INLINE stackDropRef #-}
rqToPop :: Lens' RCState QueueIndex
rqToPop = lens _rqToPop (\s x -> s {_rqToPop = x})
{-# INLINE rqToPop #-}
rqLastIx :: Lens' RCState QueueIndex
rqLastIx = lens _rqLastIx (\s x -> s {_rqLastIx = x})
{-# INLINE rqLastIx #-}
rcUpdates :: Lens' RCState [RCHRef]
rcUpdates = lens _rcUpdates (\s x -> s {_rcUpdates = x})
{-# INLINE rcUpdates #-}
dropRefs :: Lens' RCState (Fifo (NodeSize,HeapAddr))
dropRefs = lens _dropRefs (\s x -> s {_dropRefs = x})
{-# INLINE dropRefs #-}
dropAHRefs :: Lens' RCState (Fifo (NodeSize,AH_Index))
dropAHRefs = lens _dropAHRefs (\s x -> s {_dropAHRefs = x})
{-# INLINE dropAHRefs #-}
counters :: Lens' RCState (IOArray AH_Index RefCounter)
counters = lens _counters (\s x -> s {_counters = x})
{-# INLINE counters #-}
dropLoadRes :: Lens' RCState (Maybe (RefSharing, HeapNode))
dropLoadRes = lens _dropLoadRes (\s x -> s {_dropLoadRes = x})
{-# INLINE dropLoadRes #-}


data CtrlStack = CtrlStack {_topNodeCond :: !(CondValue QueueIndex), _metaSTop :: MetaSTop , _metaSRegs :: IOArray StackIndex (Checked StackMeta), 
   _savedCond :: Checked (CondValue QueueIndex), _callStack :: !(Stack CallFrame),
   _metaContStack :: !(Stack ContMeta), _extraPushCont :: EContCount}

topNodeCond :: Lens' CtrlStack (CondValue QueueIndex)
topNodeCond = lens _topNodeCond (\s x -> s {_topNodeCond = x})
{-# INLINE topNodeCond #-}
metaSTop :: Lens' CtrlStack MetaSTop
metaSTop = lens _metaSTop (\s x -> s {_metaSTop = x})
{-# INLINE metaSTop #-}
metaSRegs :: Lens' CtrlStack (IOArray StackIndex (Checked StackMeta))
metaSRegs = lens _metaSRegs (\s x -> s {_metaSRegs = x})
{-# INLINE metaSRegs #-}
savedCond :: Lens' CtrlStack (Checked (CondValue QueueIndex))
savedCond = lens _savedCond (\s x -> s {_savedCond = x})
{-# INLINE savedCond #-}
callStack :: Lens' CtrlStack (Stack CallFrame)
callStack = lens _callStack (\s x -> s {_callStack = x})
{-# INLINE callStack #-}
metaContStack :: Lens' CtrlStack (Stack ContMeta)
metaContStack = lens _metaContStack (\s x -> s {_metaContStack = x})
{-# INLINE metaContStack #-}
extraPushCont :: Lens' CtrlStack EContCount
extraPushCont = lens _extraPushCont (\s x -> s {_extraPushCont = x})
{-# INLINE extraPushCont #-}

data DataPath = DataPath {_stackTop :: Checked StackNode, _stackRegs :: IOArray StackIndex (Checked StackNode), _stackMem :: !(Stack StoredSN),
  _refQueue :: IOArray QueueIndex RefValue, _contStack :: !(Stack RefValue), _rewriteBuffer :: Maybe (NodeTag, QueueIndex, HeapRef, (RefValue,RefValue))}

stackTop :: Lens' DataPath (Checked StackNode)
stackTop = lens _stackTop (\s x -> s {_stackTop = x})
{-# INLINE stackTop #-}
stackRegs :: Lens' DataPath (IOArray StackIndex (Checked StackNode))
stackRegs = lens _stackRegs (\s x -> s {_stackRegs = x})
{-# INLINE stackRegs #-}
stackMem :: Lens' DataPath (Stack StoredSN)
stackMem = lens _stackMem (\s x -> s {_stackMem = x})
{-# INLINE stackMem #-}
refQueue :: Lens' DataPath (IOArray QueueIndex RefValue)
refQueue = lens _refQueue (\s x -> s {_refQueue = x})
{-# INLINE refQueue #-}
contStack :: Lens' DataPath (Stack RefValue)
contStack = lens _contStack (\s x -> s {_contStack = x})
{-# INLINE contStack #-}
rewriteBuffer :: Lens' DataPath (Maybe (NodeTag, QueueIndex, HeapRef, (RefValue,RefValue)))
rewriteBuffer = lens _rewriteBuffer (\s x -> s {_rewriteBuffer = x})
{-# INLINE rewriteBuffer #-}


data PrimSide = PrimSide {_primSTop :: PrimVals, _primStack :: IOArray StackIndex (Checked PrimVals),
   _primQueue :: IOArray QueueIndex PrimValue, _condQueue :: IOArray QueueIndex (CondValue QueueIndex), _primContStack :: !(Stack PrimValue)}

primSTop :: Lens' PrimSide PrimVals
primSTop = lens _primSTop (\s x -> s {_primSTop = x})
{-# INLINE primSTop #-}
primStack :: Lens' PrimSide (IOArray StackIndex (Checked PrimVals))
primStack = lens _primStack (\s x -> s {_primStack = x})
{-# INLINE primStack #-}
primQueue :: Lens' PrimSide (IOArray QueueIndex PrimValue)
primQueue = lens _primQueue (\s x -> s {_primQueue = x})
{-# INLINE primQueue #-}
condQueue :: Lens' PrimSide (IOArray QueueIndex (CondValue QueueIndex))
condQueue = lens _condQueue (\s x -> s {_condQueue = x})
{-# INLINE condQueue #-}
primContStack :: Lens' PrimSide (Stack PrimValue)
primContStack = lens _primContStack (\s x -> s {_primContStack = x})
{-# INLINE primContStack #-}

data MRU2 = WayA | WayB deriving Eq
data PredEst = WeakP | StrongP
type ICPred = (PredEst, (MRU2,Word32))

data CodeState = CodeState {_codeMem :: CodeMem, _codeCache :: IOArray Word32 (MRU2, Maybe CodeCacheLine, Maybe CodeCacheLine),
  _cLineTags :: !(CacheTag Word32), _cLineBuf :: IOArray QuadElem (Maybe CodeLine), _instrRds :: !Int, _ccHits :: !Int, _ccMiss :: !Int,
  _prevLine  :: ((MRU2,Word32), Word32), _clinePred  :: IOArray Word32 (ICPred, ICPred), _goodPreds  :: !Int,
  _prev2Line :: ((MRU2,Word32), Word32), _cline2Pred :: IOArray Word32 (ICPred, ICPred), _good2Preds :: !Int}

codeMem :: Lens' CodeState CodeMem
codeMem = lens _codeMem (\s x -> s {_codeMem = x})
{-# INLINE codeMem #-}
codeCache :: Lens' CodeState (IOArray Word32 (MRU2, Maybe CodeCacheLine, Maybe CodeCacheLine))
codeCache = lens _codeCache (\s x -> s {_codeCache = x})
{-# INLINE codeCache #-}
cLineTags :: Lens' CodeState (CacheTag Word32)
cLineTags = lens _cLineTags (\s x -> s {_cLineTags = x})
{-# INLINE cLineTags #-}
cLineBuf :: Lens' CodeState (IOArray QuadElem (Maybe CodeLine))
cLineBuf = lens _cLineBuf (\s x -> s {_cLineBuf = x})
{-# INLINE cLineBuf #-}
instrRds :: Lens' CodeState Int
instrRds = lens _instrRds (\s x -> s {_instrRds = x})
{-# INLINE instrRds #-}
ccHits :: Lens' CodeState Int
ccHits = lens _ccHits (\s x -> s {_ccHits = x})
{-# INLINE ccHits #-}
ccMiss :: Lens' CodeState Int
ccMiss = lens _ccMiss (\s x -> s {_ccMiss = x})
{-# INLINE ccMiss #-}
prevLine :: Lens' CodeState ((MRU2,Word32), Word32)
prevLine = lens _prevLine (\s x -> s {_prevLine = x})
{-# INLINE prevLine #-}
clinePred :: Lens' CodeState (IOArray Word32 (ICPred, ICPred))
clinePred = lens _clinePred (\s x -> s {_clinePred = x})
{-# INLINE clinePred #-}
goodPreds :: Lens' CodeState Int
goodPreds = lens _goodPreds (\s x -> s {_goodPreds = x})
{-# INLINE goodPreds #-}
prev2Line :: Lens' CodeState ((MRU2,Word32), Word32)
prev2Line = lens _prev2Line (\s x -> s {_prev2Line = x})
{-# INLINE prev2Line #-}
cline2Pred :: Lens' CodeState (IOArray Word32 (ICPred, ICPred))
cline2Pred = lens _cline2Pred (\s x -> s {_cline2Pred = x})
{-# INLINE cline2Pred #-}
good2Preds :: Lens' CodeState Int
good2Preds = lens _good2Preds (\s x -> s {_good2Preds = x})
{-# INLINE good2Preds #-}

data InstrCtrl = InstrCtrl {_ip :: CodeAddr, _nextI :: NextInstr, _branchCond :: CondValue QueueIndex}

ip :: Lens' InstrCtrl CodeAddr
ip = lens _ip (\s x -> s {_ip = x})
{-# INLINE ip #-}
nextI :: Lens' InstrCtrl NextInstr
nextI = lens _nextI (\s x -> s {_nextI = x})
{-# INLINE nextI #-}
branchCond :: Lens' InstrCtrl (CondValue QueueIndex)
branchCond = lens _branchCond (\s x -> s {_branchCond = x})
{-# INLINE branchCond #-}

data Stats = Stats {_steps :: !Int, _multiSteps :: !Int, _refLoads :: !Int, _knownPTrefLoads :: !Int, _funrefLoads :: !Int}

steps :: Lens' Stats Int
steps = lens _steps (\s x -> s {_steps = x})
{-# INLINE steps #-}
multiSteps :: Lens' Stats Int
multiSteps = lens _multiSteps (\s x -> s {_multiSteps = x})
{-# INLINE multiSteps #-}
refLoads :: Lens' Stats Int
refLoads = lens _refLoads (\s x -> s {_refLoads = x})
{-# INLINE refLoads #-}
knownPTrefLoads :: Lens' Stats Int
knownPTrefLoads = lens _knownPTrefLoads (\s x -> s {_knownPTrefLoads = x})
{-# INLINE knownPTrefLoads #-}
funrefLoads :: Lens' Stats Int
funrefLoads = lens _funrefLoads (\s x -> s {_funrefLoads = x})
{-# INLINE funrefLoads #-}

data ProcState = ProcState {_heap :: !HeapState, _ext :: !ExtState, _loader :: !LoadState, _rcUnit :: !RCState, _renamer :: !RenState,
  _ctrlStack :: !CtrlStack, _dataPath :: !DataPath, _primSide :: !PrimSide, _code :: CodeState, _instrCtrl :: !InstrCtrl, _stats :: !Stats}

heap :: Lens' ProcState HeapState
heap = lens _heap (\s x -> s {_heap = x})
{-# INLINE heap #-}
ext :: Lens' ProcState ExtState
ext = lens _ext (\s x -> s {_ext = x})
{-# INLINE ext #-}
loader :: Lens' ProcState LoadState
loader = lens _loader (\s x -> s {_loader = x})
{-# INLINE loader #-}
rcUnit :: Lens' ProcState RCState
rcUnit = lens _rcUnit (\s x -> s {_rcUnit = x})
{-# INLINE rcUnit #-}
renamer :: Lens' ProcState RenState
renamer = lens _renamer (\s x -> s {_renamer = x})
{-# INLINE renamer #-}
ctrlStack :: Lens' ProcState CtrlStack
ctrlStack = lens _ctrlStack (\s x -> s {_ctrlStack = x})
{-# INLINE ctrlStack #-}
dataPath :: Lens' ProcState DataPath
dataPath = lens _dataPath (\s x -> s {_dataPath = x})
{-# INLINE dataPath #-}
primSide :: Lens' ProcState PrimSide
primSide = lens _primSide (\s x -> s {_primSide = x})
{-# INLINE primSide #-}
code :: Lens' ProcState CodeState
code = lens _code (\s x -> s {_code = x})
{-# INLINE code #-}
instrCtrl :: Lens' ProcState InstrCtrl
instrCtrl = lens _instrCtrl (\s x -> s {_instrCtrl = x})
{-# INLINE instrCtrl #-}
stats :: Lens' ProcState Stats
stats = lens _stats (\s x -> s {_stats = x})
{-# INLINE stats #-}

showStackResult :: ProcState -> IO (String, ProcState)
showStackResult s = do
  let (_, _, Just t, ns) = s^.ctrlStack.metaSTop
  let (OK (StNode r xs)) = s^.dataPath.stackTop
  let (Q yh yi yj yk) = s^.primSide.primSTop
  let bodyToList (FB (T a b c) (Q d e f g)) = map (\x -> case x of {Bad -> error ("Bad value in showTop "); (OK y) -> y}) $ take (fromEnum $ nodeArity t) [a,b,c,d,e,f,g]
  let body = case ns of {PrimS -> "[]"; _ -> show (bodyToList xs)}
  return (show r ++ " @ " ++ show t ++ " :  " ++ body ++ "  :-  " ++ unCheck "__" show yh ++ " " ++ unCheck "__" show yi ++ " " ++ unCheck "__" show yj ++ " " ++ unCheck "__" show yk ++ " ", s)

showProcState :: ProcState -> IO String
showProcState (ProcState h e _ _ (RenState _ rm _ _ (QB rb) (QB pb) _) (CtrlStack _ mmx@(_,_,mt,_) _ _ (Stack rs) (Stack cms) ec) (DataPath mx sr (Stack _) rq (Stack cs) _) (PrimSide mp psr pq _ _) _ (InstrCtrl i n _) (Stats s es rls kptls frs)) = do
  rqs <- getElems rq
  pqs <- getElems pq
  let sis = catMaybes $ map (\case {StIndex i -> Just i; _ -> Nothing}) $ (if isJust mt then drop 1 else id) $ take 2 (IArray.elems rm)
  xs <- mapM (readArray sr) sis
  ys <- mapM (readArray psr) sis
  return (
    "step: " ++ show s ++ "+" ++ show es ++ " " ++ show h ++ " " ++ show e ++ " ip: " ++ show i ++ " next: " ++ show n ++
    {- "\nnc: " ++ show nc ++ -} "  ec: " ++ show ec ++
    "\nrs: " ++ show (length rs) ++ "  " ++ show (take 2 rs) ++ 
    "\npq: " ++ show (take 5 $ drop pb (pqs ++ pqs)) ++ "   rq: " ++ show (take 5 $ drop rb (rqs++rqs)) ++
    "\ncms: " ++ show (take 2 cms) ++ "   cs: " ++ show (take 2 cs) ++
    "\n" ++ show mx ++ " " ++ show mp ++ " " ++ show mmx ++ "\n" ++ concatMap ((++ "\n") . show) (zip xs ys) ++ "...   ")
   
pop :: Stack a -> Stack a
pop (Stack []    ) = error "pop empty stack"
pop (Stack (_:xs)) = Stack xs

push :: a -> Stack a -> Stack a
push x (Stack ys) = Stack (x:ys)

top :: Lens' (Stack a) a
top f (Stack ~(x:xs)) = fmap (\y -> Stack (y:xs)) (f x)
{-# INLINE top #-}

emptyBody :: FB (Maybe a)
emptyBody = FB (T Nothing Nothing Nothing) (Q Nothing Nothing Nothing Nothing)

emptyNBody :: FixedBody
emptyNBody = FB (T Bad Bad Bad) (Q Bad Bad Bad Bad)

emptyRBody :: ReadBody
emptyRBody = FB (T Bad Bad Bad) (Q Bad Bad Bad Bad)

unaryBody :: BodyArg -> FixedBody
unaryBody x = FB (T (OK x) Bad Bad) (Q Bad Bad Bad Bad) 

bodyIndices :: FB NodeElem
bodyIndices = FB (T A B C) (Q D E F G)

primAt :: QuadElem -> Lens' (Quad (Checked a)) a
primAt H f (Q ~(OK a) b c d) = fmap (\r -> Q (OK r) b c d) (f a)
primAt I f (Q a ~(OK b) c d) = fmap (\r -> Q a (OK r) c d) (f b)
primAt J f (Q a b ~(OK c) d) = fmap (\r -> Q a b (OK r) d) (f c)
primAt K f (Q a b c ~(OK d)) = fmap (\r -> Q a b c (OK r)) (f d)
{-# INLINE primAt #-}

elemAt :: NodeElem -> Lens' (Body a) a
elemAt A m (FB (T ~(OK a) b c) (Q d e f g      )) = fmap (\r -> FB (T (OK r) b c) (Q d e f g     )) (m a)
elemAt B m (FB (T a ~(OK b) c) (Q d e f g      )) = fmap (\r -> FB (T a (OK r) c) (Q d e f g     )) (m b)
elemAt C m (FB (T a b ~(OK c)) (Q d e f g      )) = fmap (\r -> FB (T a b (OK r)) (Q d e f g     )) (m c)
elemAt D m (FB (T a b c      ) (Q ~(OK d) e f g)) = fmap (\r -> FB (T a b c     ) (Q (OK r) e f g)) (m d)
elemAt E m (FB (T a b c      ) (Q d ~(OK e) f g)) = fmap (\r -> FB (T a b c     ) (Q d (OK r) f g)) (m e)
elemAt F m (FB (T a b c      ) (Q d e ~(OK f) g)) = fmap (\r -> FB (T a b c     ) (Q d e (OK r) g)) (m f)
elemAt G m (FB (T a b c      ) (Q d e f ~(OK g))) = fmap (\r -> FB (T a b c     ) (Q d e f (OK r))) (m g)
{-# INLINE elemAt #-}

kindMaskBody :: NodeTag -> FB (Maybe ValueKind)
kindMaskBody t = zipBodyWith kme bodyIndices (kindMask t) where
  kme i x = if fromEnum (nodeArity t) > fromEnum i then Just x else Nothing

zipTripleWith :: (a -> b -> c) -> Triple a -> Triple b -> Triple c
zipTripleWith f (T a b c) (T x y z) = T (f a x) (f b y) (f c z)

zipQuadWith :: (a -> b -> c) -> Quad a -> Quad b -> Quad c
zipQuadWith f (Q a b c d) (Q p q r s) = Q (f a p) (f b q) (f c r) (f d s)

zipBodyWith :: (a -> b -> c) -> FB a -> FB b -> FB c
zipBodyWith f (FB a b) (FB x y) = FB (zipTripleWith f a x) (zipQuadWith f b y)

zip3TripleWith :: (a -> b -> c -> d) -> Triple a -> Triple b -> Triple c -> Triple d
zip3TripleWith f (T a b c) (T p q r) (T x y z) = T (f a p x) (f b q y) (f c r z)

zip3QuadWith :: (a -> b -> c-> d) -> Quad a -> Quad b -> Quad c -> Quad d
zip3QuadWith f (Q a b c d) (Q p q r s) (Q w x y z)  = Q (f a p w) (f b q x) (f c r y) (f d s z)

zip3BodyWith :: (a -> b -> c -> d) -> FB a -> FB b -> FB c -> FB d
zip3BodyWith f (FB a b) (FB p q) (FB x y)  = FB (zip3TripleWith f a p x) (zip3QuadWith f b q y)

mapBodyWithKind :: b -> (ValueKind -> a -> b) -> NodeTag -> Body a -> FB b
mapBodyWithKind d f t = zipBodyWith (maybe (const d) (\k -> \case {OK x -> f k x; Bad -> error "Bad value in nodeBody" })) (kindMaskBody t)

boxNodeTag :: ConAlt -> NodeTag
boxNodeTag = NodeTag Dynamic 1 singlePrimK . Box

rawNodeTag :: FB (Maybe (Either a b)) -> (NodeTag, Arity) -- Tag and Prim arity
rawNodeTag xys = (NodeTag Dynamic ra vs Unboxed, pa) where
  ra = toEnum $ getSum $ foldMap (maybe 0 (either (const 1) (const 0))) xys
  pa = toEnum $ getSum $ foldMap (maybe 0 (either (const 0) (const 1))) xys
  vs = fmap (maybe PrimK (either (const RefK) (const PrimK))) xys

countJusts :: (Foldable f, Num x) => f (Maybe a) -> x
countJusts = getSum . foldMap (maybe 0 (const 1))

singleRefNodeTag :: Tag -> NodeTag
singleRefNodeTag = NodeTag Dynamic 1 singleRefK

withRef :: Setter (NodeArg a p) (NodeArg b p) a b
withRef = sets (\f -> \case {RVal x -> RVal $ f x; PVal y -> PVal y})
{-# INLINE withRef #-}

asRef :: Show p => Lens' (NodeArg r p) r
asRef = lens (\case {RVal r -> r; PVal p -> error ("expected Ref value " ++ show p)}) (\case {RVal _ -> RVal; y@(PVal _) -> const y})
{-# INLINE asRef #-}

asPrim :: Lens' (NodeArg r p) p
asPrim = lens (\case {PVal p -> p; RVal _ -> error "expected Prim value"}) (\case {PVal _ -> PVal; y@(RVal _) -> const y})
{-# INLINE asPrim #-}

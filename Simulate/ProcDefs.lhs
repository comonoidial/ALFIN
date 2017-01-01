This module contains the basic data structures and instruction set for lazy functional processor.

> {-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, DeriveFunctor, DeriveTraversable, DeriveFoldable #-}
> module Simulate.ProcDefs where

> import Control.Applicative
> import Data.Foldable (Foldable, foldMap)
> import Data.Traversable (Traversable)
> import Data.Int (Int64, Int32, Int8)
> import Data.Word (Word32, Word8)
> import Data.Monoid
> import Data.Maybe
> import Data.Either
> import Data.Ix

Things on the heap and stack are grouped into nodes. Every function or data constructor with their arguments is a node.
A node consist of a tag containing it's metadata and a list of values that are either heap references or primitive words.
To ease garbage collection references and primitive are explicitly separated.

> data Node = Node !NodeTag NodeBody

> type NodeBody = [NodeArg RefValue PrimValue]

A tag determines how a node can be used or how it can evaluated.
Every data constructor has it's own tag with an unique identifier, a box tag is a specialized data constructor with only a single primitive value.
Tags for unevaluated functions contain a pointer to code to evaluate them, a function with not enough arguments applied also contain the number of missing arguments.
The stack (not the heap) can have nodes that are just a group of values, denoted by the unboxed tag.
Other tags are for certain builtin functions such as (unknown function) application and tuple selection/projection and probably others.
For garbage collection purposes tags of static (top level constant) nodes need to marked explicitly.

> data NodeTag = NodeTag {nodeKind :: !NodeKind, nodeArity :: !Arity, kindMask :: !KindMask, plainTag :: !Tag}  -- kindMask contains info for all args even if they are not applied yet
> type NodeFormat = (Arity, KindMask)

> data NodeKind = Static | Dynamic deriving Eq   -- static nodes are for CAFs

> newtype Arity = Arity Word8 deriving (Eq, Ord, Num, Enum)  -- 3 bits node arity type

> type KindMask = FB ValueKind

> data ValueKind = RefK | PrimK deriving (Show, Eq)

> emptyKinds, singlePrimK, singleRefK :: KindMask
> emptyKinds  = FB (T PrimK PrimK PrimK) (pure PrimK)
> singlePrimK = FB (T PrimK PrimK PrimK) (pure PrimK)
> singleRefK  = FB (T RefK PrimK PrimK) (pure PrimK)

> data NodeArg r p = RVal r | PVal p  -- Either isomorphism that is only implicitly present in hardware because the actual information is in the kind mask
> instance (Show r, Show p) => Show (NodeArg r p) where show = showNodeArg
> showNodeArg :: (Show r, Show p) => NodeArg r p -> String
> showNodeArg (RVal x) = show x
> showNodeArg (PVal p) = "#" ++ show p

> data NodeSize = SingleNode | DoubleNode deriving (Eq, Ord)
> data UpdateFlag = WithUpd | SkipUpd deriving (Eq, Ord, Show)

> data Tag
>   = Con  !ConAlt
>   | DCon !ConAlt  !Arity                 -- Arity is here the number of missing arguments
>   | HCon !ConAlt  !NodeElem              -- partial constructor with a single hole, for avoiding trivial lambdas and maybe argument reduction tricks
>   | Box  !ConAlt
>   | Fun  !FunAddr !NextFetch !UpdateFlag -- TODO think about UpdateFlag in Pap and HFun
>   | Pap  !FunAddr !NextFetch !Arity      -- Arity is here the number of missing arguments
>   | HFun !FunAddr !NextFetch !NodeElem   -- like HCon but for functions
>   | Unboxed                              -- stack only unboxed tuple      -- TODO think about the correct meaning of nodeArity and valueKinds for Unboxed nodes
>   | FE   !EvalFun !UpdateFlag            -- TODO consider when to enable updating on EvalFuns
>   | PE   !EvalFun !Arity                 -- Arity is here the number of missing arguments
>   | Ind
>   | Blackhole
>   | Excep                                -- stack top only exception value
>   deriving (Eq, Ord)

> data EvalFun                       -- TODO think about const/flip/flip const
>   = E_id
>   | E_ap1
>   | E_ap2
>   | E_sel !NodeElem
>   deriving (Eq, Ord, Show)

> type FunAddr = (String, CodeAddr)
> type FunHash = (String, Int8)
> type ConAlt  = (ConName, ConIndex)  -- TODO switch to a global index for constructors
> type ConIndex = Word32
> type ConName = String

The word size of the processor will be 64 bit and so are the primitive values.

> type PrimValue = Int64

A (reference) value is more complex because it may contain some information about the reference, the first 16 bit are reserved for the metadata.
The normal reference is a pointer to some heap node and a pointer tag which is a condensed form of the tag of the node it's pointing to.
If a reference is to an Box node with a primitive that use a limited number of bits it can be stored in the value directly.
Also directly stored are references to nodes without argument values such as enumeration constructors and no argument applied functions.
The reason of sacrificing some bits of the heap pointer is to reduce the number memory accesses in and to allow parts of the processor continue without having to wait for the node to be loaded from heap memory.

> data RefValue = Ref !PtrTag !HeapRef | CVRef !CompactValue deriving Show

> data CompactValue
>   = PrimBox   !ConAlt  !Int64     -- should be an Int48
> --  | DoubleBox !Double            -- TODO think about adding doubles with small exponents
>   | EnumTag   !ConAlt
>   | EmptyDCon !ConAlt             !Arity !KindMask   -- Arity is here the number of missing arguments
>   | EmptyPap  !FunAddr !NextFetch !Arity !KindMask   -- idem ^^
>   | EmptyPEF  !EvalFun            !Arity !KindMask   -- idem ^^
>   | VoidRef                                          -- dummy/invalid reference value
>   | FetchedRef                                       -- token reference value marking a prefetched reference
>   deriving Eq

> data PtrTag
>   = TC !ConAlt
>   | TD !ConAlt  !Arity        -- Arity is here the number of missing arguments
>   | TF !FunHash
>   | TP !FunHash !Arity        -- idem ^^
>   | TE !EvalFun
>   | TX
>   deriving Eq

> data StackResult = OnlyTag | OnlyNode | NodeWSC | OnlySC deriving (Eq, Show)          -- OnlyNode includes unboxed tuples and primitives
> data PrimResult  = PrimRes | PrimWSC                     deriving (Eq, Show)

> data CaseTable = CaseTab2 AltInfo AltInfo | CaseTab4 (Quad (Maybe AltInfo)) | CaseTab8 (Quad AltInfo) (Quad (Maybe AltInfo))
> type AltInfo   = Either (NextFetch, RelCodeAddr) StackPops
> type AltOffset = (Int, Int)  -- jump offset altindex shift factor, add number of alts mask -- TODO both values could be Word4

> data Instruction
>   = Nop                                                   PopMask 
>   | Call       StackResult Callable ExtraCont NextFetch   PopMask
>   | Case       StackResult Callable ExtraCont CaseTable   PopMask
>   | BigCase    StackResult Callable ExtraCont AltOffset   PopMask
>   | When                   Callable ExtraCont RelCodeAddr PopMask
>   | Jump                   Callable ExtraCont             PopMask
>   | Return     NodeTag     NodeRead                       PopMask
>   | ReturnTag  NodeTag                                    PopMask     -- just a specialized version of above
>   | ReturnTop                                             PopMask     -- even more specialized
>   | ReturnRaw              SplitRead                      PopMask     -- returning an unboxed tuple
>   | ReturnConst ConAlt     Int64                          PopMask     -- should be an Int48
>   | ReturnPrim  ConAlt     PrimRead                       PopMask
>   | ReturnBool  ConAlt     CondRead                       PopMask
> --  | ReturnPrimOp ConAlt    PrimInstr                      PopMask   -- TODO maybe add this combination 
> --  | ReturnCmpOp  ConAlt    PrimInstr                      PopMask   -- TODO maybe add this combination 

Various ways of storing things and/or putting things in the reference queue.

>   | Store        NodeTag   NodeRead                       PopMask
>   | StoreCVal CompactValue                                PopMask
>   | StoreFE     NodeFormat UpdateFlag RefRead ExtraCont   PopMask     -- specialized store because of load required for store rewriting
>   | PushCAFRef             (PtrTag, HeapRef)              PopMask
>   | StoreSelect  CondRead  RefRead  RefRead               PopMask
>   | StoreBox     ConAlt    PrimRead                       PopMask
>   | StoreBool    ConAlt    CondRead                       PopMask
> --  | StoreBoxOp   ConAlt    PrimInstr                      PopMask   -- TODO maybe add this combination 

Pushing either one of the stacks.

>   | Push                   SplitRead                      PopMask
>   | PushCont                        ExtraCont             PopMask
>   | ClearRefs              SplitRead                      PopMask      -- only ref are read -- to avoid certain space leaks without copying all of the live stack

Other instructions where Send is a write to the output fifo.

>   | PrimInstr    PrimInstr  PrimInstr                     PopMask
>   | IfElse       PrimInstr  CondRead RelCodeAddr          PopMask
> --  | MultiBranch [CondRead] [RelCodeAddr]                  PopMask
> --  | IntSwitch   PrimRead   [RelCodeAddr]                  PopMask
> --  | BigSwitch   PrimRead   AltOffset
>   | GoTo         CodeAddr                                 PopMask 
>   | Send Channel NodeTag  NodeRead                        PopMask
>   | Throw        RefRead                                  PopMask
>   deriving Show

The various primitive operations.

> data PrimInstr
>   = PrimNop
>   | PrimOp      PrimOp    PrimRead PrimRead CondRead
>   | CmpOp (CmpOp,LogicOp) PrimRead PrimRead CondRead
>   | PrimConst   Int64                                      -- should be some smaller Int
>   deriving Show

Fetch is like Eval but for known evaluated references.
Receive reads a node from the input fifo.

> data Callable
>   = Eval RefRead
>   | Fetch RefRead                    -- load already evaluated value      -- TODO what is the right behaviour on this with indirections? for now not allowed
>   | EvalFetched
>   | PushFetched                      -- push prefetched evaluated value   -- idem ^^
>   | EvalCAF (PtrTag, HeapRef)        -- FetchCAF exists implicitly by looking at the pointer tag
>   | Run FunAddr NodeRead
>   | Fix FunAddr NodeRead             -- note no ExtraCont are allowed in combination with Fix
>   | Proc FunAddr SplitRead
>   | Receive Channel
>   deriving Show

> type NextFetch = Maybe NodeElem   -- FIXME should become either  Maybe (RefUse, NodeElem) OR change codegen to make it always an implicit TakeRef

> type ExtraCont = EvalCont RefRead PrimRead

> data EvalCont r p
>   = NoEvalCont
>   | Update r            -- for internal use only, can not be part of an instruction
>   | Apply1 r
>   | Apply2 r r
>   | Select NodeElem
> --  | Setter NodeElem r  -- TODO consider adding setters 
>   | ThenFetch r
>   | MaskFetch Word8 r     -- same as above but selective with mask on alternative
>   | WithCatch r
>   | WithPrim PrimOp p
>   deriving (Show)
 
> data Channel = Channel deriving Show  -- maybe support multiple channels in the future
> defaultChannel = Channel

> data PrimOp = OpAdd | OpSub | OpNeg | OpMul | OpMod | OpSel deriving (Show, Eq)

> data CmpOp = CmpLT | CmpLE | CmpGT | CmpGE | CmpEQ | CmpNE deriving Show

> data LogicOp = LogAnd | LogOr | LogXor deriving Show

> type NodeRead = FB (Maybe (Either RefRead WordRead))
> type SplitRead = FB (Maybe (Either RefRead PrimRead)) -- with the constraint of first all refs then the prims

> data RefRead
>   =  R  StackOffset NodeElem   -- taking  a ref from the node stack
>   | CR  StackOffset NodeElem   -- copying a ref from the node stack
>   |  NR StackOffset            -- taking the node ref
>   | CNR StackOffset            -- copying the node ref
>   |  RQ QueueOffset            -- taking  a ref from the reference queue
>   | CRQ QueueOffset            -- copying a ref from the reference queue
>   | SCC ConAlt                 -- small constant constructor
>   | RVoid                      -- reference to Void data type or dummy/invalid reference
>   deriving (Show)

Reading primitive values either from the node stack or the primitive side of the core.

> data WordRead = W StackOffset NodeElem | PA PrimRead
>   deriving (Show)

Reading a primitive value on the primitive side of the core.

> data PrimRead = V StackOffset QuadElem | PQ QueueOffset | Im Int | STTI  -- stack top tag index
>   deriving (Show)

> data CondRead = CQ Bool QueueOffset | CTrue | CFalse | CNext Bool | CSTI Bool | CSaved Bool  -- Bool if condition is to be inverted, CNext may only be used as second argument of logic operators
>   deriving (Show)

> data NodeElem = A | B | C | D | E | F | G
>   deriving (Show, Eq, Ord, Enum)

> data QuadElem = H | I | J | K
>   deriving (Show, Eq, Ord, Enum, Ix)

The PopMask includes a bit to empty the reference queue to avoid spaceleaks.

> type PopMask = (PopRQ, StackPops)
> type StackPops = Quad PopNode

> popNone, popSTop, popNext :: StackPops
> popNone = Q Keep Keep Keep Keep
> popSTop = Q Pop  Keep Keep Keep
> popNext = Q Keep Pop  Keep Keep

> data PopRQ = DropRQ | KeepRQ deriving (Show, Eq)

> data PopNode = Pop | Keep deriving (Show, Eq)

> data Uniqueness = Unique | Shared | GlobalRef deriving (Show, Eq)

> type HeapRef   = (Uniqueness, NodeSize, HeapAddr)
> type HeapAddr  = Int
> data RefUse    = TakeRef | CopyRef deriving Eq

> instance Monoid RefUse where  -- has any TakeRef
>   mempty = CopyRef
>   mappend TakeRef _ = TakeRef
>   mappend CopyRef x = x

> type StackOffset = Int
> type QueueOffset = Int
> newtype CodeAddr = CodeAddr {fromCodeAddr :: Word32} deriving (Eq, Ord)
> newtype RelCodeAddr = RelCodeAddr Int deriving Eq

> data Quad   a = Q !a !a !a !a            deriving (Show, Eq, Functor, Foldable, Traversable)
> data Triple a = T !a !a !a               deriving (Show, Eq, Functor, Foldable, Traversable)
> data FB a     = FB !(Triple a) !(Quad a) deriving (Show, Eq, Functor, Foldable, Traversable)

> instance Applicative Quad where
>   pure x = Q x x x x
>   (Q p q r s) <*> (Q a b c d) = Q (p a) (q b) (r c) (s d)

> execPrimOp :: PrimOp -> Bool -> Int64 -> Int64 -> Int64
> execPrimOp OpAdd _ x y = x + y
> execPrimOp OpSub _ x y = x - y
> execPrimOp OpNeg _ x _ = negate x
> execPrimOp OpMul _ x y = x * y
> execPrimOp OpMod _ x y = x `mod` y
> execPrimOp OpSel c x y = if c then x else y

> execCmpOp :: CmpOp -> Int64 -> Int64 -> Bool
> execCmpOp CmpLT x y = x <  y
> execCmpOp CmpLE x y = x <= y
> execCmpOp CmpGT x y = x >  y
> execCmpOp CmpGE x y = x >= y
> execCmpOp CmpEQ x y = x == y
> execCmpOp CmpNE x y = x /= y

> type CondValue a = (Maybe a, Bool)  -- Bool is the value itself or the inversion of not yet available value

> asBool :: String -> CondValue a -> Bool
> asBool _ (Nothing, c) = c
> asBool e (Just _ , _) = error e

> execLogicOp :: LogicOp -> Bool -> CondValue a -> CondValue a
> execLogicOp LogAnd False _ = (Nothing, False)
> execLogicOp LogAnd True  y = y
> execLogicOp LogOr  False y = y
> execLogicOp LogOr  True  _ = (Nothing, True)
> execLogicOg LogXor x     y = fmap (xOr x) y where xOr = (/=)

> nodeTag :: Node -> NodeTag
> nodeTag (Node t _) = t

> nodeSizeT :: NodeTag -> NodeSize
> nodeSizeT t = if nodeArity t <= 3 then SingleNode else DoubleNode

> bodyArity :: FB (Maybe a) -> Arity
> bodyArity = getSum . foldMap (maybe 0 $ const 1)

> nodeSize_ :: FB (Maybe a) -> NodeSize
> nodeSize_ xs = if (bodyArity xs <= 3) then SingleNode else DoubleNode

> bodyKinds :: FB (Maybe (Either r p)) -> KindMask
> bodyKinds = fmap (maybe PrimK $ either (const RefK) (const PrimK))

> node2PtrTag :: NodeTag -> PtrTag
> node2PtrTag t = tag2PtrTag (plainTag t)

> tag2PtrTag :: Tag -> PtrTag
> tag2PtrTag (Con  c        ) = TC c
> tag2PtrTag (Box  c        ) = TC c
> tag2PtrTag (DCon c   n    ) = TD c           n
> tag2PtrTag (HCon c _      ) = TD c           1
> tag2PtrTag (Fun  f _     _) = TF (hashFun f)
> tag2PtrTag (Pap  f _ n    ) = TP (hashFun f) n
> tag2PtrTag (HFun f _ _    ) = TP (hashFun f) 1
> tag2PtrTag (FE   ef _     ) = TE ef
> tag2PtrTag _                = TX

> getAltIndex :: Tag -> Word32
> getAltIndex (Con alt   ) = snd alt
> getAltIndex (Box alt   ) = snd alt
> getAltIndex (DCon alt _) = snd alt   -- allow getting altIndex of a partial applied constructor to avoid depency on application logic
> getAltIndex (HCon alt _) = snd alt   -- idem
> getAltIndex t            = error ("case on a non constructor " ++ show t)

> tag2Index :: Tag -> Word32
> tag2Index (Con  c        ) = snd c
> tag2Index (Box  c        ) = snd c
> tag2Index (DCon c   n    ) = snd c
> tag2Index (HCon c _      ) = snd c
> tag2Index (Fun  f _     _) = fromCodeAddr $ snd f
> tag2Index (Pap  f _ n    ) = fromCodeAddr $ snd f
> tag2Index (HFun f _ _    ) = fromCodeAddr $ snd f
> tag2Index _                = 0

> hashFun :: FunAddr -> FunHash
> hashFun (f, CodeAddr x) = (f, fromIntegral x)

> isUpdFTag :: Tag -> Bool
> isUpdFTag (Fun _ _ WithUpd) = True
> isUpdFTag (FE _    WithUpd) = True
> isUpdFTag _                 = False

> isValueTag :: Tag -> Bool
> isValueTag = isValuePtrTag . tag2PtrTag

> isValuePtrTag :: PtrTag -> Bool
> isValuePtrTag (TC _  ) = True
> isValuePtrTag (TD _ _) = True
> isValuePtrTag (TP _ _) = True
> isValuePtrTag _        = False

> primBoxConAlt :: Tag -> Maybe ConAlt
> primBoxConAlt (Box c  ) = Just c
> primBoxConAlt _         = Nothing

> evalFunFromApply :: EvalCont r p -> EvalFun
> evalFunFromApply (Apply1 _  ) = E_ap1
> evalFunFromApply (Apply2 _ _) = E_ap2
> evalFunFromApply (Select i  ) = E_sel i

> caseAltTarget :: CaseTable -> Tag -> AltInfo
> caseAltTarget xs t = ixwE (getAltIndex t) xs where
>   ixwE 0 (CaseTab2 a _                 ) = a
>   ixwE 1 (CaseTab2 _ b                 ) = b
>   ixwE 0 (CaseTab4 (Q (Just a) _ _ _)  ) = a
>   ixwE 1 (CaseTab4 (Q _ (Just b) _ _)  ) = b
>   ixwE 2 (CaseTab4 (Q _ _ (Just c) _)  ) = c
>   ixwE 3 (CaseTab4 (Q _ _ _ (Just d))  ) = d
>   ixwE 0 (CaseTab8 (Q a _ _ _)       _ ) = a
>   ixwE 1 (CaseTab8 (Q _ b _ _)       _ ) = b
>   ixwE 2 (CaseTab8 (Q _ _ c _)       _ ) = c
>   ixwE 3 (CaseTab8 (Q _ _ _ d)       _ ) = d
>   ixwE 4 (CaseTab8 _ (Q (Just e) _ _ _)) = e
>   ixwE 5 (CaseTab8 _ (Q _ (Just f) _ _)) = f
>   ixwE 6 (CaseTab8 _ (Q _ _ (Just g) _)) = g
>   ixwE 7 (CaseTab8 _ (Q _ _ _ (Just h))) = h
>   ixwE _ _                               = error "index too large caseAlt"

> instance Show CodeAddr where
>   show (CodeAddr x) = show x

> instance Show RelCodeAddr where
>   show (RelCodeAddr x) = "_+" ++ show x

> instance Show Arity where
>   show (Arity x) = show x

> instance Show Node where
>   show (Node t []) = show t ++ " []"
>   show (Node t xs) = show t ++ " [" ++ init (concatMap ((++", ") . showNodeArg) xs) ++ "]"

> instance Show CompactValue where
>   show (VoidRef         ) = "!Void!"
>   show (FetchedRef      ) = "!Fetched!"
>   show (EnumTag t       ) = "C_" ++ fst t
>   show (EmptyDCon c _  _) = "D_" ++ fst c
>   show (EmptyPap f _ _ _) = "P_" ++ fst f
>   show (PrimBox t x     ) = (fst t) ++ " #" ++ show x
>   show (EmptyPEF (E_sel n)  _ _) = "P_Sel_" ++ show n
>   show (EmptyPEF (E_id)  _ _) = "P_Id"

> showShortUniqueness :: Uniqueness -> String
> showShortUniqueness Unique     = "U"
> showShortUniqueness Shared     = "S"
> showShortUniqueness GlobalRef  = "G"

> instance Show NodeTag where
>   show (NodeTag Static _ _ t) = "G" ++ show t
>   show (NodeTag _      _ _ t) = show t

> instance Show NodeSize where
>   show (SingleNode) = "S"
>   show (DoubleNode) = "D"

> instance Show Tag where
>   show (Con c)           = "C_" ++ fst c
>   show (DCon c n)        = "D_" ++ fst c ++ "--" ++ show n
>   show (HCon c e)        = "D_" ++ fst c ++ "--" ++ show e
>   show (Box c)           = "B_" ++ fst c
>   show (Fun f _ WithUpd) = "F_" ++ fst f
>   show (Fun f _ SkipUpd) = "G_" ++ fst f
>   show (Pap f _ n)       = "P_" ++ fst f ++ "--" ++ show n
>   show (HFun f _ e)      = "P_" ++ fst f ++ "--" ++ show e
>   show (FE (E_ap1)   _)  = "Ap_1"
>   show (FE (E_ap2)   _)  = "Ap_2"
>   show (FE (E_sel n) _)  = "Sel_" ++ show n
>   show (FE (E_id)    _)  = "Id"
>   show (PE (E_sel n) _)  = "P_Sel_" ++ show n
>   show (PE (E_id)    _)  = "P_Id"
>   show (Unboxed)         = "(#...#)"
>   show (Ind)             = "Indirection"
>   show (Blackhole  )     = "BlAcKhOlE"

> instance Show PtrTag where
>   show (TC c)         = fst c
>   show (TF f)         = fst f
>   show (TD c n)       = fst c ++ "--" ++ show n
>   show (TP f n)       = fst f ++ "--" ++ show n
>   show (TE (E_sel _)) = "Sel"
>   show (TE (E_ap1  )) = "Ap1"
>   show (TE (E_ap2  )) = "Ap2"
>   show (TX)           = "??"

> instance Show CaseTable where
>   show (CaseTab2 a b                    ) = show [a,b]
>   show (CaseTab4 (Q a b c d)            ) = show $ catMaybes [a,b,c,d]
>   show (CaseTab8 (Q a b c d) (Q e f g h)) = show ([a,b,c,d] ++ catMaybes [e,f,g,h])

> listToBody :: [a] -> FB (Maybe a)
> listToBody [             ] = FB (T Nothing  Nothing  Nothing ) (Q Nothing  Nothing  Nothing  Nothing )
> listToBody [a            ] = FB (T (Just a) Nothing  Nothing ) (Q Nothing  Nothing  Nothing  Nothing )
> listToBody [a,b          ] = FB (T (Just a) (Just b) Nothing ) (Q Nothing  Nothing  Nothing  Nothing )
> listToBody [a,b,c        ] = FB (T (Just a) (Just b) (Just c)) (Q Nothing  Nothing  Nothing  Nothing )
> listToBody [a,b,c,d      ] = FB (T (Just a) (Just b) (Just c)) (Q (Just d) Nothing  Nothing  Nothing )
> listToBody [a,b,c,d,e    ] = FB (T (Just a) (Just b) (Just c)) (Q (Just d) (Just e) Nothing  Nothing )
> listToBody [a,b,c,d,e,f  ] = FB (T (Just a) (Just b) (Just c)) (Q (Just d) (Just e) (Just f) Nothing )
> listToBody [a,b,c,d,e,f,g] = FB (T (Just a) (Just b) (Just c)) (Q (Just d) (Just e) (Just f) (Just g))

> nodeSize__ :: [a] -> NodeSize
> nodeSize__ xs = if (length xs <= 3) then SingleNode else DoubleNode

> bodyKinds_ :: [Either r p] -> KindMask
> bodyKinds_ = bodyKinds . listToBody

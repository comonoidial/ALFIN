{-# LANGUAGE TupleSections, GADTs, MultiParamTypeClasses, FlexibleInstances, Rank2Types #-}
module Simulate.PipeLineMonad where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Class
import Data.Array.IO
import System.IO (stdout, hFlush)
import Control.Lens hiding ((%=), (.=), (+=))
import Debug.Trace

type PLST s a = MonadBuilder (PipeAction s) a

infix 4 %=, .=, +=
(%=) ::  ASetter' s a -> (a -> a) -> PLST s ()
l %= f = command (Update (over l f))  -- specialized version of lens combinator for performance
{-# INLINE (%=) #-}

(.=) ::  ASetter' s a -> a -> PLST s ()
l .= x = command (Update (set' l x))  -- specialized version of lens combinator for performance
{-# INLINE (.=) #-}

(+=) ::  ASetter' s Int -> Int -> PLST s ()
l += x = command (Update (over l (+ x)))  -- specialized version of lens combinator for performance
{-# INLINE (+=) #-}

modify :: (s -> s) -> PLST s ()
modify = command . Update

gets :: Getting a s a -> PLST s a
gets = command . Peeks . view

peeking :: Ix i => Getting (IOArray i e) s (IOArray i e) -> i -> PLST s e
peeking s = peekArray (view s)

poking :: Ix i => Getting (IOArray i e) s (IOArray i e) -> i -> e -> PLST s ()
poking s = pokeArray (view s)

replacing :: Ix i => Getting (IOArray i e) s (IOArray i e) -> i -> (e -> e) -> PLST s e
replacing s = replaceArray (view s)

update :: (s -> s) -> PLST s ()
update = command . Update

replaces :: Lens' s a -> (a -> a) -> PLST s a
replaces l f = command $ Replace (l <<%~f)

peekArray :: Ix i => (s -> IOArray i e) -> i -> PLST s e
peekArray s i = command $ PeekArray s i

pokeArray :: Ix i => (s -> IOArray i e) -> i -> e -> PLST s ()
pokeArray s i x = command $ PokeArray s i x

replaceArray :: Ix i => (s -> IOArray i e) -> i -> (e -> e) -> PLST s e
replaceArray s i f = command $ ReplaceArray s i f

listArray :: Ix i => (i, i) -> [e] -> PLST s (IOArray i e)
listArray b xs = command $ NewArray b xs

putString :: (s -> IO String) -> PLST s ()
putString = command . PutString

nextCycle :: PLST s ()
nextCycle = command NextCycle

block :: PLST s ()
block = command Block

fixupWith :: PLST s () -> PLST s ()
fixupWith = command . Fixup

data PipeAction s a where
  Update :: (s -> s) -> PipeAction s ()
  Replace :: (s -> (x,s)) -> PipeAction s x
  Sets :: s -> PipeAction s ()
  Peeks :: (s -> x) -> PipeAction s x
  Gets :: PipeAction s s
  NextCycle :: PipeAction s ()
  Block :: PipeAction s ()
  Fixup :: PLST s () -> PipeAction s ()
  PeekArray :: Ix i => (s -> IOArray i e) -> i -> PipeAction s e
  PokeArray :: Ix i => (s -> IOArray i e) -> i -> e -> PipeAction s ()
  ReplaceArray :: Ix i => (s -> IOArray i e) -> i -> (e -> e) -> PipeAction s e
  NewArray :: Ix i => (i, i) -> [e] -> PipeAction s (IOArray i e)
  PutString :: (s -> IO String) -> PipeAction s ()

data StageResult s a
  = Done a s
  | NextStage (PLST s a) !s
  | FixupNext (PLST s ()) !s (PLST s a)
  | Blocked

evalPipeStage :: PLST s a -> s -> IO (StageResult s a)
evalPipeStage = eval . commandView where
  eval :: CommandView (PipeAction s) a -> s -> IO (StageResult s a)
  eval (MReturn x       ) = return . Done x
  eval (NextCycle :>>= k) = return . NextStage (k ())
  eval (Block     :>>= k) = return . const (Blocked)
  eval (Fixup  f  :>>= k) = \s -> return (FixupNext f s (k ()))
  eval (Update f  :>>= k) = \s -> evalPipeStage (k ()   ) (f s)
  eval (Replace f :>>= k) = \s -> let (x,s') = f s in x `seq` evalPipeStage (k x) s'
  eval (Sets x    :>>= k) = \_ -> evalPipeStage (k ()      ) x
  eval (Peeks  f  :>>= k) = \s -> evalPipeStage (k $! (f s)) s
  eval (Gets      :>>= k) = \s -> evalPipeStage (k s       ) s
  eval (PeekArray f i :>>= k) = \s -> do
    x <- readArray (f s) i
    evalPipeStage (k x) s
  eval (PokeArray f i x :>>= k) = \s -> do
    writeArray (f s) i x
    evalPipeStage (k ()) s
  eval (ReplaceArray f i r :>>= k) = \s -> do
    let a = f s
    x <- readArray a i
    writeArray a i $! (r x)
    evalPipeStage (k x) s
  eval (NewArray b xs :>>= k) = \s -> do
    y <- newListArray b xs
    evalPipeStage (k y) s
  eval (PutString f :>>= k) = \s -> do
    x <- f s
    putStr x
    hFlush stdout
    evalPipeStage (k ()) s

-- simplified version of Apfelmus operational package
data MonadBuilder cmd a where
  Unit :: a -> MonadBuilder cmd a
  Bind :: MonadBuilder cmd b -> (b -> MonadBuilder cmd a) -> MonadBuilder cmd a
  Cmd  :: cmd a -> MonadBuilder cmd a

command :: cmd a -> MonadBuilder cmd a
command = Cmd

instance Monad (MonadBuilder cmd) where
  return = Unit
  (>>=)  = Bind

instance Functor (MonadBuilder cmd) where
  fmap   = liftM

instance Applicative (MonadBuilder cmd) where
  pure   = return
  (<*>)  = ap

data CommandView cmd a where
  MReturn :: a -> CommandView cmd a
  (:>>=) :: cmd b -> (b -> MonadBuilder cmd a) -> CommandView cmd a

commandView :: MonadBuilder cmd a -> CommandView cmd a
commandView (Unit x               ) = MReturn x
commandView (Unit x       `Bind` g) = commandView (g x)
commandView ((m `Bind` g) `Bind` h) = commandView (m `Bind` (\x -> g x `Bind` h))
commandView (Cmd cmd      `Bind` g) = cmd :>>= g
commandView (Cmd cmd              ) = cmd :>>= Unit

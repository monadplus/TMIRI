{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
module Prog where

import Control.Monad(ap, liftM2)
import Prelude hiding (fail)

-------------------------------------------------------------
-- 2. Backtracking Computation
-------------------------------------------------------------

data Backtr a
  = BReturn a -- Success
  | BFail -- Failure
  | Backtr a :<> Backtr a -- Choice
  deriving (Read, Show, Functor)

instance Functor Backtr => Applicative Backtr where
  pure = BReturn
  (<*>) = ap

instance Applicative Backtr => Monad Backtr where
  return :: a -> Backtr a
  return = pure

  (>>=) :: Backtr a -> (a -> Backtr b) -> Backtr b
  BReturn a >>= r = r a
  BFail >>= _ = BFail
  (p :<> q) >>= r = (p >>= r) :<> (q >>= r)

-- | Syntax for Backtr a
--
-- >>> knapsack' 3 [3,2,1]
knapsack' :: Int -> [Int] -> Backtr [Int]
knapsack' w vs
  | w < 0 = BFail
  | w == 0 = return []
  | w > 0 = do v   <- select vs
               vs' <- knapsack' (w - v) vs
               return (v:vs')
  where
    select :: [a] -> Backtr a
    select = foldr (:<>) BFail . map BReturn

-- | Handler for Backtr a

-- >>> allsols' $ knapsack 3 [3,2,1]
-- [[3],[2,1],[1,2],[1,1,1]]
allsols' :: Backtr a -> [a]
allsols' (BReturn a) = [a]
allsols' (BFail) = []
allsols' (p :<> q) = (allsols' p) ++ (allsols' q)

-------------------------------------------------------------
-- 3. Syntax Signatures
-------------------------------------------------------------

data Prog sig a
  = Return a
  | Op (sig (Prog sig a))
  deriving (Functor)

-- Backtr a ~ Prog Nondet a
data Nondet cnt
  = Fail'
  | cnt :|| cnt
  deriving (Functor)

instance (Functor sig) => Applicative (Prog sig) where
  pure = Return
  (<*>) = ap

instance (Functor sig) => Monad (Prog sig) where
  (Return a) >>= prog = prog a
  (Op op) >>= prog = Op (fmap (>>= prog) op)

-- Coproduct of signatures (to combine syntax)
data (sig1 + sig2) cnt
  = Inl (sig1 cnt)
  | Inr (sig2 cnt)
  deriving (Functor)

infixr 7 +

class (Functor sub, Functor sup) => sub ⊂ sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance Functor sig => sig ⊂ sig where
  inj = id
  prj = Just

instance (Functor sig1, Functor sig2)
    => sig1 ⊂ (sig1 + sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _ = Nothing

instance {-# OVERLAPPABLE #-} (Functor sig1, sig ⊂ sig2)
    => sig ⊂ (sig1 + sig2) where
  inj = Inr . inj
  prj (Inr ga) = prj ga
  prj _ = Nothing

inject :: (sub ⊂ sup) => sub (Prog sup a) -> Prog sup a
inject = Op . inj

project :: (sub ⊂ sup) => Prog sup a -> Maybe (sub (Prog sup a))
project (Op s) = prj s
project _ = Nothing

pattern Fail <- (project -> Just Fail')
fail :: (Nondet ⊂ sig) => Prog sig a
fail = inject Fail'

pattern p :| q <- (project -> Just (p :|| q))
(<||>) :: (Nondet ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
p <||> q = inject (p :|| q)

-- | Base case for coproduct of syntax
-- Given a program of type Prog Void a,
--   it is impossible to use the Op constructor.
-- We can nevertheless extract values
data Void cnt
  deriving Functor

-- This handler is usually the last one to be run.
run :: Prog Void a -> a
run (Return x) = x
run _ = error "Impossible by construction."

-- We will define handlers that deal with a specific part of
-- that signature, and leaves the rest untouched.

-- Other syntax that is not interesting in a given context:
pattern Other s = Op (Inr s)

-- Example: evaluate program with Nondet syntax on the left of its signature.
--
-- This is the lifted/monadized version of allsols where there
-- might be syntax other than that given by Nondet involved.
solutions :: (Functor sig) => Prog (Nondet + sig) a -> Prog sig [a]
solutions (Return a) = return [a]
solutions Fail = return []
solutions (p :| q) = liftM2 (++) (solutions p) (solutions q)
solutions (Other op) = Op (fmap solutions op)
solutions (Op _) = error "Impossible by construction."

-- Monomorphisizing solutions
allsols :: Prog (Nondet + Void) a -> [a]
allsols = run . solutions

-------------------------------------------------------------
-- 4. Composing Semantics
-------------------------------------------------------------

-- Effect handlers approach is that not only the syntax of
-- different effects, but also their semantics can be trivially composed.

data State s cnt
  = Get' (s -> cnt)
  | Put' s cnt
  deriving Functor

pattern Get k <- (project -> Just (Get' k))
get :: (State s ⊂ sig) => Prog sig s
get = inject (Get' return)

pattern Put s k <- (project -> Just (Put' s k))
put :: (State s ⊂ sig) => s -> Prog sig ()
put s = inject (Put' s (return ()))

runState :: Functor sig => s -> Prog (State s + sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a)
runState s (Get k) = runState s (k s)
runState _ (Put s k) = runState s k
runState s (Other op) = Op (fmap (runState s) op)
runState _ _ = error "Impossible by constructin."

-- | state local to the branch (local)
runLocal :: Functor sig => s -> Prog (State s + Nondet + sig) a -> Prog sig [(s, a)]
runLocal s = solutions . runState s
-- | state is shared by all branches (global)
runGlobal :: Functor sig => s -> Prog (Nondet + State s + sig) a -> Prog sig (s, [a])
runGlobal s = runState s . solutions

-- Advantage of effects handler: we get multiple interaction semantis for free
-- The following illustrates that both flavors of nondeterministic states are
-- useful for different purposes.

choices :: (Nondet ⊂ sig, State Int ⊂ sig) => Prog sig a -> Prog sig a
choices (Return a) = return a
choices (Fail) = fail
choices (p :| q) = incr >> (choices p <||> choices q)
choices (Op op) = Op (fmap choices op)

incr :: (State Int ⊂ sig) => Prog sig ()
incr = get >>= put . (succ @Int)

-- | global: how many choice points are explore to find all solutions
-- >>> run . runGlobal (0 :: Int) . choices $ knapsack 3 [3,2,1]
-- (12,[[3],[2,1],[1,2],[1,1,1]])

-- local: how deep in the tree each individual answer is found.
-- >>> run . runLocal (0 :: Int) . choices $ knapsack 3 [3,2,1]
-- [(1,[3]),(5,[2,1]),(5,[1,2]),(9,[1,1,1])]
knapsack :: (Nondet ⊂ sig) => Int -> [Int] -> Prog sig [Int]
knapsack w vs
  | w < 0 = fail
  | w == 0 = return []
  | w > 0 = do v   <- select vs
               vs' <- knapsack (w - v) vs
               return (v:vs')
  where
    select :: (Nondet ⊂ sig) => [a] -> Prog sig a
    select = foldr (<||>) fail . map return

-------------------------------------------------------------
-- 5. Cut and Call
-------------------------------------------------------------

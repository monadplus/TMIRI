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
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
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

-- NOTE same signature as Control.Monad.Free
data Prog sig a
  = Return a
  | Op (sig (Prog sig a))
  deriving (Functor)

-- Backtr a ~ Prog Nondet a
data Nondet cnt
  = Fail'
  | cnt :|| cnt
  deriving (Show, Functor)

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

-- | global: how many choice points are explore to find all solutions
-- >>> run . runGlobal (0 :: Int) . choices $ knapsack 3 [3,2,1]
-- (12,[[3],[2,1],[1,2],[1,1,1]])

-- local: how deep in the tree each individual answer is found.
-- >>> run . runLocal (0 :: Int) . choices $ knapsack 3 [3,2,1]
-- [(1,[3]),(5,[2,1]),(5,[1,2]),(9,[1,1,1])]

-------------------------------------------------------------
-- 5. Cut and Call
-------------------------------------------------------------

-- Handlers don't need to be orthogocal.
-- We can extends nondeterminism with a non-orthogonal feature.

data Cut cnt = Cutfail'
  deriving Functor
pattern Cutfail <- (project -> Just Cutfail')
cutfail :: (Cut ⊂ sig) => Prog sig a
cutfail = inject Cutfail'

call :: (Nondet ⊂ sig) => Prog (Cut + sig) a -> Prog sig a
call p = go p fail where
  -- Accumulates in its second parameter q the unexplored alternatives to p.
  -- Return/Fail => explores the accumulated alternatives.
  -- Cutfail => computation fails immediately, without exploring any alternatives.
  go :: (Nondet ⊂ sig) => Prog (Cut + sig) a -> Prog sig a -> Prog sig a
  go (Return a) q = (return a) <||> q
  go (Fail) q = q
  go (Cutfail) q = fail
  go (p1 :| p2) q = go p1 (go p2 q)
  go (Other op) q = Op (fmap (`go` q) op)

cut :: (Nondet ⊂ sig, Cut ⊂ sig) => Prog sig ()
cut = skip <||> cutfail

skip :: Monad m => m ()
skip = return ()

-- | Commit the computation to the current branch, prunning any unexplored alternatives.
--
-- For each Prog leaf, replace it value for (return x <||> cutfail).
-- Then call will replace all nodes except the first return by fail (because of the cutfail).
--    (return a :| Cutfail)
once :: (Nondet ⊂ sig) => Prog (Cut + sig) b -> Prog sig b
once p = call (do x <- p; cut; return x)

-- >>> run . solutions . once $ knapsack 3 [3,2,1]
-- [[3]]

-------------------------------------------------------------
-- 6. Grammars
-------------------------------------------------------------

-- Central problem of the paper.

-- A handler like `call` is called a **scoping handler**, because it not only
-- provides the semantics for particular syntax, but also creates a local scope
-- in which the impact of an effect is contained.

-- The two roles of scoping hadlers:
-- * different orders of handlers affect the interaction semantics.
-- * different scopes affect the extent of an effect's impact.

-- With scoping handlers these two choices are not independent; we cannot affect
-- one without the order.

-- Example: Grammars

data Symbol cnt
  = Symbol' Char (Char -> cnt)
  deriving Functor
pattern Symbol c k <- (project -> Just (Symbol' c k))
symbol :: (Symbol ⊂ sig) => Char -> Prog sig Char
symbol c = inject (Symbol' c return)

-- Nondeterministically attemps to match all of the digits.
-- Fails if this is not possible.
digit :: (Nondet ⊂ sig, Symbol ⊂ sig) => Prog sig Char
digit = foldr (<||>) fail (fmap symbol ['0'..'9'])

many,many1 :: (Nondet ⊂ sig) => Prog sig a -> Prog sig [a]
many p = many1 p <||> return []
many1 p = do a <- p; as <- many p; return (a:as)

-- Handler for Grammar: transforms the grammar to a nondeterministic programm.
--
-- fails if the input is not entirely consumed, or if the grammar expectes more symbols.
parse :: (Nondet ⊂ sig) => [Char] -> Prog (Symbol + sig) a -> Prog sig a
parse     [] (Return a) = return a
parse (x:xs) (Return a) = fail -- fail if there are still things to parse
parse     [] (Symbol c k) = fail
parse (x:xs) (Symbol c k)
  | x == c    = parse xs (k x)
  | otherwise = fail
parse xs (Other op) = Op (fmap (parse xs) op) -- Nondet is happening here.

-- Parsing arithmetic expressions:
--  * expr deals with sums
--  * term deals with products

-- We return the result of evaluating the payload directly.
expr :: (Nondet ⊂ sig, Symbol ⊂ sig) => Prog sig Int
expr = do i <- term; symbol '+'; j <- expr; return (i + j)
  <||> do i <- term; return i

term :: (Nondet ⊂ sig, Symbol ⊂ sig) => Prog sig Int
term = do i <- factor; symbol '*'; j <- term; return (i*j)
  <||> do i <- factor; return i

-- terminal case: string of digits or expression in parentheses.
factor :: (Nondet ⊂ sig, Symbol ⊂ sig) => Prog sig Int
factor = do ds <- many1 digit; return (read @Int ds)
  <||> do symbol '('; i <- expr; symbol ')'; return i

-- >>> allsols . parse "(2+2)*5+1" $ expr
-- [21]

-- Grammar refactoring: performance (parse will not explore other alternatives)

expr1 :: (Nondet ⊂ sig, Symbol ⊂ sig) => Prog sig Int
expr1 = do
  i <- term
  (do symbol '+'; j <- expr1; return (i + j)
    <||> do return i)

-- Pruning after consuming '+' seems like a sensible idea.
-- This way we avoid exploring the second branch that will *always* fail.
--
-- The locally placed _call_ handler is needed to delimit the scope of the cut.
-- After all the cut is only meant to prune the one alternative, and should
-- not affect other alternatives made elsewhere in the grammar.

-- The problem:
--
-- >>> allsols . parse "1" $ expr2
-- [] -- expected [1]
--
-- What has happened ?
expr2 :: (Nondet ⊂ sig, Symbol ⊂ sig) => Prog sig Int
expr2 = do
  i <- term
  call (do symbol '+'; cut; j <- expr2; return (i + j)
          <||> do return i)

{-
The problem is taht we have chosen the wrong order for the parse and call handlers,
  which leads to the undesired interaction.
The appropiate interaction is obtained by first applying parse and the call handlers.

Unfortunately, we cannot reorder call and parse for other reasons: call creates
a local scope. We cannot put it anywhere else without risking that cut prunes more
alternatives than it should. Conversely, it obviously does not make sense to apply
parse only in the local scope of call.
-}

{-
The copuling of scoping and semantics in scoping handlers is problematic.

Solution: decouple scoping from semantics by making scoping the province of syntax.

1. lightweight, fits better in the handlers model, error prone.
2. robust and expressive but requires much heavier machinery.
-}

-------------------------------------------------------------
-- 7. Scoped Syntax
-------------------------------------------------------------

-- Explicitly delimit the beginning and end of the scope of the _call_.

data Call cnt
    = BCall' cnt
    | ECall' cnt
  deriving (Functor)

pattern BCall p <- (project -> Just (BCall' p))
pattern ECall p <- (project -> Just (ECall' p))

-- | Ensure that each BCall is pared with an ECall.
call'
  :: (Call ⊂ sig)
  => Prog sig a
  -> Prog sig a
call' p = do begin; x <- p; end; return x where
  begin = inject (BCall' (return ()))
  end = inject (ECall' (return ()))

expr3
  :: (Nondet  ⊂ sig
     , Symbol ⊂ sig
     , Call   ⊂ sig
     , Cut    ⊂ sig
     ) => Prog sig Int
expr3 = do
  i <- term
  call' (do symbol '+'; cut; j <- expr3; return (i + j)
            <||> do return i)

-- >>> run . solutions . runCut . parse "1" $ expr3

-- | Eliminate Call and Cut from the signature:
runCut
  :: (Nondet  ⊂ sig)
  => Prog (Call + Cut + sig) a
  -> Prog sig a
runCut p = call (bcall p)

bcall
  :: (Nondet  ⊂ sig)
  => Prog (Call + Cut + sig) a
  -> Prog (Cut + sig) a
bcall (Return a) = return a
bcall (BCall p) = upcast (call (ecall p)) >>= bcall -- execute everything until next ecall
bcall (ECall a) = error "Mismatched ECall!"
bcall (Other op) = Op (fmap bcall op)

-- | Takes a program with scoped synta and
-- modifies it so that any scope content is removed.
ecall
  :: (Nondet  ⊂ sig)
  => Prog (Call + Cut + sig) a
  -> Prog (Cut + sig) (Prog (Call + Cut + sig) a)
ecall (Return a) = return (Return a)
ecall (BCall p) = upcast (call (ecall p)) >>= ecall
ecall (ECall p) = return p
ecall (Other op) = Op (fmap ecall op)

-- | extends a signature so that it contains an additional syntax functor.
upcast
  :: ( Functor f
     , Functor sig)
  => Prog sig a
  -> Prog (f + sig) a
upcast (Return x) = return x
upcast (Op op) = Op (Inr (fmap upcast op))

-- >>> run . solutions . runCut . parse "1" $ expr3
-- [1]

-------------------------------------------------------------
-- 8. Exceptions
-------------------------------------------------------------

-- syntax
data Exc e cnt
    = Throw' e
  deriving (Functor)
pattern Throw e <- (project -> Just (Throw' e))
throw :: (Exc e ⊂ sig) => e -> Prog sig a
throw e = inject (Throw' e)

-- handler
runExc
  :: Functor sig
  => Prog (Exc e + sig) a
  -> Prog sig (Either e a)
runExc (Return x) = return (Right x)
runExc (Throw e) = return (Left e)
runExc (Other op) = Op (fmap runExc op)

catch
  :: (Exc e ⊂ sig)
  => Prog sig a
  -> (e -> Prog sig a)
  -> Prog sig a
catch (Return x) h = return x
catch (Throw e) h = h e
catch (Op op) h = Op (fmap (\p -> catch p h) op)

-- Same problem as our initial version of call:
--  its does not compose as flexibly as it could.

-- Example: interaction of exceptions and state.
--
-- Decrement the state counter three times, and if an exception
--   is thrown it is handled with return:
tripleDecr :: (State Int ⊂ sig, Exc () ⊂ sig) => Prog sig ()
tripleDecr = decr >> catch (decr >> decr) return
  where
    decr :: (State Int ⊂ sig, Exc () ⊂ sig) => Prog sig ()
    decr = do
      x <- get
      if x > (0 :: Int)
        then put (pred x)
        else throw ()

-- Expected final states:
--  * global) final state of 0, where the first two decrs persist
--  * local) all effects within a catch to be rolled back, so that the final state 1 is the result of the first decr only.
--
-- Reordering handlers should allow both behaviours.
-- However, because catch is a scoping handler that creates a local scope,
-- we can only express the global interpretration

tripleDecrExample :: Either () (Int, ())
tripleDecrExample = run . runExc . runState 2 $ tripleDecr

-- Exchanging catch and runState does not make sense, because
-- it would change the scope created by catch.

-------------------------------------------------------------
-- 9. Scoped Syntax Revisited
-------------------------------------------------------------

-- The scoped syntax in Section 7 is insufficient to capture the behaviour of exceptions.
-- The issue is that a catch block has two different continuations in addition to the body
-- that is to be executed: one cont. in the case where no exceptions are thrown,
-- and another for the exception handler.

data Catch e cnt
    = BCatch' cnt (e -> cnt)
    | ECatch' cnt
  deriving (Functor)
pattern BCatch p q <- (project -> Just (BCatch' p q))
pattern ECatch p <- (project -> Just (ECatch' p))
-- pattern BCatch :: forall e sup a. (Catch e ⊂ sup) => Prog sup a -> (e -> Prog sup a) -> Prog sup a
-- pattern ECatch :: forall e sup a. (Catch e ⊂ sup) => Prog sup a -> Prog sup a
-- pattern ECatch p <- (project @(Catch e) -> Just (ECatch' p))

-- Syntactic sugar that ensures the tags are matched appropriately:
catch'
  :: forall e sig a. (Catch e ⊂ sig)
  => Prog sig a
  -> (e -> Prog sig a)
  -> Prog sig a
catch' p h = begin (do x <- p; end; return x) h where
  begin p q = inject (BCatch' p q)
  end = inject (ECatch' (return ()) :: Catch e (Prog sig ()))

runCatch
  :: (Functor sig)
  => Prog (Catch e + (Exc e + sig)) a -> Prog sig (Either e a)
runCatch p = runExc (bcatch p)

-- searches for a BCatch p q, when one is encountered, it recursively runs exceptio nhandling on p.
-- If an exception is raised, then the handling code q is used for the cont.
bcatch
  :: forall sig e a. (Functor sig)
  => Prog (Catch e + (Exc e + sig)) a
  -> Prog (Exc e + sig) a
bcatch (Return a) = return a
bcatch (BCatch p q) = do
  r <- upcast (runExc (ecatch p))
  case r of
    Left e   -> bcatch (q e)
    Right p' -> bcatch p'
bcatch (project @(Catch e) -> Just (ECatch' _)) = error "Mismatched ECatch!"
bcatch (Other op) = Op (fmap bcatch op)

ecatch
  :: forall sig e a. (Functor sig)
  => Prog (Catch e + (Exc e + sig)) a
  -> Prog (Exc e + sig) (Prog (Catch e + (Exc e + sig)) a)
ecatch (Return a) = return (Return a)
ecatch (BCatch p q) = do
  r <- upcast (runExc (ecatch p))
  case r of
    Left e   -> ecatch (q e)
    Right p' -> ecatch p'
ecatch (project @(Catch e) -> Just (ECatch' p)) = return p
ecatch (Other op) = Op (fmap ecatch op)

tripleDecr' :: (State Int ⊂ sig, Exc () ⊂ sig, Catch () ⊂ sig) => Prog sig ()
tripleDecr' = decr >> catch' (decr >> decr) return
  where
    decr = do
      x <- get
      if x > (0 :: Int)
        then put (pred x)
        else throw ()

-- Now, we can change the behaviour by composing runCatch and runState in
-- different orders:

-- Local
--
-- >>> tripleDecrExample'
-- Right (1,())
tripleDecrExample' :: Either () (Int, ())
tripleDecrExample' = run . runCatch . runState 2 $ tripleDecr'

-- Global
--
-- >>> tripleDecrExample''
-- (0,Right ())
tripleDecrExample'' :: (Int, Either () ())
tripleDecrExample'' = run . runState 2 . runCatch $ tripleDecr'

-------------------------------------------------------------
-- 10. Higher-Order Syntax
-------------------------------------------------------------

-- Moved to Prog2.hs

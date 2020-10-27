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
module Prog2 where

import Prelude hiding (log)
import Control.Monad (ap, join, liftM)

-- Previous definitions that are also used in the following sections

-------------------------------------------------------------
-- 10. Higher-Order Syntax
-------------------------------------------------------------

-- the previous section used syntax to carefully mark the beggining/end of a syntax block.

-- A more direct solution is to model scoping constructs with higher-order syntax, where
-- the syntax carries those syntax blocks directly.
--
-- For the handler catch p h, we introduce the following signature, where
-- the syntax Catch' p h k carries the program contained in p directly
-- as an argument, as well as the exception handler h. The continuation is k,
-- which takes the result of either a succesful program p, or from the exception handler h.

-- 'cnt' is split in 'm' and 'a' to have tigher control over the type of cont.
data HExc e m a
  = Throw' e
  | forall x. Catch' (m x) (e -> m x) (x -> m a)

-- Higher-order signatures are functorial in both type parameters.
-- The last parameter a clearly satisfy the ordinary functor laws when m is a functor.

instance Functor m => Functor (HExc e m) where
  fmap _ (Throw' e) = Throw' e
  fmap f (Catch' p h k) = Catch' p h (fmap f . k)

-- Natural transformation
type f ~> g = forall x. f x -> g x

-- High-order functor
class HFunctor (h :: (* -> *) -> * -> *) where
  hmap :: (Functor f, Functor g) => (f ~> g) -> (h f ~> h g)

-- This allow us to transform the type constructor m with a natural transformation.
instance HFunctor (HExc e) where
  hmap _ (Throw' x) = Throw' x
  hmap t (Catch' p h k) = Catch' (t p) (t . h) (t . k)

{-
Higher-order signatures depart from ordinary ones in an important way:
 they support more precise control over how they compose, and how handlers
 must traverse them.

In first-order signatures this control is determined entirely by the functor instance,
but on deeper inspection the function fmap :: (cnt -> cnt') -> (sig cnt -> sig cnt') plays two roles:
first, to extend the continuation captured by the syntax, and second, to thread
handlers through the syntax.

We separate these two roles into different functions for higher-order syntax,
where they will not always coincide.
-}

class HFunctor sig => Syntax sig where
  -- extend the continuation
  emap :: (m a -> m b) -> (sig m a -> sig m b)
  -- how handlers should be threaded through the syntax
  weave :: (Monad m, Monad n, Functor s)
    => s () -> Handler s m n -> (sig m a -> sig n (s a))

-- capture state when it suspends and make it available when resuming.
type Handler s m n = forall x. s (m x) -> n (s x)

-- We describe this functions in more detail:

{- Extending the Continuation

This type is obtained by refinint 'cnt' to 'm a' in the signature of fmap

emap id = id
emap f . emap g = emap (f . g)

The fmap on the left hand side is from the functor instance of sig m
and this should agree with the fmap for m when extended by emap.

fmap = emap . fmap

-}

-- Since higher-order signatures and programsa are a generalization of first-order ones,
-- we will redefine all of the infraestructure so that it works in this setting.

-- Has to work for @Prog (HExc e)@ where 'HExc e m a'
data Prog (sig :: (* -> *) -> * -> *) (a :: *)
  = Return a
  | Op (sig (Prog sig) a)

{-
we use emap in the definition of the free monad Prog over higher-order
signatures, since this is where continuations get plugged together.
-}

-- FIXME this may be problematic
instance Functor (Prog sig) where
  fmap = undefined

-- FIXME this may be problematic
instance Applicative (Prog sig) where
  pure = undefined
  (<*>) = undefined

instance Syntax sig => Monad (Prog sig) where
  return v = Return v
  Return v >>= prog = prog v
  Op op >>= prog = Op (emap (>>= prog) op)

-- The restricted type of emap precisely captures our requirements
-- here, where m is Prog sig

{- Distributing Handlers

Scoped syntax such as Catch' p h k represents a sequential
computation 'p >>= k' where 'p' is isolated in a scope.
However, this scope is only relevant for the interpretation of Throw' e,
and not for other effects.

The generic threading of another handler 'hdl' through Catch' p h k
results in Catch' p' h' k'.

When no exception is throw in p, then p' >>= k' should be equivalent to running
the 'hdl' on p >>= k. This means that it should be possible to suspend handlers
and resume them from an intermediate point like inbetween p and k.

Because a handler may be stateful, we need to capture its intermediate state
when it suspends and make it available when resuming.

We capture these requirements in the 'Handler s m n'.

   type Handler s m n = forall x. s (m x) -> n (s x)

Here 's' is a functor that captures the computation state of the handler.

A higher-order handler is then a function that transforms a state-annotated
computation in one monad 'm' into a computation in another monad 'n' whose value
is annotated with the final state.

The type of a handler `hdl :: Handler s m n` reveals that it is a natural transf.

  hdl . fmap return = return                      (4)
  hdl . fmap join = join . fmap hdl. hdl          (5)

(4) the handler preserves a pure computation without modifying its state

(5) it makes no difference whether a composite computation is transformed
    before or after composition. Rewritten as:

  hdl (fmap (>>= k) sm) = hdl sm >>= hdl . fmap k (5)

The 'weave' method generically threads a handler through a higher-order signature.
Also, it takes the initial state of 's', represented by 's ()'

  weave :: (Monad m, Monad n, Functor s)
    => s () -> Handler s m n -> (sig m a -> sig n (s a))

Its interpretation is perhaps best understood with an example: here
is the Call instance of the Syntax class:
-}

instance Syntax (HExc e) where
  emap :: (m a -> m b) -> (HExc e m a -> HExc e m b)
  emap _ (Throw' e) = Throw' e
  emap f (Catch' p h k) = Catch' p h (f . k)

  -- type Handler s m n = forall x. s (m x) -> n (s x)
  weave :: (Monad m, Monad n, Functor s)
    => s () -> Handler s m n -> (HExc e m a -> HExc e n (s a))
  weave _   _ (Throw' x) = Throw' x
  weave f hdl (Catch' p h k) =   -- Notice how x is interchanged with s x
    Catch' (hdl $ fmap (const p) f) -- n (s x)
           (\e -> hdl $ fmap (const (h e)) f) -- e -> n (s x)
           (hdl . fmap k) -- \(s x) -> n (s a)

-- 10.1 Infrastructure

-- Adaptation of the previous syntax:
--  * The functor constraint becomes Syntax instead
--  * The continuation parameter `cnt` becomes `m a`

data (sig1 + sig2) (m :: * -> *) (a :: *)
  = Inl (sig1 m a)
  | Inr (sig2 m a)
infixr 7 +

instance (HFunctor sig1, HFunctor sig2)
    => (HFunctor (sig1 + sig2)) where
  hmap t (Inl op) = Inl (hmap t op)
  hmap t (Inr op) = Inr (hmap t op)

instance (Syntax sig1, Syntax sig2)
    => (Syntax (sig1 + sig2)) where
  emap f (Inl op) = Inl (emap f op)
  emap f (Inr op) = Inr (emap f op)
  weave s hdl (Inl op) = Inl (weave s hdl op)
  weave s hdl (Inr op) = Inr (weave s hdl op)

class (Syntax sub, Syntax sup) => sub ⊂ sup where
  inj :: sub m a -> sup m a
  prj :: sup m a -> Maybe (sub m a)

instance Syntax sig => sig ⊂ sig where
  inj = id
  prj = Just

instance (Syntax sig1, Syntax sig2)
    => sig1 ⊂ (sig1 + sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _ = Nothing

instance {-# OVERLAPPABLE #-} (Syntax sig1, sig ⊂ sig2)
    => sig ⊂ (sig1 + sig2) where
  inj = Inr . inj
  prj (Inr ga) = prj ga
  prj _ = Nothing

-- data Prog (sig :: (* -> *) -> * -> *) (a :: *)
--   = Return a
--   | Op (sig (Prog sig) a)
inject :: (sub ⊂ sup) => sub (Prog sup) a -> Prog sup a
inject = Op . inj

project :: (sub ⊂ sup) => Prog sup a -> Maybe (sub (Prog sup) a)
project (Op s) = prj s
project _ = Nothing

pattern Throw e <- (project -> Just (Throw' e))
throw :: (HExc e ⊂ sig) => e -> Prog sig a
throw e = inject (Throw' e)

pattern Catch p h k <- (project -> Just (Catch' p h k))
catch :: (HExc e ⊂ sig) => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catch p h = inject (Catch' p h return)

pattern Other s = Op (Inr s)

{-
We can easily lift our existing first-order signatures to higher-order signatures.,
by performing the refinement of 'cnt' to 'm a'.
-}

newtype Lift sig (m :: * -> *) a = Lift (sig (m a))

instance Functor sig => HFunctor (Lift sig) where
  hmap t (Lift op) = Lift (fmap t op)

instance Functor sig => Syntax (Lift sig) where
  emap f (Lift op) = Lift (fmap f op)
  weave s hdl (Lift op) =
    Lift (fmap (\p -> hdl (fmap (const p) s)) op)

{-
Providing signatures and syntax for first-order syntax is now simple boilerplate.
-}

-- HVoid syntax

data Void cnt deriving Functor
type HVoid = Lift Void
run :: Prog HVoid a -> a
run (Return x) = x

-- HState syntax

data State s cnt
  = Get' (s -> cnt)
  | Put' s cnt
  deriving Functor

type HState s = Lift (State s)

pattern Get k <- (project -> Just (Lift (Get' k)))
get :: (HState s ⊂ sig) => Prog sig s
get = inject (Lift (Get' return))

pattern Put s k <- (project -> Just (Lift (Put' s k)))
put :: (HState s ⊂ sig) => s -> Prog sig ()
put s = inject (Lift (Put' s (return ())))

-- 10.2 Higher-Order Handlers

{-
First handler: runState

Two things have changed:
  * the type signature is modified to use HState
  * The clause for 'Other op' involves weave.
-}

runState :: Syntax sig
  => s -> Prog (HState s + sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a)
runState s (Get k) = runState s (k s)
runState _ (Put s k) = runState s k
runState s (Other op) = Op (weave (s, ()) (uncurry runState) op)

runExc
  :: forall sig e a. Syntax sig
  => Prog (HExc e + sig) a
  -> Prog sig (Either e a)
runExc (Return x) = return (Right x)
runExc (Throw e) = return (Left e)
runExc (project @(HExc e) -> Just (Catch' p h k)) = do
  r <- runExc p
  case r of
    Right a -> runExc (k a)
    Left e -> do
      r <- runExc (h e)
      case r of
        Left e -> return (Left e) -- Unhandled exception
        Right a -> runExc (k a) -- k a may throw exception
runExc (Other op) = Op (weave (Right ()) hdl op) where
  hdl :: Syntax sig => Handler (Either e) (Prog (HExc e + sig)) (Prog sig)
  hdl = either (return . Left) runExc -- propagate error when encountered

tripleDecr :: (HState Int ⊂ sig, HExc () ⊂ sig) => Prog sig ()
tripleDecr = decr >> (catch (decr >> decr) return)

incr :: (HState Int ⊂ sig) => Prog sig ()
incr = get >>= put . (succ @Int)

decr :: (HState Int ⊂ sig, HExc () ⊂ sig) => Prog sig ()
decr = do
  x <- get
  if x > (0 :: Int)
    then put (pred x)
    else throw ()

-- >>> tripleDecrExample
-- Right(1, ())
tripleDecrExample :: Either () (Int, ())
tripleDecrExample = run . runExc . runState 2 $ tripleDecr

-- >>> tripleDecrExample'
-- (0, Right())
tripleDecrExample' :: (Int, Either () ())
tripleDecrExample' = run . runState 2 . runExc $ tripleDecr

-------------------------------------------------------------
-- 11. Multi-Threading
-------------------------------------------------------------

{-
The examples of scoped effects we have seen so far:
  * pruning non-deterministic computations
  * and exception handling
have been solved by clever use of first-order syntax tagging, and also by higher-order syntax.

Then, are both techniques equally expressive ?
Cooperative multi-threading can only be solved with higher-order syntax.

-}

{-

'fork d' spaws a new thread d
'yield' relinquishes control

'yield' is a plain algebraic operation
'fork' is clearly a scoping construct that delimits the new thread.

data Thread cnt -- BOGUS!
  = Yield' cnt
  | Fork' cnt cnt -- Fork' p q represent a computation that spawns a new thread p
                  -- while the master thread continues with q

The problem is that, in the first-order framework, we have that:

    Op (Fork' p q) >>= k = Op (Fork' (p >>= k) (q >>= k))

not the expected semantics, the continuation should only be applied to the remainding of the parent q.

    Op (Fork' p q) >>= k = Op (Fork' p (q >>= k))

We need to distinguish between the subcomputation for the child and the parent.
And only higher-order syntax does:
-}

data Thread m a
  = Yield' (m a)
  | forall x. Fork' (m x) (m a) -- note how child has an existential return type.

pattern Yield p <- (project -> Just (Yield' p))
yield :: (Thread ⊂ sig) => Prog sig ()
yield = inject (Yield' (return ()))

pattern Fork p q <- (project -> Just (Fork' p q))
fork :: (Thread ⊂ sig) => Prog sig x -> Prog sig ()
fork d = inject (Fork' d (return ()))

instance HFunctor Thread where
  hmap t (Yield' p) = Yield' (t p)
  hmap t (Fork' d p) = Fork' (t d) (t p)

instance Syntax Thread where
  emap f (Yield' p) = Yield' (f p)
  emap f (Fork' d p) = Fork' d (f p)
  weave s hdl (Yield' p) = Yield' (hdl (fmap (const p) s))
  weave s hdl (Fork' d p) = Fork' (hdl (fmap (const d) s)) (hdl (fmap (const p) s))

{-
Note that the result type of the new thread is existentially quantified.

This is in line with the notion that in Fork'  p >>= k the continuatiion k
does not interact with the child's result.

We call a thread with an existentially quantified result type a daemon,
in contrast with the master thread of the program.

-}

data Daemon sig = forall x. Daemon (Prog (Thread + sig) x)

-- 11.2 Handler

-- | Thread state
data SThread sig r
  = SYield (Prog (Thread + sig) r) -- ^ default
  | SFork (Daemon sig)
          (Prog (Thread + sig) r)  -- ^ suspended after fork, should continue with p
  | SActive r                      -- ^ suspended after yield, should continue with p

instance Syntax sig => Functor (SThread sig) where
  fmap f (SActive x) = SActive (f x)
  fmap f (SYield p) = SYield (liftM f p)
  fmap f (SFork d p) = SFork d (liftM f p)

-- The handlers

runThread
  :: Syntax sig
  => Prog (Thread + sig) x
  -> Prog sig (SThread sig x)
runThread (Return x) = return (SActive x)
runThread (Yield q) = return (SYield q)
runThread (Fork d q) = return (SFork (Daemon d) q)
runThread (Other op) = Op (weave (SActive ()) thread op)

-- how to continue from an intermediate state
thread
  :: Syntax sig
  => Handler (SThread sig) (Prog (Thread + sig)) (Prog sig)
thread (SActive p) = runThread p
thread (SYield p) = return (SYield (join p))
thread (SFork d p) = return (SFork d (join p))

-- | Runs the master thread and daemons in round-robin fashion.
--
-- We keep track of master thread 'p'
--
-- The program ends when the master thread ends;
-- any unfinished daemons are discarded.
schedule :: Syntax sig => Prog (Thread + sig) a -> Prog sig a
schedule p = master p [] where
  master p ds = do
    r <- runThread p
    case r of
      SActive x -> return x
      SYield p -> daemons ds [] p
      SFork d p -> daemons (d:ds) [] p
  daemons [] ds' p = master p (reverse ds')
  daemons (Daemon q : ds) ds' p = do
    r <- runThread q
    case r of
      SActive _   -> daemons      ds             ds' p
      SYield q'   -> daemons      ds (Daemon q':ds') p
      SFork d' q' -> daemons (d':ds) (Daemon q':ds') p

-- 11.3 Threading in Action

-- Syntax for IO.

data Out cnt = Out' String cnt -- the string should be written out
  deriving (Functor)
type HOut = Lift Out
pattern Out s p <- (project -> Just (Lift (Out' s p)))
out :: (HOut ⊂ sig) => String -> Prog sig ()
out s = inject (Lift (Out' s (return ())))

-- io handler
io :: Prog HOut a -> IO a
io (Return x) = return x
io (Out s p) = putStrLn s >> io p

prog :: (Thread ⊂ sig, HState Int ⊂ sig, HOut ⊂ sig) => Prog sig ()
prog = do
  logIncr "master"
  fork (logIncr "daemon" >> logIncr "daemon")
  logIncr "master"

log :: (HState Int ⊂ sig, HOut ⊂ sig) => String -> Prog sig ()
log x = do (n :: Int) <- get; out (x ++ ": " ++ show n)

logIncr :: (HState Int ⊂ sig, HOut ⊂ sig) => String -> Prog sig ()
logIncr x = log x >> incr

{-
We can achieve different semantics:
  * Global state, shared between threads
  * Local state to each thread
-}

-- Global state
-- >>> (io . runState (0 :: Int) . schedule) prog
-- master: 0
-- daemon: 1
-- daemon: 2
-- master: 3
-- (4,())

-- Local state
-- >>> (io . schedule . runState (0 :: Int)) prog
-- master: 0
-- daemon: 1
-- daemon: 2
-- master: 1
-- (2,())

-------------------------------------------------------------
-- 12. Related Work
-------------------------------------------------------------

{-
Plotkin and Power were the first to explore effect
  operations (from a category theory prespective):

  * Notions of computation determine monads
  * Algebraic operations and generic effects
  * Combining effects: Sum and tensor

they even introduced the notion of handlers:

  * Handlers of Algebraic Effects

Languages:

Based on this idea, two entirely new programming
languages have been created from the ground up
around algebraic effect handlers

  * Eff: ML-variant that does not track effect in its static type system
  * Frank: tracks effect signatures in its static type system (higher-order not allowed)

Libraries:

  * Idris provides an effect handlers approach
  * Krammar et al. based on free monad and cps (scoping syntax not covered)
  * Kiselyov et al. haskell impl. in terms of the free monad (scoping syntax not covered)

Kiselyov et al. are the first to provide handler for Cut but do not discuss the scoping problem.


-}

{- Conclusions

Effect handlers for scoping fixes the interaction between effects.

Syntax should determine scope.

Two approaches:

  * (1) scope markers
  * (2) high-order syntax

(1) play nicely with all existing effect handler frameworks

(2) more expressive and natural way to denote scoping (no unbalance).

Open question: how to implement higher-order syntax on top of delimited
continuations, which is the basis for effect handlers in strict languages.
-}

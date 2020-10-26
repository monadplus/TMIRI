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

import Control.Monad (ap)

-------------------------------------------------------------
-- 10. Higher-Order Syntax
-------------------------------------------------------------

-- the previous section used syntax to carefully mark the beggining/end of a syntax block.

-- A more direct solution is to model scoping constructs with higher-order syntax, where
-- the syntax carries those syntax blocks directly.
--
-- For the handler catch p h, we introduce the following signature, where
-- the syntax Catch' p h k carries teh program contained in p directly
-- as an argument, as well as the exception handler h. The continuation is k,
-- which takes the result of either a succesful program p, or from the exception handler h.

-- 'cnt' is split in 'm' and 'a' to have tigher control over the type of cont.
data HExc e m a
  = Throw' e
  | forall x. Catch' (m x) (e -> m x) (x -> m a)

-- higher-order signatures are functorial in both type parameters.
-- The last parameter a clearly satisfy the ordinary functor laws when m is a functor.

instance Functor m => Functor (HExc e m) where
  fmap _ (Throw' e) = Throw' e
  fmap f (Catch' p h k) = Catch' p h (fmap f . k)

type f ~> g = forall x. f x -> g x

class HFunctor (h :: (* -> *) -> * -> *) where
  hmap :: (Functor f, Functor g) => (f ~> g) -> (h f ~> h g)

instance HFunctor (HExc e) where
  hmap _ (Throw' x) = Throw' x
  hmap t (Catch' p h k) = Catch' (t p) (t . h) (t . k)

-- This allow us to transform the type constructor m with a natural transformation.

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

-- sig :: (* -> *) -> * -> *
class HFunctor sig => Syntax sig where
  -- extend the continuation
  emap :: (m a -> m b) -> (sig m a -> sig m b)
  -- how handlers should be threaded through the syntax
  weave :: (Monad m, Monad n, Functor s)
    => s () -> Handler s m n -> (sig m a -> sig n (s a))

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


-}

-------------------------------------------------------------
-- 11. Multi-Threading
-------------------------------------------------------------

-------------------------------------------------------------
-- 12. Related Work
-------------------------------------------------------------

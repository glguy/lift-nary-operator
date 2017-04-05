{-# Language
     TypeFamilies, GADTs, DataKinds, ConstraintKinds, RankNTypes,
     TypeOperators, ScopedTypeVariables, KindSignatures,
     FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
     AllowAmbiguousTypes, TypeApplications
  #-}

{-|
Module      : Derive
Description : Implement the generic lifting of n-ary operators to product types
Copyright   : (c) Eric Mertens, 2016
License     : ISC
Maintainer  : emertens@gmail.com
-}

module Derive
  ( -- * Natural numbers
    Nat(..)
  , NatVal(..)
  , KnownNat(..)

  -- * Length-indexed vectors
  , V(..)

  -- * N-ary functions
  , FunN(..)
  , Op
  , curryN
  , uncurryN

  -- * Generic operator lifting
  , GOpN(..)
  , genericOpN
  ) where

import Control.Applicative
import Control.Monad
import Data.Profunctor
import GHC.Generics

-- | Kind of natural numbers.
data {-kind-} Nat :: * where
  Z ::        Nat
  S :: Nat -> Nat

-- | Value-level view of natural numbers.
data NatVal :: Nat -> * where
  IsZ ::             NatVal 'Z
  IsS :: NatVal n -> NatVal ('S n)

-- | Value-level access to type-level natural number.
class                  KnownNat n      where knownNat :: NatVal n
instance               KnownNat 'Z     where knownNat = IsZ
instance KnownNat n => KnownNat ('S n) where knownNat = IsS knownNat

------------------------------------------------------------------------

-- | Vectors indexed by their lengths.
data V n a where
  Nil  ::               V 'Z a
  Cons :: a -> V n a -> V ('S n) a

instance Functor (V n) where
  fmap _ Nil         = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

------------------------------------------------------------------------

-- | N-ary function taking @n@ arguments of type @a@ to produce @b@.
newtype FunN n a b = FunN { ($$) :: V n a -> b }

infixl 9 $$

instance Profunctor (FunN n) where
  dimap f g (FunN h) = FunN (g . h . fmap f)

-- | /Reader/-like behavior
instance Functor (FunN n e) where fmap = liftM

-- | /Reader/-like behavior
instance Applicative (FunN n e) where
  pure  = FunN . const
  (<*>) = ap

-- | /Reader/-like behavior
instance Monad (FunN n e) where
  m >>= f = FunN (\x -> f (m $$ x) $$ x)

------------------------------------------------------------------------

-- | N-ary 'uncurry'.
uncurryN :: Op n a b -> V n a -> b
uncurryN x Nil         = x
uncurryN f (Cons x xs) = uncurryN (f x) xs

-- | N-ary 'curry'.
curryN :: forall n a b. KnownNat n => (V n a -> b) -> Op n a b
curryN = go (knownNat @n)
  where
    go :: forall m. NatVal m -> (V m a -> b) -> Op m a b
    go IsZ     f = f Nil
    go (IsS n) f = \x -> go n (f . Cons x)

-- | Family of N-ary operator types.
type family Op n a b where
  Op 'Z     a b = b
  Op ('S n) a b = a -> Op n a b

------------------------------------------------------------------------

-- | Class for lifting an N-ary operator for instances of some
-- typeclass @c@ to work over the generic representation of a
-- product type.
class GOpN c f where
  -- | Lift a polymorphic operator constrained by a typeclass @c@.
  liftOpN :: (forall a. c a => FunN n a a) -> FunN n (f p) (f p)

-- | Metadata
instance GOpN c f => GOpN c (M1 i d f) where
  liftOpN f = dimap unM1 M1 (liftOpN @c f)

-- | Product of fields
instance (GOpN c f, GOpN c g) => GOpN c (f :*: g) where
  liftOpN f = liftA2 (:*:) (fstf `lmap` liftOpN @c f)
                           (sndf `lmap` liftOpN @c f)

-- | Absence of fields
instance GOpN c U1 where
  liftOpN _ = pure U1

-- | Field value
instance c a => GOpN c (K1 i a) where
  liftOpN = dimap unK1 K1

-- | Lift a polymorphic, N-ary operator constrained by a typeclass @c@
-- to work over an arbitrary product type via its 'Generic' instance.
genericOpN ::
  forall c n a.
  GOpN c (Rep a) =>
  Generic a      =>
  KnownNat n     =>
  (forall b. c b => Op n b b) {- ^ polymorphic n-ary operator -} ->
  Op n a a                    {- ^ lifted n-ary operator      -}
genericOpN f =
  curryN @n @a @a $ \xs ->
    dimap from to
      (liftOpN @c (FunN (uncurryN (f @z) :: forall z. c z => V n z -> z)))
    $$ xs

------------------------------------------------------------------------

-- | Selector for first component of '(:*:)'.
fstf :: (f :*: g) p -> f p
fstf (x :*: _) = x

-- | Selector for second component of '(:*:)'.
sndf :: (f :*: g) p -> g p
sndf (_ :*: y) = y

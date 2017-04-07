{-# Language
     TypeFamilies, GADTs, DataKinds, ConstraintKinds, RankNTypes,
     TypeOperators, ScopedTypeVariables, KindSignatures, InstanceSigs,
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

  -- * N-ary functions
  , FunN(..)
  , Op

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

-- | N-ary function taking @n@ arguments of type @a@ to produce @b@.
newtype FunN n a b = FunN { runFunN :: Op n a b }

instance KnownNat n => Profunctor (FunN n) where
  dimap :: forall a b c d. (a -> b) -> (c -> d) -> FunN n b c -> FunN n a d
  dimap ab cd (FunN bc) = FunN (go (knownNat @n) bc)
    where
      go :: NatVal m -> Op m b c -> Op m a d
      go IsZ     x = cd x
      go (IsS m) x = go m . x . ab

-- | /Reader/-like behavior
instance KnownNat n => Functor (FunN n e) where
  fmap = liftA

-- | /Reader/-like behavior
instance KnownNat n => Applicative (FunN n e) where
  pure :: forall a. a -> FunN n e a
  pure x = FunN (go (knownNat @n))
    where
      go :: NatVal m -> Op m e a
      go IsZ     = x
      go (IsS m) = \_ -> go m

  (<*>) :: forall a b. FunN n e (a -> b) -> FunN n e a -> FunN n e b
  FunN ff <*> FunN fx = FunN (go (knownNat @n) ff fx)
    where
      go :: NatVal m -> Op m e (a -> b) -> Op m e a -> Op m e b
      go IsZ     = id
      go (IsS m) = liftA2 (go m)

------------------------------------------------------------------------

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
  liftOpN :: KnownNat n => (forall a. c a => FunN n a a) -> FunN n (f p) (f p)

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
  runFunN @n @a @a
    $ dimap from to
    $ liftOpN @c (FunN (f @z) :: forall z. c z => FunN n z z)

------------------------------------------------------------------------

-- | Selector for first component of '(:*:)'.
fstf :: (f :*: g) p -> f p
fstf (x :*: _) = x

-- | Selector for second component of '(:*:)'.
sndf :: (f :*: g) p -> g p
sndf (_ :*: y) = y

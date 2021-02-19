{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- This is an experimental attempt at modularizing apart the use of multiple different instances of the same class for the same type.
-- The basic idea is to associate each instance with a value of a type, so that it can be parameterized in a relatively easy way.
module MultiInstances where

import HaskellPlus
import GHC.Exts (Constraint)

--class MultiInstance (c :: k -> Constraint) (p :: *) (t :: k) where

class TestClass a b where
	f :: a -> b

class SOClass (c :: k -> Constraint) t where

instance SOClass (TestClass Int) String where

instance SOClass (FlippedBifunctor TestClass String) Int where



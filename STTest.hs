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
-- Existential second-order unification (with instantiation set results, performing batch unification (multiple unifiers and equations at once))
module STTest where

import HaskellPlus
import Data.Maybe
import Control.Monad.State
import Control.Monad.Morph
import Control.Monad.ST
import Data.Tuple
import Debug.Trace

data MyTypeS s = FooS s | BarS [s]

weirds :: MyTypeS s -> [MyTypeS s]
weirds (FooS x) = [FooS x, BarS [x,x]]
weirds (BarS []) = [BarS []]
weirds (BarS (x:xs)) = [BarS (x:xs), BarS (x:x:xs)]

unstlist :: ST s [MyTypeS s] -> [ST s (MyTypeS s)]
unstlist stl = do {l <- stl; case l of {[] -> return (

newtype MyTypeBad = MyTypeBad {fromMTB :: forall s. ST s (MyTypeS s)}

weirdbad :: MyTypeBad -> [MyTypeBad]
weirdbad (MyTypeBad mts) = undefined -- Cannot extract the list structure from the ST s.

data MyType = Foo (forall s. ST s s) | Bar (forall s. ST s [s])
data MyTypeF = FooF | BarF

getf :: MyType -> MyTypeF
getf (Foo _) = FooF
getf (Bar _) = BarF

getfs :: MyTypeS s -> MyTypeF
getfs (FooS _) = FooF
getfs (BarS _) = BarF

magic :: (forall s. ST s (MyTypeS s)) -> MyType
magic stmts = case f of {FooF -> Foo (do {FooS x <- stmts; return x}); BarF -> Bar (do {BarS x <- stmts; return x})}
	where
		f = runST (do
		{
			mts <- stmts;
			return (case mts of {FooS _ -> FooF; BarS _ -> BarF})
		})

unmagic :: MyType -> (forall s. ST s (MyTypeS s))
unmagic mt = case mt of
	{
		Foo x -> do {rx <- x; return (FooS rx)};
		Bar x -> do {rx <- x; return (BarS rx)}
	}

weird :: MyType -> [MyType]
weird (Foo stx) = do 

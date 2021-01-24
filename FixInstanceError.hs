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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
module FixInstanceError where

data WeirdFix (f :: * -> *) v = WeirdFixBase v | WeirdFixRec (f (WeirdFix f v))

instance (Eq v, Eq (f (WeirdFix f v))) => Eq (WeirdFix f v) where
	WeirdFixBase v1 == WeirdFixBase v2 = v1 == v2
	WeirdFixRec f1 == WeirdFixRec f2 = f1 == f2
	_ == _ = False

data SimpleThing t = SimpleThing t

instance Eq t => Eq (SimpleThing t) where
	SimpleThing x == SimpleThing y = x == y

letstestit :: WeirdFix SimpleThing Int -> Bool
letstestit wf = wf == wf

data SimpleThing2 t = SimpleThing2Base | SimpleThing2Rec t

instance Eq t => Eq (SimpleThing2 t) where
	SimpleThing2Base == SimpleThing2Base = True
	SimpleThing2Rec x == SimpleThing2Rec y = x == y
	_ == _ = False

letstestit2 :: WeirdFix SimpleThing2 Int -> Bool
letstestit2 wf = wf == wf

data ComplexThing a f = ComplexThingBase | ComplexThingRec a [f]

instance (Eq a, Eq f) => Eq (ComplexThing a f) where
	ComplexThingBase == ComplexThingBase = True
	ComplexThingRec h1 ts1 == ComplexThingRec h2 ts2 = (h1 == h2) && (ts1 == ts2)
	_ == _ = False

letstestit3 :: WeirdFix (ComplexThing Int) Int -> Bool
letstestit3 wf = wf == wf

data SuperSimpleThing = SuperSimpleThing Int Int deriving (Eq, Ord)

data SuperSimpleThing2 = SuperSimpleThing2 Int Int deriving (Eq, Ord)

letstestit4 :: WeirdFix (ComplexThing SuperSimpleThing) SuperSimpleThing2 -> Bool
letstestit4 wf = wf == wf

letstestit5 :: WeirdFix (ComplexThing SuperSimpleThing2) SuperSimpleThing -> Bool
letstestit5 wf = wf == wf




class MultiClass a b | a -> b where
	foo :: a -> b

data WithParams a b = WithParams a b

data WithoutParams a b = WithoutParams

instance MultiClass (WithoutParams a b) (WithParams a b) where
	foo _ = WithParams undefined undefined

poking :: MultiClass a b => [a] -> b
poking [] = undefined
poking (x:_) = foo x

pokingmore :: WithParams (IO Int) ([IO [[Char]]])
pokingmore = poking [WithoutParams,WithoutParams]

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
module AnswerSetTest where

import HaskellPlus
import EnumProc
import AnswerSet

data Mults = Mults Int | MCM Mults Mults deriving Show

instance Implicit Mults Int where
	checkImplicit (Mults n) m = (mod m n) == 0
	checkImplicit (MCM a b) m = (checkImplicit a m) && (checkImplicit b m)
	enumImplicit (Mults n) = n --> (fmap (n+) (enumImplicit (Mults n)))
	enumImplicit (MCM a b) = efilter (checkImplicit a) (enumImplicit b)

data Times = Times Int deriving Show

instance Functional Times Int (AnswerSet Mults Int) where
	tofun (Times n) m = SingleAS (n*m)

instance ImplicitF Mults Int Mults Int Times where	
	composeImplicit (Mults n) (Times m) = ImplicitAS (Mults (n*m))
	composeImplicit (MCM a b) (Times m) = ImplicitAS (MCM xa xb) where (ImplicitAS xa) = composeImplicit a (Times m); (ImplicitAS xb) = composeImplicit b (Times m)


-- An example of why implicits are useful.

-- m4n6 are multiples of the minimum common multiple of 4 and 6. That is, multiples of twelve.
m4n6 :: Mults
m4n6 = MCM (Mults 4) (Mults 6)

-- m4n6t10 is the implicit multiplication of this set by 10.
m4n6t10 :: AnswerSet Mults Int
m4n6t10 = (ImplicitAS m4n6) ?>>= (Times 10)

-- m4n6t10alt is the explicit multiplication of the same set by 10.
m4n6t10alt :: AnswerSet Mults Int
m4n6t10alt = (ImplicitAS m4n6) >>= (return . (*10))

-- Both answer sets are equal. Check it by printing them.


-- This element is in them:
x :: Int
x = 120*9999

-- And while checking this is instantaneous for the implicit answer set:
testimplicit :: IO ()
testimplicit = print (checkAS m4n6t10 x)

-- It takes almost forever for the explicit answer set:
testexplicit :: IO ()
testexplicit = print (checkAS m4n6t10alt x)

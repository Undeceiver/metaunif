{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
module ExistentialTest where

class Class1 a b where
	foo :: a -> b

instance {-# INCOHERENT #-} Monoid a => Class1 a (Either b a) where
	foo x = Right (x <> x)

instance {-# INCOHERENT #-} Monoid a => Class1 a (Either a b) where
	foo x = Left x

class Class2 a where
	foo2 :: a

instance Class2 b => Class1 a (Either a b) where
	foo x = foo2



data Bar a = Dir a | forall b. Class1 b a => FromB b

getA :: Bar a -> a
getA (Dir a) = a
getA (FromB b) = foo b

createBar :: Bar (Either String t)
createBar = FromB "abc"

createBar2 :: Bar (Either t String)
createBar2 = FromB "def"

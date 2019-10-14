{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module WeirdFunDeps where

class Class1 a b | a -> b where
	fun1 :: a -> b

instance Class1 [a] [a] where
	fun1 = id

class Class1 a b => Class2 a b c | b -> c where
	fun2 :: a -> (b,c)

instance Class1 a Int => Class2 a Int Int where
	fun2 x = (fun1 x, fun1 x)

instance Class1 Char Char where
	fun1 = id

instance Class2 Char Char Char where
	fun2 x = (x,x)

instance (Class2 a b c, Class1 [a] [b]) => Class2 [a] [b] [c] where
	fun2 l = unzip (map fun2 l)

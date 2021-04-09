{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
module HiddenTypeVariable where

import HaskellPlus

class Class1 a b | b -> a where
	fun1 :: b -> a

class Class3 a b where
	fun7 :: b -> a

class Class1 (Class1FamRes b) b => Class1Fam b where
	type Class1FamRes b
	fun1fam :: b -> Class1FamRes b
	fun1fam = fun1

fun5 :: forall a b c. ((Class1 a b, Class1 b c) => c -> a)
fun5 = fun1 . fun1

fun6 :: (Class1 a b, Class1 b c, Show b) => c -> a
fun6 = fun1 . fun1

--fun8 :: (Class3 a b, Class3 b c) => c -> a
--fun8 = fun7 . fun7


instance Class1 Int String where
	fun1 x = 5

instance Class1Fam String where
	type Class1FamRes String = Int

instance Class1 Bool Int where
	fun1 x = True

instance Class1Fam Int where
	type Class1FamRes Int = Bool

fun2 :: (Class1Fam a, Class1Fam (Class1FamRes a)) => a -> Class1FamRes (Class1FamRes a)
fun2 = fun1 . fun1

class Class2 a c | c -> a where
	fun4 :: c -> a

newtype Class2FamW a = Class2FamW {fromW :: Class1FamRes (Class1FamRes a)}

instance (Class1Fam a, Class1Fam (Class1FamRes a)) => Class2 (Class2FamW a) a where
	fun4 = Class2FamW . fun1 . fun1

class Class2Fam a where
	type Class2FamRes a
	--type Class2FamRes a = Class1FamRes (Class1FamRes a)
	fun3 :: a -> Class2FamRes a

instance (Class1Fam a, Class1Fam (Class1FamRes a)) => Class2Fam a where
	type Class2FamRes a = Class1FamRes (Class1FamRes a)
	fun3 = fun1 . fun1




type TypeClass1 a b = b -> a

data Fun9Cstrs a b c = Fun9Cstrs {fun9_typeclass1ab :: TypeClass1 a b, fun9_typeclass1bc :: TypeClass1 b c}

fun9 :: Fun9Cstrs a b c -> c -> a
fun9 fun9cstrs c = fun9cstrs £ fun9_typeclass1ab $ fun9cstrs £ fun9_typeclass1bc $ c

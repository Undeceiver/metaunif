{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- Important note: By answer set here we really refer to what in databases is usually thought of as a "result set". It is not trivially the same thing as answer sets in answer set programming. We chose not to change this name because result set would not be that much more clear and it would imply changing a large amount of stuff.
module AnswerSet where

import HaskellPlus
import EnumProc

class Implicit (s :: *) (t :: *) | s -> t where
	checkImplicit :: s -> t -> Bool
	enumImplicit :: s -> EnumProc t

class (Implicit sa a, Implicit sb b, Functional f a (AnswerSet sb b)) => ImplicitF (sa :: *) (a :: *) (sb :: *) (b :: *) (f :: *) | f sa -> sb, f a -> b where
	composeImplicit :: sa -> f -> AnswerSet sb b

-- Any functional can be "composed implicitly" by doing it absolutely explicitly. This is the most inefficient thing to do, but it can always be done. Only use when no more clever thing can be done.
composeImplicitDefault :: (Implicit sa a, Functional f a (AnswerSet sb b)) => sa -> f -> AnswerSet sb b
composeImplicitDefault sa f = (explicitAS (enumImplicit sa)) >>= (tofun f)

-- The third constructor should only appear when there is an instance Implicit s a.
data AnswerSet s a = SingleAS a | ExplicitAS (EnumProc (AnswerSet s a)) | Implicit s a => ImplicitAS s

emptyAS :: AnswerSet s a
emptyAS = ExplicitAS Empty

-- Make the answer set explicit, and therefore the implicit structure type becomes irrelevant. Useful when we need to convert types for when we know there are no more implicit things we can usefully do with it.
makeExplicit :: AnswerSet s1 a -> AnswerSet s2 a
makeExplicit (SingleAS a) = SingleAS a
makeExplicit (ExplicitAS en) = ExplicitAS (fmap makeExplicit en)
makeExplicit (ImplicitAS s) = ExplicitAS (fmap SingleAS (enumImplicit s))

checkAS :: Eq a => AnswerSet s a -> a -> Bool
checkAS (SingleAS a1) a2 | a1 == a2 = True
checkAS (SingleAS a1) a2 = False
checkAS (ExplicitAS en) a = or (fmap (\x -> checkAS x a) en)
checkAS (ImplicitAS s) a = checkImplicit s a

-- Don't use this if you can do things with checkAS: This is necessarily explicit and therefore slower in general
checkPAS :: (a -> a -> Bool) -> AnswerSet s a -> a -> Bool
checkPAS p as a = uns_produce_next (eany (\a2 -> return (p a a2)) (enumAS as))

enumAS :: AnswerSet s a -> EnumProc a
enumAS (SingleAS a) = a --> Empty
enumAS (ExplicitAS en) = es_econcat (fmap enumAS en)
enumAS (ImplicitAS s) = enumImplicit s

explicitAS :: EnumProc a -> AnswerSet s a
explicitAS en = ExplicitAS (fmap SingleAS en)

(?>>=) :: (ImplicitF sa a sb b f, Functional f a (AnswerSet sb b)) => AnswerSet sa a -> f -> AnswerSet sb b
(SingleAS x) ?>>= f = tofun f x
(ExplicitAS en) ?>>= f = ExplicitAS (fmap (?>>= f) en)
(ImplicitAS s) ?>>= f = composeImplicit s f

instance Functor (AnswerSet s) where
	fmap f (SingleAS x) = SingleAS (f x)
	fmap f (ExplicitAS en) = ExplicitAS (fmap (fmap f) en)
	-- This is where the ugly happens, so don't use fmap if you can use implicit composition.
	fmap f (ImplicitAS s) = ExplicitAS (fmap (SingleAS . f) (enumImplicit s))

instance Applicative (AnswerSet s) where
	pure x = SingleAS x
	(SingleAS f) <*> xs = fmap f xs
	(ExplicitAS en) <*> xs = ExplicitAS (fmap (<*> xs) en)
	(ImplicitAS s) <*> xs = ExplicitAS (fmap (\f -> fmap f xs) (enumImplicit s))

instance Monad (AnswerSet s) where
	return x = SingleAS x
	(SingleAS x) >>= f = f x
	(ExplicitAS en) >>= f = ExplicitAS (fmap (>>= f) en)
	(ImplicitAS s) >>= f = (ExplicitAS (fmap SingleAS (enumImplicit s))) >>= f

instance Foldable (AnswerSet s) where
	foldr f e as = foldr f e (enumAS as)

-- Invertible relations are always implicitly composable.
data Invertible sa sb a b = Invertible {fun :: a -> AnswerSet sb b, inv :: b -> AnswerSet sa a, dom :: AnswerSet sa a, rg :: AnswerSet sb b}

invert :: Invertible sa sb a b -> Invertible sb sa b a
invert (Invertible fun inv dom rg) = Invertible inv fun rg dom

instance Functional (Invertible sa sb a b) a (AnswerSet sb b) where
	tofun (Invertible fun inv dom rg) = fun

instance Functional (Invertible sa sb a b) b (AnswerSet sa a) where
	tofun (Invertible fun inv dom rg) = inv

-- This is really an application, but that name would be even more confusing. It's an application using the invertible type.
data Inversion sa sb a b = Inversion (Invertible sa sb a b) (AnswerSet sa a)

enum_inversion :: (Implicit sa a, Eq a, Eq b) => Inversion sa sb a b -> AnswerSet (Inversion sa sb a b) b
enum_inversion (Inversion f a) = a ?>>= f

instance (Implicit sa a, Functional (Invertible sa sb a b) a (AnswerSet (Inversion sa sb a b) b), Eq a, Eq b) => Implicit (Inversion sa sb a b) b where
	checkImplicit (Inversion f a) b = if (checkAS (rg f) b) then (any (\x -> (checkAS a x)) (inv f b)) else False
	enumImplicit (Inversion f a) = (enumAS a) >>= (\x -> enumAS (fun f x))

instance (Implicit sa a, Functional (Invertible sa sb a b) a (AnswerSet (Inversion sa sb a b) b), Eq a, Eq b) => ImplicitF sa a (Inversion sa sb a b) b (Invertible sa sb a b) where
	composeImplicit sa f = ImplicitAS (Inversion f (ImplicitAS sa))

instance (Implicit sa a, Eq a, Eq b) => Functional (Invertible sa sb a b) a (AnswerSet (Inversion sa sb a b) b) where
	tofun f a = enum_inversion (Inversion f (SingleAS a))



-- Similarly, making a tuple is always implicitly composable (independent answer sets).
instance (Implicit sa a, Implicit sb b, Eq a, Eq b) => Implicit (AnswerSet sa a, AnswerSet sb b) (a,b) where
	checkImplicit (asa,asb) (a,b) = (checkAS asa a) && (checkAS asb b)
	enumImplicit (asa,asb) = (enumAS asa) >>= (\x -> (enumAS asb) >>= (\y -> ((x,y) --> Empty)))

-- Because this makes the type "grow", it is highly recommended that it is only used to construct, meaning that the implicit type can be left as a wildcard and then simply enumAS or checkAS are used on the final result. Otherwise, use with care.
tupleAS :: (Implicit sa a, Implicit sb b, Eq a, Eq b) => AnswerSet sa a -> AnswerSet sb b -> AnswerSet (AnswerSet sa a, AnswerSet sb b) (a,b)
tupleAS asa asb = ImplicitAS (asa,asb)


-- An answer set of implicit solutions is also an implicit solution. But, if enumeration is infinite for the set of implicit solutions, then even checking for the set of combined solutions could be non-terminating.
instance (Implicit sa a, Eq a) => Implicit (AnswerSet ssa sa) a where
	checkImplicit as a = uns_produce_next (as_checkImplicit as a)
	enumImplicit as = (enumAS as) >>= enumImplicit

as_checkImplicit :: (Implicit sa a, Eq a) => AnswerSet ssa sa -> a -> EnumProc Bool
as_checkImplicit (SingleAS imp) a = (checkImplicit imp a) --> Empty
as_checkImplicit (ExplicitAS en) a = eany (\imp -> as_checkImplicit imp a) en
as_checkImplicit (ImplicitAS iimp) a = eany (\imp -> (checkImplicit imp a) --> Empty) (enumImplicit iimp)

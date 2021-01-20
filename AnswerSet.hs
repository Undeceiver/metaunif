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
{-# LANGUAGE ConstraintKinds #-}
-- Important note: By answer set here we really refer to what in databases is usually thought of as a "result set". It is not trivially the same thing as answer sets in answer set programming. We chose not to change this name because result set would not be that much more clear and it would imply changing a large amount of stuff.
module AnswerSet where

import HaskellPlus
import EnumProc
import Algorithm
import Data.Bifunctor
import Debug.Trace

class Implicit (s :: *) (t :: *) | s -> t where
	checkImplicit :: s -> t -> Computation Bool
	enumImplicit :: s -> Computation t

diagEnumImplicit :: Implicit s t => s -> EnumProc t
diagEnumImplicit s = (enumImplicit s) \$ ()

class ImplicitF (sa :: *) (sb :: *) (b :: *) (f :: *) | f sa -> sb where
	composeImplicit :: sa -> f -> AnswerSet sb b

type FullImplicitF sa a sb b f = (Implicit sa a, Implicit sb b, Functional f a (AnswerSet sb b), ImplicitF sa sb b f)

-- Any functional can be "composed implicitly" by doing it absolutely explicitly. This is the most inefficient thing to do, but it can always be done. Only use when no more clever thing can be done.
composeImplicitDefault :: (Implicit sa a, Functional f a (AnswerSet sb b)) => sa -> f -> AnswerSet sb b
composeImplicitDefault sa f = (explicitAS (diagEnumImplicit sa)) >>= (tofun f)

-- The third constructor should only appear when there is an instance Implicit s a.
data AnswerSet s a = SingleAS a | ExplicitAS (EnumProc (AnswerSet s a)) | Implicit s a => ImplicitAS s

emptyAS :: AnswerSet s a
emptyAS = ExplicitAS Empty

-- Checks if the AnswerSet is obviously empty. It may still be empty depending on the implicit representation, but this function only checks if it can be said to be empty regardless of the implicit checking.
nullAS :: AnswerSet s a -> Bool
nullAS (SingleAS _) = False
nullAS (ExplicitAS en) = all nullAS en
nullAS (ImplicitAS _) = False

-- Make the answer set explicit, and therefore the implicit structure type becomes irrelevant. Useful when we need to convert types for when we know there are no more implicit things we can usefully do with it.
makeExplicit :: ExecOrder t => t -> AnswerSet s1 a -> AnswerSet s2 a
makeExplicit _ (SingleAS a) = SingleAS a
makeExplicit t (ExplicitAS en) = ExplicitAS (fmap (makeExplicit t) en)
makeExplicit t (ImplicitAS s) = ExplicitAS (fmap SingleAS (runcomp t (enumImplicit s)))

checkAS :: Eq a => AnswerSet s a -> a -> Computation Bool
checkAS (SingleAS a1) a2 | a1 == a2 = comp True
checkAS (SingleAS a1) a2 = comp False
checkAS (ExplicitAS en) a = compor ((cunfactor (\x -> checkAS x a)) ... (ecomp en))
checkAS (ImplicitAS s) a = checkImplicit s a

-- Don't use this if you can do things with checkAS: This is necessarily explicit and therefore slower in general
checkPAS :: (a -> Bool) -> AnswerSet s a -> Bool
checkPAS p as = uns_produce_next (eany (\a -> return (p a)) (diagEnumAS as))

enumAS :: AnswerSet s a -> Computation a
enumAS (SingleAS a) = comp a
-- This below incurs in infinite recursion when we have infinitely nested answer sets!
--enumAS (ExplicitAS en) = (algcomp . ecomp) (fmap enumAS en)
enumAS (ExplicitAS en) = (cunfactor enumAS) ... (ecomp en)
enumAS (ImplicitAS s) = enumImplicit s

diagEnumAS :: AnswerSet s a -> EnumProc a
diagEnumAS as = (enumAS as) \$ ()

implicitOnly :: AnswerSet s a -> Computation s
implicitOnly (SingleAS a) = error "The answer set contains explicit answers!"
-- This below incurs in infinite recursion when we have infinitely nested answer sets!
--implicitOnly (ExplicitAS en) = (algcomp . ecomp) (fmap implicitOnly en)
implicitOnly (ExplicitAS en) = (cunfactor implicitOnly) ... (ecomp en)
implicitOnly (ImplicitAS s) = comp s

explicitAS :: EnumProc a -> AnswerSet s a
explicitAS en = ExplicitAS (fmap SingleAS en)

(?>>=) :: FullImplicitF sa a sb b f => AnswerSet sa a -> f -> AnswerSet sb b
(SingleAS x) ?>>= f = tofun f x
(ExplicitAS en) ?>>= f = ExplicitAS (fmap (?>>= f) en)
(ImplicitAS s) ?>>= f = composeImplicit s f
infixl 7 ?>>=

-- Note that the Bifunctor instance is naive in that it considers the effects of the function on implicits and the function on explicits independent.
-- That is, the function on explicits will never be applied when the elements are expressed implicitly.
-- In other words, it should be true that, for functions f (on implicits) and g (on explicits), it should be true that ((enumAS (bimap f g as)) == (enumAS (fmap g as)))
-- It is a much simpler and less flexible version of implicit composition.

-- Also, because Bifunctor cannot include constraints on the functions, we need to use our own version instead of actual Bifunctor.
--instance Bifunctor AnswerSet where
bimap_as :: Implicit b d => (a -> b) -> (c -> d) -> AnswerSet a c -> AnswerSet b d
bimap_as f g (SingleAS x) = SingleAS (g x)
bimap_as f g (ExplicitAS en) = ExplicitAS ((bimap_as f g) <$> en)
bimap_as f g (ImplicitAS s) = ImplicitAS (f s)

instance Functor (AnswerSet s) where
	fmap f (SingleAS x) = SingleAS (f x)
	fmap f (ExplicitAS en) = ExplicitAS (fmap (fmap f) en)
	-- This is where the ugly happens, so don't use fmap if you can use implicit composition.
	fmap f (ImplicitAS s) = ExplicitAS (fmap (SingleAS . f) (diagEnumImplicit s))

instance Applicative (AnswerSet s) where
	pure x = SingleAS x
	(SingleAS f) <*> xs = fmap f xs
	(ExplicitAS en) <*> xs = ExplicitAS (fmap (<*> xs) en)
	(ImplicitAS s) <*> xs = ExplicitAS (fmap (\f -> fmap f xs) (diagEnumImplicit s))

instance Monad (AnswerSet s) where
	return x = SingleAS x
	(SingleAS x) >>= f = f x
	(ExplicitAS en) >>= f = ExplicitAS (fmap (>>= f) en)
	(ImplicitAS s) >>= f = (ExplicitAS (fmap SingleAS (diagEnumImplicit s))) >>= f

-- We really should not need this instance for now.
--instance Foldable (AnswerSet s) where
--	foldr f e as = foldr f e (enumAS as)

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
	checkImplicit (Inversion f a) b = do
		{
			inrg <- checkAS (rg f) b;
			if inrg then do
			{
				let {invs = enumAS (inv f b); ch = cunfactor (checkAS a)};
				company ch invs
			}
			else (return False)
		}
	enumImplicit (Inversion f a) = (enumAS a) >>= (\x -> enumAS (fun f x))

instance (Implicit sa a, Eq a, Eq b) => ImplicitF sa (Inversion sa sb a b) b (Invertible sa sb a b) where
	composeImplicit sa f = ImplicitAS (Inversion f (ImplicitAS sa))

instance (Implicit sa a, Eq a, Eq b) => Functional (Invertible sa sb a b) a (AnswerSet (Inversion sa sb a b) b) where
	tofun f a = enum_inversion (Inversion f (SingleAS a))



-- Similarly, making a tuple is always implicitly composable (independent answer sets).
instance (Implicit sa a, Implicit sb b, Eq a, Eq b) => Implicit (AnswerSet sa a, AnswerSet sb b) (a,b) where
	checkImplicit (asa,asb) (a,b) = do {cha <- checkAS asa a; chb <- checkAS asb b; return (cha && chb)}
	enumImplicit (asa,asb) = (enumAS asa) >>= (\x -> (enumAS asb) >>= (\y -> (comp (x,y))))

-- Because this makes the type "grow", it is highly recommended that it is only used to construct, meaning that the implicit type can be left as a wildcard and then simply enumAS or checkAS are used on the final result. Otherwise, use with care.
tupleAS :: (Implicit sa a, Implicit sb b, Eq a, Eq b) => AnswerSet sa a -> AnswerSet sb b -> AnswerSet (AnswerSet sa a, AnswerSet sb b) (a,b)
tupleAS asa asb = ImplicitAS (asa,asb)


-- An answer set of implicit solutions is also an implicit solution. But, if enumeration is infinite for the set of implicit solutions, then even checking for the set of combined solutions could be non-terminating.
instance (Implicit sa a, Eq a) => Implicit (AnswerSet ssa sa) a where
	checkImplicit (SingleAS imp) a = checkImplicit imp a
	checkImplicit (ExplicitAS en) a = company (cunfactor (\imp -> checkImplicit imp a)) (ecomp en)
	checkImplicit (ImplicitAS iimp) a = company (cunfactor (\imp -> checkImplicit imp a)) (enumImplicit iimp)
	enumImplicit as = (enumAS as) >>= enumImplicit

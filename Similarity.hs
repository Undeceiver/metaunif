{-# LANGUAGE DeriveGeneric #-}
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
module Similarity where

import HaskellPlus
import Control.Monad.Except
import Analogous
import Equiv
import Algorithm
import EnumProc
import Data.Either
import GHC.Generics (Generic)
import Data.Hashable

class Functor t => Similarity t where
	similarities :: (Hashable a, Ord a, Hashable b, Ord b) => t a -> t b -> Computation (Equiv (Either a b))

-- Replaces the elements with their equivalence class.
similarities_as_structure :: (Hashable a, Ord a, Hashable b, Ord b, Similarity t) => Equiv (Either a b) -> t a -> t [Either a b]
similarities_as_structure eq t = get_equiv_class eq <$> (Left <$> t)

instructure_similarities :: (Similarity t, Hashable a, Ord a, Hashable b, Ord b) => t a -> t b -> Computation (t [Either a b])
instructure_similarities ta tb = similarities ta tb >>= (\eq -> return (similarities_as_structure eq ta))

-- The index indicates from which structure the value came.
-- Note that this assumes conjunctive associativity of similarities, by doing all similarities with the first element, and then just combining them (satisfying all equivalences at the same time).
multisimilarities :: (Similarity t, Hashable a, Ord a) => [t a] -> Computation (Equiv (Int,a))
multisimilarities [] = comp mempty
multisimilarities (t:[]) = comp mempty
multisimilarities (t:ts) = foldM (\eq1 -> \ceq2 -> ceq2 >>= (return . (<> eq1))) empty_equiv allsimsidxs
	where
		allsims = similarities t <$> ts;
		fis = (\idx -> (alg (\aallsims -> from_equiv_classes (fmap (fmap (\either -> case either of {Left x -> (0,x); Right y -> (idx+1,y)})) (get_equiv_classes aallsims)))) ... (allsims !! idx));
		allsimsidxs = fis <$> [0..((length allsims) - 1)];

multisimilarities_as_structure :: (Similarity t, Hashable a, Ord a) => Equiv (Int, a) -> Int -> t a -> t [(Int, a)]
multisimilarities_as_structure eq idx t = get_equiv_class eq <$> ((idx,) <$> t)

instructure_multisimilarities :: (Similarity t, Hashable a, Ord a) => [t a] -> Computation (t [(Int, a)])
instructure_multisimilarities [] = emptycomp
instructure_multisimilarities (ta:tas) = multisimilarities (ta:tas) >>= (\eq -> return (multisimilarities_as_structure eq 0 ta))

-- Note that this blends together all the a's in the left and all the b's in the left, as any other similarity probably would. This one is for certain, though, so if any a appears on several s's on the left, they are all considered the same, and the same for the b's. This is actually useful in most practical cases, though.
-- It's like merging namespaces for variables.	
composite_similarities :: (Similarity t, Similarity s, Hashable a, Ord a, Hashable b, Ord b, Hashable (s a), Ord (s a), Hashable (s b), Ord (s b)) => t (s a) -> t (s b) -> Computation (Equiv (Either a b))
composite_similarities tsa tsb = simss >>= composite_similarities_fromequiv
	where
		simss = similarities tsa tsb;

composite_similarities_fromequiv :: (Similarity s, Hashable a, Ord a, Hashable b, Ord b, Hashable (s a), Ord (s a), Hashable (s b), Ord (s b)) => Equiv (Either (s a) (s b)) -> Computation (Equiv (Either a b))
composite_similarities_fromequiv eq = concatequivs
	where
		cs = get_equiv_classes eq;
		cequivs = traverse composite_similarities_fromequiv_class cs;
		concatequivs = mconcat <$> cequivs;
		
composite_similarities_fromequiv_class :: (Similarity s, Hashable a, Ord a, Hashable b, Ord b) => [Either (s a) (s b)] -> Computation (Equiv (Either a b))
composite_similarities_fromequiv_class c = case ls of
	{
		(hl:tls) -> case rs of
		{
			(hr:trs) -> do {vxsimt <- similarities hl hr; vlsimst <- lsimst; vrsimst <- rsimst; return (vxsimt <> vlsimst <> vrsimst)};
			[] -> rsimst
		};
		[] -> case rs of
		{
			(hr:trs) -> lsimst;
			[] -> comp empty_equiv
		}
	}
	where
		ls = fmap (fromLeftErr "composite_similarities_fromequiv: Left: Shouldn't happen") (Prelude.filter isLeft c);
		rs = fmap (fromRightErr "composite_similarities_fromequiv: Right: Shouldn't happen") (Prelude.filter isRight c);
		lsims = multisimilarities ls;
		rsims = multisimilarities rs;
		lsimst = fmap (fmap_equiv (Left . snd)) lsims;
		rsimst = fmap (fmap_equiv (Right . snd)) rsims;
		


-- Lists have different ways to consider their similarities, so we use wrappers to identify which one we are using.
newtype PosSimilarList a = PosSimilarList {fromPosSimilarList :: [a]} deriving (Eq, Ord, Functor, Foldable, Traversable, Generic)

instance Hashable a => Hashable (PosSimilarList a)

instance Similarity PosSimilarList where
	similarities (PosSimilarList l1) (PosSimilarList l2) = poslistsimilarities l1 l2

poslistsimilarities :: (Hashable a, Ord a, Hashable b, Ord b) => [a] -> [b] -> Computation (Equiv (Either a b))
poslistsimilarities [] [] = comp mempty
poslistsimilarities (a:as) [] = emptycomp
poslistsimilarities [] (b:bs) = emptycomp
poslistsimilarities (a:as) (b:bs) = ((Left a) =:~ (Right b) $) <$> poslistsimilarities as bs

-- Lists as sets, but each element in each list is considered different from the others in the same list.
newtype SetSimilarList a = SetSimilarList {fromSetSimilarList :: [a]} deriving (Eq, Ord, Functor, Foldable, Traversable, Generic)

instance Hashable a => Hashable (SetSimilarList a)

instance Similarity SetSimilarList where
	similarities (SetSimilarList l1) (SetSimilarList l2) = setlistsimilarities l1 l2

setlistsimilarities :: (Hashable a, Ord a, Hashable b, Ord b) => [a] -> [b] -> Computation (Equiv (Either a b))
setlistsimilarities [] [] = comp mempty
setlistsimilarities (a:as) [] = emptycomp
setlistsimilarities [] (b:bs) = emptycomp
setlistsimilarities (a:as) bs = (ecomp . uns_enum_from_list) ((\(rb,rbs) -> (((Left a) =:~ (Right rb) $),rbs)) <$> (setlist_conss bs)) >>= (\(f,rrbs) -> f <$> setlistsimilarities as rrbs)

-- Lists as sets, and now we allow each element in one list to potentially match with multiple on the other list and/or with others on the same list.
-- Note that this may produce repeated similarities. This redundancy, if needed to be removed, should be removed outside, since it is not trivial to remove it inside.
newtype AnySetSimilarList a = AnySetSimilarList {fromAnySetSimilarList :: [a]} deriving (Eq, Ord, Functor, Foldable, Traversable, Generic)

instance Hashable a => Hashable (AnySetSimilarList a)

instance Similarity AnySetSimilarList where
	similarities (AnySetSimilarList l1) (AnySetSimilarList l2) = anysetlistsimilarities l1 l2

anysetlistsimilarities :: (Hashable a, Ord a, Hashable b, Ord b) => [a] -> [b] -> Computation (Equiv (Either a b))
anysetlistsimilarities as bs = anysetlistsimilarities_single ((Left <$> as) ++ (Right <$> bs))

anysetlistsimilarities_single :: (Hashable a, Ord a, Hashable b, Ord b) => [Either a b] -> Computation (Equiv (Either a b))
anysetlistsimilarities_single [] = comp mempty
anysetlistsimilarities_single (x:xs) = (comp mempty) .+. ((algfilter (mb_from_filter (not . is_empty_equiv))) ... ((ecomp . uns_enum_from_list) (id:((\ox -> (x =:~ ox $)) <$> xs)) >>= (\f -> f <$> (anysetlistsimilarities_single xs))))

-- We can build an analogy from a similarity!
similarity_analogy :: (Traversable t, Similarity t, Hashable a, Ord a) => Analogy Computation (t a) (t b) a b -- ~~ ([a] -> Computation b) -> [t a] -> AnalError (Computation (t b))
similarity_analogy f [] = nostructure
similarity_analogy f tas = return ctb
	where
		tcs = instructure_multisimilarities tas;
		tls = fmap (fmap (fmap snd)) tcs;
		ctb = tls >>= (\tl -> traverse f tl)
		


-- Conceptually, the structures are alpha-equivalent if there is at least one branch that produces True.
c_alpha_eq :: (Traversable t, Similarity t, Hashable a, Ord a, Hashable b, Ord b) => t a -> t b -> Computation Bool
c_alpha_eq t1 t2 = (not . fsim) <$> sims
	where
		sims = similarities t1 t2;
		fcl = (\cl -> (length (Prelude.filter isLeft cl) > 1) || (length (Prelude.filter isRight cl) > 1));
		fsim = (\eq -> any fcl (get_equiv_classes eq))

c_alpha_eq_wsim :: (Traversable t, Hashable a, Ord a, Hashable b, Ord b) => (t a -> t b -> Computation (Equiv (Either a b))) -> t a -> t b -> Computation Bool
c_alpha_eq_wsim sim t1 t2 = (not . fsim) <$> sims
	where
		sims = sim t1 t2;
		fcl = (\cl -> (length (Prelude.filter isLeft cl) > 1) || (length (Prelude.filter isRight cl) > 1));
		fsim = (\eq -> any fcl (get_equiv_classes eq))

alpha_eq :: (Traversable t, Similarity t, Hashable a, Ord a, Hashable b, Ord b) => t a -> t b -> Bool
alpha_eq t1 t2 = uns_produce_next (eany (return . id) (c_alpha_eq t1 t2 \$ ()))

alpha_eq_wsim :: (Traversable t, Hashable a, Ord a, Hashable b, Ord b) => (t a -> t b -> Computation (Equiv (Either a b))) -> t a -> t b -> Bool
alpha_eq_wsim sim t1 t2 = uns_produce_next (eany (return . id) (c_alpha_eq_wsim sim t1 t2 \$ ()))

(=@=) :: (Traversable t, Similarity t, Hashable a, Ord a, Hashable b, Ord b) => t a -> t b -> Bool
(=@=) = alpha_eq

infixl 7 =@=

-- Cannot implement this as an actual class, as it would require Equiv to be a Functor, which it can't because of the Ord constraint.
-- This similarity matches the structure of the equivalences. Which means, it associates elements in the left equivalence with elements in the right equivalence, such that equivalences in the left are mapped to equivalences in the right, while distinctness in both sides is also preserved (so equivalence class sets are the same size)
equiv_similarities :: (Hashable a, Ord a, Hashable b, Ord b) => Equiv a -> Equiv b -> Computation (Equiv (Either a b))
equiv_similarities eq1 eq2 = equiv_similarities_classes (get_equiv_classes eq1) (get_equiv_classes eq2)

equiv_similarities_classes :: (Hashable a, Ord a, Hashable b, Ord b) => [[a]] -> [[b]] -> Computation (Equiv (Either a b))
equiv_similarities_classes eqs1 eqs2 = composite_similarities (SetSimilarList (SetSimilarList <$> eqs1)) (SetSimilarList (SetSimilarList <$> eqs2))

-- We can produce an instance for the double list, though
newtype EquivClasses a = EquivClasses {fromEquivClasses :: [[a]]} deriving (Eq, Show, Ord, Generic)

instance Hashable a => Hashable (EquivClasses a)

equivclasses :: (Hashable a, Ord a) => Equiv a -> EquivClasses a
equivclasses x = EquivClasses (get_equiv_classes x)

instance Functor EquivClasses where
	fmap g = EquivClasses . (fmap2 g) . fromEquivClasses

instance Foldable EquivClasses where
	foldr g z (EquivClasses eqs) = homofoldr2 g eqs z

instance Traversable EquivClasses where
	traverse g (EquivClasses eqs) = EquivClasses <$> (traverse2 g eqs)

instance Similarity EquivClasses where
	similarities (EquivClasses eqs1) (EquivClasses eqs2) = equiv_similarities_classes eqs1 eqs2

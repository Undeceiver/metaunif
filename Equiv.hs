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
-- A simple but efficient equivalence class library. This is really union find, except we avoid using monads in a certain way here that make everything complicated (cough, cough)
module Equiv where

import HaskellPlus
import Data.HashMap
import Data.Maybe
import Control.Lens
import Data.Hashable

-- You cannot undo equivalences!
data Equiv t = Equiv (t := t)
--data Equiv t where
--	Equiv :: (Hashable t, Ord t) => t := t -> Equiv t

fromEquiv :: Equiv t -> t := t
fromEquiv (Equiv x) = x

lens_equiv :: Lens' (Equiv t) (t := t)
lens_equiv f (Equiv m) = fmap (\r -> Equiv r) (f m) 

empty_equiv :: Equiv t
empty_equiv = Equiv empty

is_empty_equiv :: Equiv t -> Bool
is_empty_equiv (Equiv m) = Data.HashMap.null m

get_leaf :: (Hashable t, Ord t) => Equiv t -> t -> t
get_leaf eq x | isNothing (eq ^. (lens_equiv . (at x))) = x
get_leaf eq x = get_leaf eq (fromJust (eq ^. (lens_equiv . (at x))))

(!->) :: (Hashable t, Ord t) => Equiv t -> t -> t
(!->) = get_leaf

infixl 7 !->

get_equiv_class :: (Hashable t, Ord t) => Equiv t -> t -> [t]
get_equiv_class eq x = lx:(Prelude.filter (\y -> y =~ lx $ eq) ks)
	where
		lx = eq !-> x;
		ks = keys (fromEquiv eq);

make_equiv :: (Hashable t, Ord t) => Equiv t -> t -> t -> Equiv t
make_equiv eq x y | (eq !-> x) == (eq !-> y) = eq
make_equiv eq x y = (lens_equiv . (at (eq !-> x))) .~ (Just y) $ eq

(=:~) :: (Hashable t, Ord t) => t -> t -> Equiv t -> Equiv t
a =:~ b = (\eq -> make_equiv eq a b)

infixl 7 =:~

is_equiv :: (Hashable t, Ord t) => Equiv t -> t -> t -> Bool
is_equiv eq x y = (eq !-> x) == (eq !-> y)

(=~) :: (Hashable t, Ord t) => t -> t -> Equiv t -> Bool
a =~ b = (\eq -> is_equiv eq a b)

infixl 7 =~

get_equiv_classes :: (Hashable t, Ord t) => Equiv t -> [[t]]
get_equiv_classes eq = get_equiv_classes_rec eq [] (keys (fromEquiv eq))

get_equiv_classes_rec :: (Hashable t, Ord t) => Equiv t -> [[t]] -> [t] -> [[t]]
get_equiv_classes_rec eq ex [] = ex
get_equiv_classes_rec eq ex (x:xs) = get_equiv_classes_rec eq (get_equiv_classes_rec_rec eq ex x lx) xs
	where
		lx = eq !-> x;

get_equiv_classes_rec_rec :: (Hashable t, Ord t) => Equiv t -> [[t]] -> t -> t -> [[t]]
get_equiv_classes_rec_rec eq [] x lx = [[lx,x]]
-- The lists in the result are never empty, and in fact never have less than 2 elements.
get_equiv_classes_rec_rec eq ((ly:ys):yss) x lx | lx == ly = ((ly:x:ys):yss)
get_equiv_classes_rec_rec eq (ys:yss) x lx = ys:(get_equiv_classes_rec_rec eq yss x lx)

from_equiv_classes :: (Hashable t, Ord t) => [[t]] -> Equiv t
from_equiv_classes [] = empty_equiv
from_equiv_classes ([]:tss) = from_equiv_classes tss
from_equiv_classes ((t:[]):tss) = from_equiv_classes tss
from_equiv_classes ((t:ts):tss) = (Prelude.foldr (\ot -> \peq -> ot =:~ t $ peq) empty_equiv ts) <> (from_equiv_classes tss)

instance (Hashable t, Ord t) => Semigroup (Equiv t) where
	eq1 <> eq2 = Prelude.foldr (\(x:xs) -> \peq -> Prelude.foldr (\y -> \peq2 -> x =:~ y $ peq2) peq xs) eq1 cs where cs = get_equiv_classes eq2

instance (Hashable t, Ord t) => Monoid (Equiv t) where
	mempty = empty_equiv

-- We can make Equiv a functor by transforming back and forth from equivalence classes, though this assumes that both source and target are Ord.
fmap_equiv :: (Hashable a, Ord a, Hashable b, Ord b) => (a -> b) -> Equiv a -> Equiv b
fmap_equiv f eq = from_equiv_classes . (fmap (fmap f)) . get_equiv_classes $ eq

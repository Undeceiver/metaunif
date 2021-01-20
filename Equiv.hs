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
import Data.Map.Strict
import Data.Maybe
import Control.Lens

-- You cannot undo equivalences!
data Equiv t = Equiv {fromEquiv :: t := t}

lens_equiv :: Lens' (Equiv t) (t := t)
lens_equiv f (Equiv m) = fmap (\r -> Equiv r) (f m) 

empty_equiv :: Equiv t
empty_equiv = Equiv Empty

get_leaf :: Ord t => Equiv t -> t -> t
get_leaf eq x | isNothing (eq ^. (lens_equiv . (at x))) = x
get_leaf eq x = get_leaf eq (fromJust (eq ^. (lens_equiv . (at x))))

(!->) :: Ord t => Equiv t -> t -> t
(!->) = get_leaf

infixl 7 !->

make_equiv :: Ord t => Equiv t -> t -> t -> Equiv t
make_equiv eq x y = (lens_equiv . (at (eq !-> x))) .~ (Just y) $ eq

(=:~) :: Ord t => t -> t -> Equiv t -> Equiv t
a =:~ b = (\eq -> make_equiv eq a b)

infixl 7 =:~

is_equiv :: Ord t => Equiv t -> t -> t -> Bool
is_equiv eq x y = (eq !-> x) == (eq !-> y)

(=~) :: Ord t => t -> t -> Equiv t -> Bool
a =~ b = (\eq -> is_equiv eq a b)

infixl 7 =~


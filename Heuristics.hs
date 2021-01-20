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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
module Heuristics where

import HaskellPlus
import Control.Monad.State
import Control.Monad.Identity

-- c : Choice type: What is the type of the options that the heuristics chooses from
-- i : Persistent info type: What is the type used to provide **persistent** information that could be relevant for the heuristics.
-- l : Local info type: What is the type used to provide local information when asking the heuristics for a choice.
class Monad m => HeuristicsI (h :: *) (i :: *) (m :: * -> *) | h -> m i where
	heur_inform :: h -> i -> m h

class Monad m => HeuristicsC (h :: *) (l :: *) (c :: *) (m :: * -> *) | h -> m, h c -> l where
	heur_choose :: h -> l -> [c] -> m (Maybe c, h)

class (HeuristicsI h i m, HeuristicsC h l c m) => Heuristics h i l c m where
	-- No methods other than the ones from the two classes above.

data MHeuristic i l c a = MHeuristic {fromMHeuristic :: (forall h m. Heuristics h i l c m => StateT h m a)}

instance Functor (MHeuristic i l c) where
	fmap f (MHeuristic st) = MHeuristic (fmap f st)

instance Applicative (MHeuristic i l c) where
	pure a = MHeuristic (pure a)
	(MHeuristic f) <*> (MHeuristic a) = MHeuristic (f <*> a)

instance Monad (MHeuristic i l c) where
	(MHeuristic sta) >>= f = MHeuristic (do {a <- sta; let {(MHeuristic b) = f a}; b})

m_heur_inform :: i -> MHeuristic i l c ()
m_heur_inform i = MHeuristic (StateT (\h -> do {rh <- heur_inform h i; return ((),rh)}))

m_heur_choose :: l -> [c] -> MHeuristic i l c (Maybe c)
m_heur_choose l cs = MHeuristic (StateT (\h -> heur_choose h l cs))

m_heur_compute :: Heuristics h i l c m => h -> MHeuristic i l c a -> m a
m_heur_compute h (MHeuristic sta) = fst <$> runStateT sta h


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
{-# LANGUAGE TupleSections #-}
module HeuristicsTest where

import HaskellPlus
import Heuristics
import Control.Monad.State
import EnumProc
import Control.Monad.Identity

instance HeuristicsI [Int] Int EnumProc where
	heur_inform ns n = ((n:ns) --> (2*n:ns) --> EnumProc.Empty)

instance HeuristicsC [Int] () Int EnumProc where
	heur_choose ns _ cs = ((,ns) <$> heur_stint_choose cs ns)

instance Heuristics [Int] Int () Int EnumProc where

heur_stint_choose :: [Int] -> [Int] -> EnumProc (Maybe Int)
heur_stint_choose [] _ = EnumProc.Empty
heur_stint_choose cs [] = EnumProc.Empty
heur_stint_choose cs (h:hs) | elem h cs = Just h --> heur_stint_choose cs hs
heur_stint_choose cs (h:hs) = heur_stint_choose cs hs

instance HeuristicsI Int Int Identity where
	heur_inform _ n = Identity n

instance HeuristicsC Int Int Int Identity where
	heur_choose n m cs = if (elem n cs) then (Identity (Just n, n)) else (if (elem m cs) then (Identity (Just m, m)) else (Identity (Nothing, m)))

instance Heuristics Int Int Int Int Identity where




test_mheur_1 :: MHeuristic Int l Int (Maybe Int)
test_mheur_1 = do {m_heur_inform 1; m_heur_inform 2; m_heur_inform 3; m_heur_choose undefined [1,2,3,4,5]}

test_mheur_2 :: MHeuristic Int l Int (Maybe Int)
test_mheur_2 = do {m_heur_inform 1; m_heur_inform 2; m_heur_inform 3; m_heur_choose undefined [1,2,3]}

test_mheur_3 :: MHeuristic Int l Int (Maybe Int)
test_mheur_3 = do {m_heur_inform 1; m_heur_inform 2; m_heur_inform 3; m_heur_choose undefined [1,2]}

test_mheur_4 :: MHeuristic Int l Int (Maybe Int)
test_mheur_4 = do {m_heur_inform 1; m_heur_inform 2; m_heur_inform 3; mb_n <- m_heur_choose undefined [1,2,3]; case mb_n of {Nothing -> return Nothing; Just n -> do {m_heur_inform (3*n); m_heur_choose undefined [3,9,21]}}}

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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
module CESQResolutionProvenance where

import HaskellPlus
import Data.List
import Algorithm
import Provenance

class CQRPElement t where
	cqrp_show :: String -> t -> String

data CQRP = CQRPText String | forall t. CQRPElement t => CQRPEl t | CQRPRec [CQRP] | CQRPSeq [CQRP]

-- This is an abnormal instance, but it is useful.
instance CQRPElement CQRP where
	cqrp_show pre (CQRPText str) = pre ++ str ++ ";\n"
	cqrp_show pre (CQRPEl t) = pre ++ "#\n" ++ (cqrp_show pre t) ++ "#\n"
	cqrp_show pre (CQRPRec cqrps) = pre ++ "{\n" ++ (concat (map (cqrp_show (pre ++ "\t")) cqrps)) ++ "}\n"
	cqrp_show pre (CQRPSeq cqrps) = concat (map (cqrp_show pre) cqrps)

instance Show CQRP where
	show = cqrp_show ""

instance Semigroup CQRP where
	(CQRPSeq cqrps1) <> (CQRPSeq cqrps2) = CQRPSeq (cqrps1 ++ cqrps2)
	(CQRPSeq cqrps1) <> cqrp2 = CQRPSeq (cqrps1 ++ [cqrp2])
	cqrp1 <> (CQRPSeq cqrps2) = CQRPSeq (cqrp1:cqrps2)
	cqrp1 <> cqrp2 = CQRPSeq [cqrp1,cqrp2]

instance Monoid CQRP where
	mempty = CQRPSeq []


-- We introduce a type operator for Algorithms with this provenance, since once the Provenance is known it is a binary operator.
-- Keep in mind that this operator does not say anything about CQRP being the Provenance, but in the context in which this module will be used, it is what is implicitly assumed by the symbolism (and explicitly by the type synonym).
type (a .:-> b) = ProvAlgorithm CQRP a b
infixr 0 .:->


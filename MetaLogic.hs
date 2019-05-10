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
module MetaLogic where

import Control.Exception
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Unification
import Control.Unification.IntVar
import Control.Unification.Types
import Control.Monad.Trans
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Error.Class
import HaskellPlus
import Syntax
import ObjectLogic

newtype MVariable = MVar Int deriving (Eq, Ord)

instance Show MVariable where
	show (MVar x) = "X" ++ (show x)
instance Read MVariable where
	readsPrec _ ('X':xs) = (let r = (head (reads xs))
				in [(MVar (fst r),(snd r))])

instance Variabilizable MVariable where 
	get_var (MVar x) = IntVar x

newtype AMVariable = AMVar Int deriving (Eq, Ord)

instance Show AMVariable where
	show (AMVar x) = "Z" ++ (show x)
instance Read AMVariable where
	readsPrec _ ('Z':xs) = (let r = (head (reads xs))
				in [(AMVar (fst r),(snd r))])

instance Variabilizable AMVariable where 
	get_var (AMVar x) = IntVar x


-- This is NOT what I used to call a meta-term.
type Metaterm = Metawrap MVariable UTerm CTermF OVariable
instance Read Metaterm where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(OVariable,String))
				in [(mw (UVar (fst r)),(snd r))])
	readsPrec _ ('X':xs) = (let r = (head (reads ('X':xs))::(MVariable,String))
				in [(mv (UVar (fst r)),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]))

instance {-# OVERLAPPING #-} Show Metaterm where
	show mx = show_metawrap mx

type Metaatom = PredMetawrap MVariable AMVariable UTerm CAtomPF CTermF OVariable

-- We use X for term meta-variables and Z for atom meta-variables
instance Read Metaatom where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(OVariable,String))
				in [(MTerm (mw (UVar (fst r))),(snd r))])
	readsPrec _ ('X':xs) = (let r = (head (reads ('X':xs))::(MVariable,String))
				in [(MTerm (mv (UVar (fst r))),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(MTerm (UTerm (TFun (fst r) (fst r2))),(snd r2))]))
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs))::(OPredicate,String))
				in (let r2 = read_term_list (snd r)
					in [(MAtom (APred (fst r) (fst r2)),(snd r2))]))
	readsPrec _ ('Z':xs) = (let r = (head (reads ('Z':xs))::(AMVariable,String))
				in [(apmv (fst r),(snd r))])


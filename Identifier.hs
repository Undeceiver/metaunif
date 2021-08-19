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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ExistentialQuantification #-}
-- The purpose of this module is to enable using multiple types to identify something within a context, so that we can deal with these multiple ways transparently.
module Identifier where

import HaskellPlus
import Data.List
import Data.HashMap
import Control.Lens
import Control.Lens.Iso
import Control.Monad.State

-- Types a and b are isomorphic relative to context c.
-- Maybe isomorphism is not the best word, we refer to isomorphism modulo equivalence classes on the image. That is, it is *not* necessarily true that: (relfw c a) >>= (relbw c) = return a or that (relbw c a) >>= (relfw c) = return a,
-- but it is indeed true that (relfw c a) >>= (relbw c) >>= (relfw c) = relfw c a and (relbw c a) >>= (relfw c) >>= (relbw c) = relbw c
-- Update: We have changed the semantics of this a bit. a and b are not symmetrical. For every b there needs to be an a, but some a's may exist without a corresponding b.
class Monad m => RelativeIso m c a b where
	relbw :: c -> b -> m a
	relfw :: c -> a -> m (Maybe b)	

-- a is the canonical identifier.
data RelativeId m c a = DirectId a | forall b. RelativeIso m c a b => RelBwId b

getRelativeId :: Monad m => c -> RelativeId m c a -> m a
getRelativeId c (DirectId a) = return a
getRelativeId c (RelBwId b) = relbw c b

getRelativeCoId :: (RelativeIso m c a b, Monad m) => c -> RelativeId m c a -> m (Maybe b)
getRelativeCoId c rid = (getRelativeId c rid) >>= (relfw c)

eqRelativeIds :: (Monad m, Eq a) => c -> RelativeId m c a -> RelativeId m c a -> m Bool
eqRelativeIds c a b = do {ida <- getRelativeId c a; idb <- getRelativeId c b; return (ida == idb)}

-- To deal with relative ids, we define an iso that, given a context, allows us to manipulate the relative id as if it were an a (over the monad). This is the most general way to do so.
iso_relativeid :: Monad m => c -> Iso' (m (RelativeId m c a)) (m a)
iso_relativeid ctxt = iso (>>= (getRelativeId ctxt)) (fmap DirectId)

-- A straightforward use of this is with the state monad.
-- There is a more general application of the StateT monad which does not assume it is also the underlying monad, but that one is not so interesting.
-- The magic here is that we use the c within the state, but otherwise this is the same as iso_relativeid
state_iso_relativeid :: Monad m => Iso' (StateT c m (RelativeId (StateT c m) c a)) (StateT c m a)
state_iso_relativeid = iso state_iso_relativeid_bw (fmap DirectId)

state_iso_relativeid_bw :: Monad m => StateT c m (RelativeId (StateT c m) c a) -> StateT c m a
state_iso_relativeid_bw st = StateT (\c -> (runStateT st c) >>= (\(rid,rc) -> runStateT (getRelativeId rc rid) rc))

-- A special instance of RelativeIso in which we work with the true assumption that when using state_iso_relativeid the state value is the same when calling relfw and relbw as it will be in the state itself.
class Monad m => STRelativeIso m c a b where
	strelfw :: a -> StateT c m (Maybe b)
	strelbw :: b -> StateT c m a

newtype STRelativeIsoInst a = STRII {fromSTRII :: a}

instance STRelativeIso m c a b => RelativeIso (StateT c m) c (STRelativeIsoInst a) (STRelativeIsoInst b) where
	relfw _ = ((STRII <$>) <$>) . strelfw . fromSTRII
	relbw _ = (STRII <$>) . strelbw . fromSTRII

getSTRelativeId :: Monad m => RelativeId (StateT c m) c a -> StateT c m a
getSTRelativeId rid = StateT (\c -> runStateT (getRelativeId c rid) c)

getSTRelativeCoId :: (STRelativeIso m c a b, Monad m) => RelativeId (StateT c m) c a -> StateT c m (Maybe b)
getSTRelativeCoId rid = (getSTRelativeId rid) >>= strelfw

eqSTRelativeIds :: (Monad m, Eq a) => RelativeId (StateT c m) c a -> RelativeId (StateT c m) c a -> StateT c m Bool
eqSTRelativeIds a b = do {ida <- getSTRelativeId a; idb <- getSTRelativeId b; return (ida == idb)}

compareSTRelativeIds :: Monad m => (a -> a -> Bool) -> RelativeId (StateT c m) c a -> RelativeId (StateT c m) c a -> StateT c m Bool
compareSTRelativeIds f a b = do {ida <- getSTRelativeId a; idb <- getSTRelativeId b; return (f ida idb)}

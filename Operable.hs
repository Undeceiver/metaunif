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
module Operable where

import HaskellPlus
import Data.List
import Data.Map.Strict
import EnumProc
import Data.Maybe
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import Control.Monad.Morph
import Data.PQueue.Min

-- Less priority means it gets executed first.
-- An important decision that we made is to inherit the unspecified order for elements which are in the same equivalence class. That is, not necessarily respecting insertion order when running operations.
-- This is to be taken seriously by users of the module. Conceptually, users should have a very clear definition of a correct priority of their operations which is not dependant on insertion order.
-- If they want to just use creation order, use the CreationOrder type.
-- Very importantly, when running an operation, other operations may get queued. This is the key difference with simply running the operation instantly.
class Ord op => Operation op s | op -> s where
	runOp :: s -> op -> (s,[op])

-- Operating room seemed an excessively long and metaphorical name.
data Operating op s = Operating s (MinQueue op)

emptyOp :: s -> Operating op s
emptyOp s = Operating s (Data.PQueue.Min.empty)

insertOp :: Operation op s => Operating op s -> op -> Operating op s
insertOp (Operating s q) op = Operating s (Data.PQueue.Min.insert op q)

(<+) :: Operation op s => Operating op s -> op -> Operating op s
(<+) = insertOp
infixl 4 <+

runNextOp :: Operation op s => Operating op s -> Operating op s
runNextOp (Operating s q) = if (isNothing mb_rs) then (Operating s q) else (Operating rs rrq) where mb_rs = Data.PQueue.Min.minView q; (nextop,rq) = fromJust mb_rs; (rs,rops) = runOp s nextop; rrq = Data.List.foldr Data.PQueue.Min.insert rq rops

-- Important note to self: I may have to implement a version of the below function which returns an EnumProc, in the case that this process may be non-terminating. I don't do it for now, but keep it in mind.
runAllOps :: Operation op s => Operating op s -> Operating op s
runAllOps (Operating s q) = if (Data.PQueue.Min.null q) then (Operating s q) else (runAllOps (runNextOp (Operating s q)))

runOps :: Operation op s => Operating op s -> s
runOps ops = rs where (Operating rs _) = runAllOps ops

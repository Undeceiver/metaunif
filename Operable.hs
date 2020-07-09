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
import Data.Tuple
import Debug.Trace

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

insertOp :: Ord op => Operating op s -> op -> Operating op s
insertOp (Operating s q) op = Operating s (Data.PQueue.Min.insert op q)

(<+) :: Ord op => Operating op s -> op -> Operating op s
(<+) = insertOp
infixl 4 <+

runNextOp :: Operation op s => Operating op s -> Operating op s
runNextOp (Operating s q) = if (isNothing mb_rs) then (Operating s q) else (Operating rs rrq) where mb_rs = Data.PQueue.Min.minView q; (nextop,rq) = fromJust mb_rs; (rs,rops) = runOp s nextop; rrq = Data.List.foldr Data.PQueue.Min.insert rq rops

-- Important note to self: I may have to implement a version of the below function which returns an EnumProc, in the case that this process may be non-terminating. I don't do it for now, but keep it in mind.
runAllOps :: Operation op s => Operating op s -> Operating op s
runAllOps (Operating s q) = if (Data.PQueue.Min.null q) then (Operating s q) else (runAllOps (runNextOp (Operating s q)))

runOps :: Operation op s => Operating op s -> s
runOps ops = rs where (Operating rs _) = runAllOps ops


-- And just because monads, here you have the same, but with monads...
class (Ord op, Monad m) => MOperation m op s | op -> m s where
	runMOp :: s -> op -> m (s,[op])

runNextMOp :: MOperation m op s => Operating op s -> m (Operating op s)
runNextMOp (Operating s q) = do
	{
		let {mb_rs = Data.PQueue.Min.minView q};
		let {(nextop,rq) = fromJust mb_rs};
		(rs,rops) <- runMOp s nextop;
		let {rrq = Data.List.foldr Data.PQueue.Min.insert rq rops};
		if (isNothing mb_rs) then (return (Operating s q)) else (return (Operating rs rrq))
	}

runAllMOps :: MOperation m op s => Operating op s -> m (Operating op s)
runAllMOps (Operating s q) = if (Data.PQueue.Min.null q) then (return (Operating s q)) else (runNextMOp (Operating s q) >>= runAllMOps)

runMOps :: MOperation m op s => Operating op s -> m s
runMOps ops = (\(Operating rs _) -> rs) <$> (runAllMOps ops)



-- And now the particular case of StateT, with some tricks to simplify
class (Ord op, Monad m) => StateTOperation m op s | op -> s where
	runStateTOp :: op -> StateT s m [op]

runNextStateTOp :: StateTOperation m op s => StateT (Operating op s) m ()
runNextStateTOp = StateT (\(Operating s q) -> do
	{
		let {mb_rs = Data.PQueue.Min.minView q};
		let {(nextop,rq) = fromJust mb_rs};
		(rops,rs) <- runStateT (runStateTOp nextop) s;
		let {rrq = Data.List.foldr Data.PQueue.Min.insert rq rops};
		if (isNothing mb_rs) then (return ((),Operating s q)) else (return ((),Operating rs rrq))
	})

runAllStateTOps :: StateTOperation m op s => StateT (Operating op s) m ()
runAllStateTOps = StateT (\(Operating s q) -> if (Data.PQueue.Min.null q) then (return ((),Operating s q)) else (trace "RUNNING AN OP" (runStateT runNextStateTOp (Operating s q)) >>= (\((),ss) -> runStateT runAllStateTOps ss)))
--runAllStateTOps = StateT (\(Operating s q) -> if (Data.PQueue.Min.null q) then (return ((),Operating s q)) else (runStateT runNextStateTOp (Operating s q)) >>= (\((),ss) -> runStateT runAllStateTOps ss))

runStateTOps :: StateTOperation m op s => [op] -> StateT s m ()
runStateTOps ops = StateT (f_runStateTOps ops)

f_runStateTOps :: StateTOperation m op s => [op] -> s -> m ((),s)
f_runStateTOps ops s = (\((),Operating rs _) -> ((),rs)) <$> rm where rm = runStateT runAllStateTOps (Prelude.foldr (flip (<+)) (emptyOp s) ops)

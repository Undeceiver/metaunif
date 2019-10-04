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
-- This module defines exclusively the notion of a query. It does *not* implement solvers for queries.
-- It also does so in as much a polymorphic way as possible, leaving things like first-order, second-order and specific term structures open to the user.
module QueryLogic where

import Control.Unification
import Control.Unification.IntVar
import HaskellPlus
import Data.Either
import Control.Unification.Types
import Data.List
import Data.Maybe
import Data.Map.Strict
import Syntax
import AnswerSet

-- Conceptually, SequentialQ is like an inner join performed quadratically, while ImplicitQ is like an inner join performed via some form of match algorithm. ProductQ is an outer join.
-- Note that we read in function composition order: queries to the right are performed first.
-- The variables in the select clause of the BaseQ is not necessarily all the free variables. There may be other free variables that are input from an argument map and replaced thus by elements.
-- Variables in the select clause is a subset of the free variables in a query.
-- Remaining free variables in a query after substitutions that are not part of the select clause are taken to be existential: they are calculated as part of the query, but discarded.
-- Note also that because we use Maps to express responses, products which share variables will be problematic. It should be ensured to standardize variables apart before performing products.
data Query (q :: *) (v :: *) (r :: *) = BaseQ [v |<- r] q | SequentialQ (Query q v r) (v :->= r) (Query q v r) | ImplicitQ (Query q v r) (v :->= r) (Query q v r) | ProductQ (Query q v r) (Query q v r)

data QuerySelect v r = QVar v | QConst r
type (v |<- r) = QuerySelect v r
infix 7 |<-

type QArgumentMap v r = (v := ((v := r) -> r))
type (v :->= r) = QArgumentMap v r
infix 7 :->=

instance Functional (QArgumentMap v r) (v := r) (AnswerSet s (v := r)) where
	tofun argmap m = SingleAS (fmap ($ m) argmap)

data ProductQOP = ProductQOP

instance Ord v => Functional ProductQOP (v := r, v := r) (AnswerSet s (v := r)) where
	tofun ProductQOP (m1,m2) = SingleAS (Data.List.foldr (\(v,r) -> Data.Map.Strict.insert v r) m1 (assocs m2))

instance (Eq v, Substitutable r v r) => Substitutable (v |<- r) v r where
	subst v2 r (QVar v1) | v1 == v2 = QConst r
	subst v2 r (QVar v1) = QVar v1
	subst v2 r (QConst r2) = QConst (subst v2 r r2)

qFreeVarsSelect :: [v |<- r] -> [v]
qFreeVarsSelect [] = []
qFreeVarsSelect ((QVar v):xs) = (v:(qFreeVarsSelect xs))
qFreeVarsSelect ((QConst r):xs) = qFreeVarsSelect xs

qSelectVars :: Eq v => Query q v r -> [v]
qSelectVars (BaseQ vs _) = qFreeVarsSelect vs
qSelectVars (SequentialQ q1 argmap q2) = (qSelectVars q1) Data.List.\\ (keys argmap)
qSelectVars (ImplicitQ q1 argmap q2) = (qSelectVars q1) Data.List.\\ (keys argmap)
qSelectVars (ProductQ q1 q2) = (qSelectVars q1) ++ (qSelectVars q2)

instance (Eq v, Substitutable r v r, Ord v) => Substitutable (QArgumentMap v r) v r where
	subst v2 r = fmap (\f -> (\m -> f (Data.Map.Strict.insert v2 r m)))

instance (Eq v, Substitutable r v r, Substitutable q v r, Ord v) => Substitutable (Query q v r) v r where
	subst v2 r (BaseQ vs q) = BaseQ (subst v2 r vs) (subst v2 r q)
	subst v2 r (SequentialQ q1 m q2) | member v2 m = SequentialQ q1 (subst v2 r m) (subst v2 r q2)
	subst v2 r (SequentialQ q1 m q2) = SequentialQ (subst v2 r q1) (subst v2 r m) (subst v2 r q2)
	subst v2 r (ImplicitQ q1 m q2) | member v2 m = ImplicitQ q1 (subst v2 r m) (subst v2 r q2)
	subst v2 r (ImplicitQ q1 m q2) = ImplicitQ (subst v2 r q1) (subst v2 r m) (subst v2 r q2)
	subst v2 r (ProductQ q1 q2) = ProductQ (subst v2 r q1) (subst v2 r q2)

class Queriable q v r s | q v -> r s where
	runBaseQ :: [v |<- r] -> q -> AnswerSet s (v := r)

runQuery :: (Queriable q v r s, Eq v, Substitutable r v r, Substitutable q v r, Ord v, ImplicitF s (v := r) si (v := r) (QArgumentMap v r), ImplicitF si (v := r) s (v := r) (Query q v r), ImplicitF (AnswerSet s (v := r), AnswerSet s (v := r)) (v := r, v := r) s (v := r) ProductQOP, Eq r) => Query q v r -> AnswerSet s (v := r)
runQuery (BaseQ vs q) = runBaseQ vs q
runQuery (SequentialQ q1 m q2) = (runQuery q2) >>= (\m2 -> runQuery (Data.List.foldr (\(v,f) -> subst v (f m2)) q1 (assocs m)))
runQuery (ImplicitQ q1 m q2) = (runQuery q2) ?>>= m ?>>= q1
runQuery (ProductQ q1 q2) = (tupleAS (runQuery q1) (runQuery q2)) ?>>= ProductQOP

instance (Queriable q v r s, Eq v, Substitutable r v r, Substitutable q v r, Ord v, ImplicitF s (v := r) si (v := r) (QArgumentMap v r), ImplicitF si (v := r) s (v := r) (Query q v r), ImplicitF (AnswerSet s (v := r), AnswerSet s (v := r)) (v := r, v := r) s (v := r) ProductQOP, Eq r) => Functional (Query q v r) (v := r) (AnswerSet s (v := r)) where
	tofun q m = runQuery (Data.List.foldr (\(v,r) -> subst v r) q (assocs m))

-- We include only one formula, so it must include the theory and the goal in it. Typically through negated conjunction.
data LogicQuery f = Entails f | Satisfies f | Equals f f


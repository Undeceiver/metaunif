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
import EnumProc
import Data.Bifunctor

-- Conceptually, SequentialQ is like an inner join performed quadratically, while ImplicitQ is like an inner join performed via some form of match algorithm. ProductQ is an outer join.
-- Intersection is a nested query in the where clause.
-- Note that we read in function composition order: queries to the right are performed first.
-- The variables in the select clause of the BaseQ is not necessarily all the free variables. There may be other free variables that are input from an argument map and replaced thus by elements.
-- Variables in the select clause is a subset of the free variables in a query.
-- Remaining free variables in a query after substitutions that are not part of the select clause are taken to be existential: they are calculated as part of the query, but discarded.
-- Note also that because we use Maps to express responses, products which share variables will be problematic. It should be ensured to standardize variables apart before performing products.
-- Implicit calculation of intersection is not supported: Intersection is always calculated explicitly.
data Query (q :: *) (v :: *) (r :: *) = BaseQ [v |<- r] q | SequentialQ (Query q v r) (v :->= r) (Query q v r) | ImplicitQ (Query q v r) (v :->= r) (Query q v r) | ProductQ (Query q v r) (Query q v r) | IntersectionQ (Query q v r) (v :->= r) (Query q v r)

instance (Show q, Show v, Show r) => Show (Query q v r) where
	show (BaseQ sel q) = (show sel) ++ " " ++ (show q)
	-- The choice of making argument maps functions makes it so that we cannot show them properly. It's not a huge deal, but worth mentioning. We omit it in the show.
	show (SequentialQ q1 m q2) = "(" ++ (show q1) ++ ") <- (" ++ (show q2) ++ ")"
	show (ImplicitQ q1 m q2) = "(" ++ (show q1) ++ ") <= (" ++ (show q2) ++ ")"
	show (ProductQ q1 q2) = "(" ++ (show q1) ++ ") x (" ++ (show q2) ++ ")"
	show (IntersectionQ q1 m q2) = "ALL (" ++ (show q1) ++ ") <= (" ++ (show q2) ++ ")"

($<-) :: Query q v r -> Query q v r -> (v :->= r) -> Query q v r
q1 $<- q2 = (\m -> SequentialQ q1 m q2)
infix 7 $<-

($<=) :: Query q v r -> Query q v r -> (v :->= r) -> Query q v r
q1 $<= q2 = (\m -> ImplicitQ q1 m q2)
infix 7 $<=

($<=|) :: Query q v r -> Query q v r -> (v :->= r) -> Query q v r
q1 $<=| q2 = (\m -> IntersectionQ q1 m q2)
infix 7 $<=|

data QuerySelect v r = QVar v | QConst r
type (v |<- r) = QuerySelect v r
infix 7 |<-

instance (Show v, Show r) => Show (QuerySelect v r) where
	show (QVar v) = "?" ++ (show v)
	show (QConst r) = ":" ++ (show r)

instance (Read v, Read r) => Read (QuerySelect v r) where
	readsPrec _ xs =
		case stripPrefix "?" xs of
		{
			Just rest -> (let r = (head (reads rest)::(v,String)) in
				[(QVar (fst r), (snd r))]);
			Nothing ->
		case stripPrefix ":" xs of
		{
			Just rest -> (let r = (head (reads rest)::(r,String)) in
				[(QConst (fst r), (snd r))]);
			Nothing -> error ("Could not read select clause in query: " ++ xs)
		}}

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

instance (Eq v, Substitutable r v r) => Substitutable [(v |<- r)] v r where
	subst = subst_fmap


-- Sadly, to allow variable substitution, we need to wrap things in the query in newtypes.
newtype VarSubstQuerySelect v r = VarSubstQuerySelect {fromVarSubstQuerySelect :: (v |<- r)}
instance Eq v => Substitutable (VarSubstQuerySelect v r) v v where
	subst v2 v3 (VarSubstQuerySelect (QVar v1)) | v1 == v2 = (VarSubstQuerySelect (QVar v3))
	subst v2 v3 (VarSubstQuerySelect (QVar v1)) = (VarSubstQuerySelect (QVar v1))
	subst v2 v3 (VarSubstQuerySelect (QConst r2)) = (VarSubstQuerySelect (QConst r2))

instance Eq v => Substitutable [VarSubstQuerySelect v r] v v where
	subst = subst_fmap

qFreeVarsSelect :: [v |<- r] -> [v]
qFreeVarsSelect [] = []
qFreeVarsSelect ((QVar v):xs) = (v:(qFreeVarsSelect xs))
qFreeVarsSelect ((QConst r):xs) = qFreeVarsSelect xs

qSelectVars :: Eq v => Query q v r -> [v]
qSelectVars (BaseQ vs _) = qFreeVarsSelect vs
qSelectVars (SequentialQ q1 argmap q2) = (qSelectVars q1) Data.List.\\ (keys argmap)
qSelectVars (ImplicitQ q1 argmap q2) = (qSelectVars q1) Data.List.\\ (keys argmap)
qSelectVars (ProductQ q1 q2) = (qSelectVars q1) ++ (qSelectVars q2)
qSelectVars (IntersectionQ q1 argmap q2) = (qSelectVars q1) Data.List.\\ (keys argmap)

instance (Eq v, Substitutable r v r, Ord v) => Substitutable (QArgumentMap v r) v r where
	subst v2 r = fmap (\f -> (\m -> f (Data.Map.Strict.insert v2 r m)))

newtype VarSubstArgumentMap v r = VarSubstArgumentMap {fromVarSubstArgumentMap :: QArgumentMap v r}
instance (Eq v, Ord v) => Substitutable (VarSubstArgumentMap v r) v v where
	subst v2 v3 m = VarSubstArgumentMap (Data.Map.Strict.insert v2 (\m2 -> m2 ! v3) (fromVarSubstArgumentMap m))

instance (Eq v, Substitutable r v r, Substitutable q v r, Ord v) => Substitutable (Query q v r) v r where
	subst v2 r (BaseQ vs q) = BaseQ (subst v2 r vs) (subst v2 r q)
	subst v2 r (SequentialQ q1 m q2) | member v2 m = SequentialQ q1 (subst v2 r m) (subst v2 r q2)
	subst v2 r (SequentialQ q1 m q2) = SequentialQ (subst v2 r q1) (subst v2 r m) (subst v2 r q2)
	subst v2 r (ImplicitQ q1 m q2) | member v2 m = ImplicitQ q1 (subst v2 r m) (subst v2 r q2)
	subst v2 r (ImplicitQ q1 m q2) = ImplicitQ (subst v2 r q1) (subst v2 r m) (subst v2 r q2)
	subst v2 r (ProductQ q1 q2) = ProductQ (subst v2 r q1) (subst v2 r q2)
	subst v2 r (IntersectionQ q1 m q2) | member v2 m = IntersectionQ q1 (subst v2 r m) (subst v2 r q2)
	subst v2 r (IntersectionQ q1 m q2) = IntersectionQ (subst v2 r q1) (subst v2 r m) (subst v2 r q2)


newtype VarSubstQuery q v r = VarSubstQuery {fromVarSubstQuery :: Query q v r}
instance (Eq v, Substitutable q v v, Ord v) => Substitutable (VarSubstQuery q v r) v v where
	subst v2 r (VarSubstQuery (BaseQ vs q)) = VarSubstQuery (BaseQ (fmap fromVarSubstQuerySelect (subst v2 r (fmap VarSubstQuerySelect vs))) (subst v2 r q))
	subst v2 r (VarSubstQuery (SequentialQ q1 m q2)) | member v2 m = VarSubstQuery (SequentialQ q1 (fromVarSubstArgumentMap (subst v2 r (VarSubstArgumentMap m))) (fromVarSubstQuery (subst v2 r (VarSubstQuery q2))))
	subst v2 r (VarSubstQuery (SequentialQ q1 m q2)) = VarSubstQuery (SequentialQ (fromVarSubstQuery (subst v2 r (VarSubstQuery q1))) (fromVarSubstArgumentMap (subst v2 r (VarSubstArgumentMap m))) (fromVarSubstQuery (subst v2 r (VarSubstQuery q2))))
	subst v2 r (VarSubstQuery (ImplicitQ q1 m q2)) | member v2 m = VarSubstQuery (ImplicitQ q1 (fromVarSubstArgumentMap (subst v2 r (VarSubstArgumentMap m))) (fromVarSubstQuery (subst v2 r (VarSubstQuery q2))))
	subst v2 r (VarSubstQuery (ImplicitQ q1 m q2)) = VarSubstQuery (ImplicitQ (fromVarSubstQuery (subst v2 r (VarSubstQuery q1))) (fromVarSubstArgumentMap (subst v2 r (VarSubstArgumentMap m))) (fromVarSubstQuery (subst v2 r (VarSubstQuery q2))))
	subst v2 r (VarSubstQuery (ProductQ q1 q2)) = VarSubstQuery (ProductQ (fromVarSubstQuery (subst v2 r (VarSubstQuery q1))) (fromVarSubstQuery (subst v2 r (VarSubstQuery q2))))
	subst v2 r (VarSubstQuery (IntersectionQ q1 m q2)) | member v2 m = VarSubstQuery (IntersectionQ q1 (fromVarSubstArgumentMap (subst v2 r (VarSubstArgumentMap m))) (fromVarSubstQuery (subst v2 r (VarSubstQuery q2))))
	subst v2 r (VarSubstQuery (IntersectionQ q1 m q2)) = VarSubstQuery (IntersectionQ (fromVarSubstQuery (subst v2 r (VarSubstQuery q1))) (fromVarSubstArgumentMap (subst v2 r (VarSubstArgumentMap m))) (fromVarSubstQuery (subst v2 r (VarSubstQuery q2))))


class Queriable q v t r s | q v t -> r s where
	runBaseQ :: t -> [v |<- r] -> q -> AnswerSet s (v := r)

type BaseQueryInput q v t r = (t,[v |<- r],q)
type QueryInput q v t r = (t,Query q v r)

runBaseQIn :: Queriable q v t r s => BaseQueryInput q v t r -> AnswerSet s (v := r)
runBaseQIn (t,s,q) = runBaseQ t s q

runQuery :: (Queriable q v t r s, Eq v, Substitutable r v r, Substitutable q v r, Ord v, FullImplicitF s (v := r) s (v := r) (QArgumentMap v r), FullImplicitF s (v := r) s (v := r) (BaseQueryInput q v t r), FullImplicitF (AnswerSet s (v := r), AnswerSet s (v := r)) (v := r, v := r) s (v := r) ProductQOP, Eq r) => t -> Query q v r -> AnswerSet s (v := r)
runQuery t (BaseQ vs q) = runBaseQ t vs q
runQuery t (SequentialQ q1 m q2) = (runQuery t q2) >>= (\m2 -> runQuery t (Data.List.foldr (\(v,f) -> subst v (f m2)) q1 (assocs m)))
runQuery t (ImplicitQ q1 m q2) = (runQuery t q2) ?>>= m ?>>= (t,q1)
runQuery t (ProductQ q1 q2) = (tupleAS (runQuery t q1) (runQuery t q2)) ?>>= ProductQOP
runQuery t (IntersectionQ q1 m q2) = ExplicitAS (SingleAS <$> (eintersectAll ((\m2 -> diagEnumAS (runQuery t (Data.List.foldr (\(v,f) -> subst v (f m2)) q1 (assocs m)))) <$> (diagEnumAS (runQuery t q2)))))

-- In this instance we assume that the argument map has already been processed. This is important, as a base query does not include the argument map in itself, but it must be processed for correctness.
-- That is, the input map is expressed in the variables of the query.
instance (Queriable q v t r s, Eq v, Substitutable r v r, Substitutable q v r, Ord v) => Functional (BaseQueryInput q v t r) (v := r) (AnswerSet s (v := r)) where
	tofun (t,s,q) m = runBaseQ t s (Data.List.foldr (\(v,r) -> subst v r) q (assocs m))

instance (Queriable q v t r s, Eq v, Substitutable r v r, Substitutable q v r, Ord v, Implicit s (v := r), FullImplicitF s (v := r) s (v := r) (BaseQueryInput q v t r), FullImplicitF s (v := r) s (v := r) (QArgumentMap v r), FullImplicitF (AnswerSet s (v := r), AnswerSet s (v := r)) (v := r, v := r) s (v := r) ProductQOP, Eq r) => ImplicitF s s (v := r) (QueryInput q v t r) where
	composeImplicit s (t,(BaseQ vs q)) = composeImplicit s (t,vs,q)
	composeImplicit s (t,(SequentialQ q1 m q2)) = (composeImplicit s (t,q2)) >>= (\m2 -> runQuery t (Data.List.foldr (\(v,f) -> subst v (f m2)) q1 (assocs m)))
	composeImplicit s (t,(ImplicitQ q1 m q2)) = (composeImplicit s (t,q2)) ?>>= m ?>>= (t,q1)
	composeImplicit s (t,(ProductQ q1 q2)) = (tupleAS (composeImplicit s (t,q1)) (composeImplicit s (t,q2))) ?>>= ProductQOP
	composeImplicit s (t,(IntersectionQ q1 m q2)) = ExplicitAS (SingleAS <$> (eintersectAll ((\m2 -> diagEnumAS (runQuery t (Data.List.foldr (\(v,f) -> subst v (f m2)) q1 (assocs m)))) <$> (diagEnumAS (composeImplicit s (t,q2))))))

instance (Queriable q v t r s, Eq v, Substitutable r v r, Substitutable q v r, Ord v, FullImplicitF s (v := r) s (v := r) (QArgumentMap v r), FullImplicitF s (v := r) s (v := r) (BaseQueryInput q v t r), FullImplicitF (AnswerSet s (v := r), AnswerSet s (v := r)) (v := r, v := r) s (v := r) ProductQOP, Eq r) => Functional (QueryInput q v t r) (v := r) (AnswerSet s (v := r)) where
	tofun (t,q) m = runQuery t (Data.List.foldr (\(v,r) -> subst v r) q (assocs m))

data LogicQuery cnf t = Entails cnf | Satisfies cnf cnf | Equals t t | NotEquals t t deriving Functor

instance Bifunctor LogicQuery where
	bimap f g (Entails x) = Entails (f x)
	bimap f g (Satisfies x y) = Satisfies (f x) (f y)
	bimap f g (Equals x y) = Equals (g x) (g y)
	bimap f g (NotEquals x y) = NotEquals (g x) (g y)

instance (Show cnf, Show t) => Show (LogicQuery cnf t) where
	show (Entails x) = "|= " ++ (show x)
	show (Satisfies x y) = "*|= " ++ (show x) ++ " || " ++ (show y)
	show (Equals x y) = (show x) ++ " ~ " ++ (show y)
	show (NotEquals x y) = (show x) ++ " # " ++ (show y)

instance (Read cnf, Read t) => Read (LogicQuery cnf t) where
	readsPrec _ xs =
		case stripPrefix "|= " xs of
		{
			Just rest -> (let r = (head (reads rest)::(cnf,String)) in
				[(Entails (fst r), (snd r))]);
			Nothing ->
		case stripPrefix "*|= " xs of
		{
			Just rest -> (let r = (head (reads rest)::(cnf,String)) in
				(case stripPrefix " || " (snd r) of
				{
					Just rest2 -> (let r2 = (head (reads rest2)::(cnf,String)) in
						[(Satisfies (fst r) (fst r2), (snd r2))]);
					Nothing -> error ("Could not read logic query: " ++ xs)
				}));
			Nothing ->
		case break (== '~') xs of 
		{
			(t1,('~':' ':t2)) -> (let r1 = (head (reads t1)::(t,String)) in
				(let r2 = (head (reads t2)::(t,String)) in
					[(Equals (fst r1) (fst r2), (snd r2))]));
			_ ->
		case break (== '#') xs of 
		{
			(t1,('#':' ':t2)) -> (let r1 = (head (reads t1)::(t,String)) in
				(let r2 = (head (reads t2)::(t,String)) in
					[(NotEquals (fst r1) (fst r2), (snd r2))]));
			_ -> error ("Could not read logic query: " ++ xs)
		}}}}


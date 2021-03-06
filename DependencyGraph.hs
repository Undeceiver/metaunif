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
-- This class really is very much designed to work as a carrier of existential second-order unification data. It is unlikely that it can be used as is for other purposes.
-- However, we separate this from the actual second-order logic semantics because here we provide the most basic primitives to deal with the graph-ish data that we deal with there,
-- while there we will provide higher level operations that do more intelligent things on the graph as a unifier itself.
module DependencyGraph where

import HaskellPlus
import Data.List
import Data.Map.Strict
import EnumProc
import Data.Maybe
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import Control.Monad.Morph
import Operable
import Control.Monad.ST
--import Data.UnionFind.ST
import Safe (headMay)
import Identifier
--import DebugTricks
import Debug.Trace
import GlobalTrace

-- These graphs have:
--	* Two types of nodes:
--		- First-order nodes, that are sources or targets of first-order edges
--		- Second-order nodes, that can be sources or targets of second-order edges, and heads of first-order or second-order edges
--	* Two types of edges:
--		- First-order edges, that have multiple sources (first-order nodes), one target (first-order node), and one head (second-order node). In the intended use these represent first-order term structures.
--		- Second-order edges, that have multiple sources (second-order nodes), one target (second-order node), and one head (second-order node). In the intended use these represent second-order term structures.

-- Some basic notions to deal with the graph:
-- All its elements have an identifier (an integer) that is used whenever we wish to do something with an element within the graph. This allows us to keep a cyclic data structure while being able to update it properly and efficiently.
-- We categorically do not store any domain data in the graph itself. The graph contains strictly the structure. For example, in our unification usage of this data structure, we will implement a structure on top of the graph that stores all of the dependant, function and related data, associating it with nodes in the graph via its identifiers.
-- The identifiers are the soul of the graph. The graph may change its topology, but conceptually you can trace how it changed and what became what via the node identifiers. Therefore, it is very important when using the graphs to know when to update a node and when to replace it with a different node, as it means conceptually very different things.
-- What the elements of the structure do contain, however, are pointers to other elements of the structure itself, for quick traversal and search. Any updates, however, should *always* be done using the global graph functions, of course.
-- The identifier is unique amongst each element type, not necessarily amongst all of them together.

class DGElement t where
	dgid :: t -> Int

newtype DGElementEq t = DGElementEq t
instance DGElement t => Eq (DGElementEq t) where
	(DGElementEq a) == (DGElementEq b) = (dgid a) == (dgid b)

instance DGElement t => Ord (DGElementEq t) where
	(DGElementEq a) <= (DGElementEq b) = (dgid a) <= (dgid b)

-- Identifier, outgoing edges, incoming edges.
data DGFONode = DGFONode Int [Int] [Int]
-- Identifier, head, sources, target
data DGFOEdge = DGFOEdge Int Int [Int] Int
-- Identifier, outgoing edges, incoming edges, f.o. edges it's a head of, s.o. edges it's a head of.
data DGSONode = DGSONode Int [Int] [Int] [Int] [Int]
-- Identifier, head, sources, target
data DGSOEdge = DGSOEdge Int Int [Int] Int

instance DGElement DGFONode where
	dgid (DGFONode id _ _) = id

deriving via (DGElementEq DGFONode) instance (Eq DGFONode)
deriving via (DGElementEq DGFONode) instance (Ord DGFONode)

instance DGElement DGFOEdge where
	dgid (DGFOEdge id _ _ _) = id

deriving via (DGElementEq DGFOEdge) instance (Eq DGFOEdge)
deriving via (DGElementEq DGFOEdge) instance (Ord DGFOEdge)

instance DGElement DGSONode where
	dgid (DGSONode id _ _ _ _) = id

deriving via (DGElementEq DGSONode) instance (Eq DGSONode)
deriving via (DGElementEq DGSONode) instance (Ord DGSONode)

instance DGElement DGSOEdge where
	dgid (DGSOEdge id _ _ _) = id

deriving via (DGElementEq DGSOEdge) instance (Eq DGSOEdge)
deriving via (DGElementEq DGSOEdge) instance (Ord DGSOEdge)

-- Turns out that lenses for the basic elements sub-parts might be useful.
-- We do not need lenses for the identifier: we can obtain it with dgid and there is no sensible occassion in which we wish to modify just that.
lens_dgfonode_out :: Lens' DGFONode [Int]
lens_dgfonode_out f (DGFONode id eout ein) = fmap (\reout -> DGFONode id reout ein) (f eout)

lens_dgfonode_in :: Lens' DGFONode [Int]
lens_dgfonode_in f (DGFONode id eout ein) = fmap (\rein -> DGFONode id eout rein) (f ein)

lens_dgfoedge_head :: Lens' DGFOEdge Int
lens_dgfoedge_head f (DGFOEdge id h ss t) = fmap (\rh -> DGFOEdge id rh ss t) (f h)

lens_dgfoedge_sources :: Lens' DGFOEdge [Int]
lens_dgfoedge_sources f (DGFOEdge id h ss t) = fmap (\rss -> DGFOEdge id h rss t) (f ss)

lens_dgfoedge_target :: Lens' DGFOEdge Int
lens_dgfoedge_target f (DGFOEdge id h ss t) = fmap (\rt -> DGFOEdge id h ss rt) (f t)

lens_dgsonode_out :: Lens' DGSONode [Int]
lens_dgsonode_out f (DGSONode id eout ein foh soh) = fmap (\reout -> DGSONode id reout ein foh soh) (f eout)

lens_dgsonode_in :: Lens' DGSONode [Int]
lens_dgsonode_in f (DGSONode id eout ein foh soh) = fmap (\rein -> DGSONode id eout rein foh soh) (f ein)

lens_dgsonode_foh :: Lens' DGSONode [Int]
lens_dgsonode_foh f (DGSONode id eout ein foh soh) = fmap (\rfoh -> DGSONode id eout ein rfoh soh) (f foh)

lens_dgsonode_soh :: Lens' DGSONode [Int]
lens_dgsonode_soh f (DGSONode id eout ein foh soh) = fmap (\rsoh -> DGSONode id eout ein foh rsoh) (f soh)

lens_dgsoedge_head :: Lens' DGSOEdge Int
lens_dgsoedge_head f (DGSOEdge id h ss t) = fmap (\rh -> DGSOEdge id rh ss t) (f h)

lens_dgsoedge_sources :: Lens' DGSOEdge [Int]
lens_dgsoedge_sources f (DGSOEdge id h ss t) = fmap (\rss -> DGSOEdge id h rss t) (f ss)

lens_dgsoedge_target :: Lens' DGSOEdge Int
lens_dgsoedge_target f (DGSOEdge id h ss t) = fmap (\rt -> DGSOEdge id h ss rt) (f t)



-- As a matter of fact, for quick access, elements of the graph are stored in lists with their identifiers as indices. However, because elements may be removed, these lists may contain empty elements.
-- Technically speaking, an array-like type would be more efficient than lists. This should be fairly easy to change later on if need be, so for now we leave it as lists. Abstract away from this implementation so that we can change it if/when necessary.
data DGraph = DGraph [Maybe DGFONode] [Maybe DGFOEdge] [Maybe DGSONode] [Maybe DGSOEdge]

-- Basic lenses for the dependency graph
lens_fonodes :: Lens' DGraph [Maybe DGFONode]
lens_fonodes f (DGraph fonodes foedges sonodes soedges) = fmap (\rfonodes -> DGraph rfonodes foedges sonodes soedges) (f fonodes)

lens_foedges :: Lens' DGraph [Maybe DGFOEdge]
lens_foedges f (DGraph fonodes foedges sonodes soedges) = fmap (\rfoedges -> DGraph fonodes rfoedges sonodes soedges) (f foedges)

lens_sonodes :: Lens' DGraph [Maybe DGSONode]
lens_sonodes f (DGraph fonodes foedges sonodes soedges) = fmap (\rsonodes -> DGraph fonodes foedges rsonodes soedges) (f sonodes)

lens_soedges :: Lens' DGraph [Maybe DGSOEdge]
lens_soedges f (DGraph fonodes foedges sonodes soedges) = fmap (\rsoedges -> DGraph fonodes foedges sonodes rsoedges) (f soedges)

lens_foout :: Lens' DGFONode [Int]
lens_foout f (DGFONode id eout ein) = fmap (\reout -> DGFONode id reout ein) (f eout)

lens_foin :: Lens' DGFONode [Int]
lens_foin f (DGFONode id eout ein) = fmap (\rein -> DGFONode id eout rein) (f ein)

lens_soout :: Lens' DGSONode [Int]
lens_soout f (DGSONode id eout ein efh esh) = fmap (\reout -> DGSONode id reout ein efh esh) (f eout)

lens_soin :: Lens' DGSONode [Int]
lens_soin f (DGSONode id eout ein efh esh) = fmap (\rein -> DGSONode id eout rein efh esh) (f ein)

lens_fohs :: Lens' DGSONode [Int]
lens_fohs f (DGSONode id eout ein efh esh) = fmap (\refh -> DGSONode id eout ein refh esh) (f efh)

lens_sohs :: Lens' DGSONode [Int]
lens_sohs f (DGSONode id eout ein efh esh) = fmap (\resh -> DGSONode id eout ein efh resh) (f esh)

lens_foss :: Lens' DGFOEdge [Int]
lens_foss f (DGFOEdge id h ss t) = fmap (\rss -> DGFOEdge id h rss t) (f ss)

lens_foh :: Lens' DGFOEdge Int
lens_foh f (DGFOEdge id h ss t) = fmap (\rh -> DGFOEdge id rh ss t) (f h)

lens_fot :: Lens' DGFOEdge Int
lens_fot f (DGFOEdge id h ss t) = fmap (\rt -> DGFOEdge id h ss rt) (f t)

lens_soss :: Lens' DGSOEdge [Int]
lens_soss f (DGSOEdge id h ss t) = fmap (\rss -> DGSOEdge id h rss t) (f ss)

lens_soh :: Lens' DGSOEdge Int
lens_soh f (DGSOEdge id h ss t) = fmap (\rh -> DGSOEdge id rh ss t) (f h)

lens_sot :: Lens' DGSOEdge Int
lens_sot f (DGSOEdge id h ss t) = fmap (\rt -> DGSOEdge id h ss rt) (f t)







show_dgraph :: (Int -> String) -> (Int -> String) -> (Int -> String) -> (Int -> String) -> DGraph -> String
show_dgraph foshow soshow efoshow esoshow (DGraph fonodes foedges sonodes soedges) = (concat . (fmap (show_dgraph_sonode soshow esoshow (DGraph fonodes foedges sonodes soedges) . fromJust) . (Data.List.filter isJust)) $ sonodes) ++ "\n\n" ++ (concat . (fmap (show_dgraph_fonode foshow soshow efoshow (DGraph fonodes foedges sonodes soedges) . fromJust) . (Data.List.filter isJust)) $ fonodes)

show_dgraph_sonode :: (Int -> String) -> (Int -> String) -> DGraph -> DGSONode -> String
show_dgraph_sonode soshow esoshow dg (DGSONode id eout ein efh esh) = (soshow id) ++ ":\n\n\tOut:\n" ++ (concat . (fmap (show_dgraph_soedge_out soshow esoshow dg . fromJust . getDGSOEdge dg)) $ eout) ++ "\n\tIn:\n" ++ (concat . (fmap (show_dgraph_soedge_in soshow esoshow dg . fromJust . getDGSOEdge dg)) $ ein) ++ "\n"

show_dgraph_soedge_out :: (Int -> String) -> (Int -> String) -> DGraph -> DGSOEdge -> String
show_dgraph_soedge_out soshow esoshow dg (DGSOEdge id h ss t) = "\t\t" ++ (esoshow id) ++ "--" ++ (soshow h) ++ "->" ++ (soshow t) ++ "\n"

show_dgraph_soedge_in :: (Int -> String) -> (Int -> String) -> DGraph -> DGSOEdge -> String
show_dgraph_soedge_in soshow esoshow dg (DGSOEdge id h ss t) = "\t\t" ++ (esoshow id) ++ "<-" ++ (soshow h) ++ "--[" ++ (concat (intersperse "," (soshow <$> ss))) ++ "]\n"

show_dgraph_fonode :: (Int -> String) -> (Int -> String) -> (Int -> String) -> DGraph -> DGFONode -> String
show_dgraph_fonode foshow soshow efoshow dg (DGFONode id eout ein) = (foshow id) ++ ":\n\n\tOut:\n" ++ (concat . (fmap (show_dgraph_foedge_out foshow soshow efoshow dg . fromJust . getDGFOEdge dg)) $ eout) ++ "\n\tIn:\n" ++ (concat . (fmap (show_dgraph_foedge_in foshow soshow efoshow dg . fromJust . getDGFOEdge dg)) $ ein) ++ "\n"

show_dgraph_foedge_out :: (Int -> String) -> (Int -> String) -> (Int -> String) -> DGraph -> DGFOEdge -> String
show_dgraph_foedge_out foshow soshow efoshow dg (DGFOEdge id h ss t) = "\t\t" ++ (efoshow id) ++ "--" ++ (soshow h) ++ "->" ++ (foshow t) ++ "\n"

show_dgraph_foedge_in :: (Int -> String) -> (Int -> String) -> (Int -> String) -> DGraph -> DGFOEdge -> String
show_dgraph_foedge_in foshow soshow efoshow dg (DGFOEdge id h ss t) = "\t\t" ++ (efoshow id) ++ "<-" ++ (soshow h) ++ "--[" ++ (concat (intersperse "," (foshow <$> ss))) ++ "]\n"

instance Show DGraph where
	show = show_dgraph show show (\_ -> "") (\_ -> "")



-- Complex operations on the graph.
data DGraphOp = DGDeleteFONode Int | DGDeleteFOEdge Int | DGDeleteSONode Int | DGDeleteSOEdge Int deriving Eq

instance Ord DGraphOp where
	op1 <= op2 | dgraphop_prio op1 < dgraphop_prio op2 = True
	op1 <= op2 | dgraphop_prio op2 < dgraphop_prio op1 = False
	(DGDeleteFONode x) <= (DGDeleteFONode y) = x <= y
	(DGDeleteFOEdge x) <= (DGDeleteFOEdge y) = x <= y
	(DGDeleteSONode x) <= (DGDeleteSONode y) = x <= y
	(DGDeleteSOEdge x) <= (DGDeleteSOEdge y) = x <= y

dgraphop_prio :: DGraphOp -> Int
dgraphop_prio (DGDeleteFONode _) = 0
dgraphop_prio (DGDeleteFOEdge _) = -100
dgraphop_prio (DGDeleteSONode _) = 200
dgraphop_prio (DGDeleteSOEdge _) = -50

instance Operation DGraphOp DGraph where
	runOp dg (DGDeleteFONode x) = do_delete_fo_node dg x
	runOp dg (DGDeleteFOEdge x) = do_delete_fo_edge dg x
	runOp dg (DGDeleteSONode x) = do_delete_so_node dg x
	runOp dg (DGDeleteSOEdge x) = do_delete_so_edge dg x

do_delete_fo_node :: DGraph -> Int -> (DGraph,[DGraphOp])
do_delete_fo_node dg x = if (isNothing mb_node)
			then (dg,[])
			else (if ((Data.List.null ein) && (Data.List.null eout)) then ((lens_fonodes . (lens_idx x)) .~ Nothing $ dg,[]) else (dg,(DGDeleteFONode x):(DGDeleteFOEdge <$> (ein ++ eout))))
	where mb_node = getDGFONode dg x; (DGFONode _ ein eout) = fromJust mb_node

do_delete_fo_edge :: DGraph -> Int -> (DGraph,[DGraphOp])
do_delete_fo_edge dg x = if (isNothing mb_edge)
			then (dg,[])
			else ((lens_foedges . (lens_idx x)) .~ Nothing $ h_upd,[])
	where mb_edge = getDGFOEdge dg x; (DGFOEdge _ h ss t) = fromJust mb_edge;
		t_f_upd = (\(DGFONode pid pout pin) -> DGFONode pid pout (Data.List.filter (/= x) pin)); t_upd = (((lens_fonodes . (lens_idx t)) ..~) . fmap $ t_f_upd) $ dg;
		s_f_upd = (\(DGFONode pid pout pin) -> DGFONode pid (Data.List.filter (/= x) pout) pin); ss_upd = Data.List.foldr (\s -> ((lens_fonodes . (lens_idx s)) ..~) . fmap $ s_f_upd) t_upd ss;
		h_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid pout pin (Data.List.filter (/= x) pfh) psh); h_upd = (((lens_sonodes . (lens_idx h)) ..~) . fmap $ h_f_upd) $ ss_upd

do_delete_so_node :: DGraph -> Int -> (DGraph,[DGraphOp])
do_delete_so_node dg x = if (isNothing mb_node)
			then (dg,[])
			else (if ((Data.List.null ein) && (Data.List.null eout) && (Data.List.null efh) && (Data.List.null esh)) then ((lens_sonodes . (lens_idx x)) .~ Nothing $ dg,[]) else (dg,(DGDeleteSONode x):((DGDeleteSOEdge <$> (ein ++ eout)) ++ (DGDeleteFOEdge <$> efh) ++ (DGDeleteSOEdge <$> esh))))
	where mb_node = getDGSONode dg x; (DGSONode _ ein eout efh esh) = fromJust mb_node

do_delete_so_edge :: DGraph -> Int -> (DGraph,[DGraphOp])
do_delete_so_edge dg x = if (isNothing mb_edge)
			then (dg,[])
			else ((lens_soedges . (lens_idx x)) .~ Nothing $ h_upd,[])
	where mb_edge = getDGSOEdge dg x; (DGSOEdge _ h ss t) = fromJust mb_edge;
		t_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid pout (Data.List.filter (/= x) pin) pfh psh); t_upd = (((lens_sonodes . (lens_idx t)) ..~) . fmap $ t_f_upd) $ dg;
		s_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid (Data.List.filter (/= x) pout) pin pfh psh); ss_upd = Data.List.foldr (\s -> ((lens_sonodes . (lens_idx s)) ..~) . fmap $ s_f_upd) t_upd ss;
		h_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid pout pin pfh (Data.List.filter (/= x) psh)); h_upd = (((lens_sonodes . (lens_idx h)) ..~) . fmap $ h_f_upd) $ ss_upd


----------------------------------------------------------------------------------------------------------------------------------------------------
-- Dependency graph primitives
----------------------------------------------------------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------------------------------------------------------
-- Create a graph
emptyDG :: DGraph
emptyDG = DGraph [] [] [] []

----------------------------------------------------------------------------------------------------------------------------------------------------
-- Lookup

getDGFONode :: DGraph -> Int -> Maybe DGFONode
getDGFONode (DGraph fonodes _ _ _) i = join (fonodes !!? i)

getDGFOEdge :: DGraph -> Int -> Maybe DGFOEdge
getDGFOEdge (DGraph _ foedges _ _) i = join (foedges !!? i)

getDGSONode :: DGraph -> Int -> Maybe DGSONode
getDGSONode (DGraph _ _ sonodes _) i = join (sonodes !!? i)

getDGSOEdge :: DGraph -> Int -> Maybe DGSOEdge
getDGSOEdge (DGraph _ _ _ soedges) i = join (soedges !!? i)

-- Inline versions with the arguments flipped. These are particularly useful when we have indices that we wish to translate into nodes or edges by indicating the graph in an inline way while using lenses, for example.

(?@) :: Int -> DGraph -> Maybe DGFONode
(?@) = flip getDGFONode
infix 8 ?@

(?-) :: Int -> DGraph -> Maybe DGFOEdge
(?-) = flip getDGFOEdge
infix 8 ?-

(?@@) :: Int -> DGraph -> Maybe DGSONode
(?@@) = flip getDGSONode
infix 8 ?@@

(?--) :: Int -> DGraph -> Maybe DGSOEdge
(?--) = flip getDGSOEdge
infix 8 ?--

----------------------------------------------------------------------------------------------------------------------------------------------------
-- Create new nodes

newDGFONode :: State DGraph Int
newDGFONode = state (\(DGraph fonodes foedges sonodes soedges) -> (length fonodes,DGraph (fonodes ++ [Just (DGFONode (length fonodes) [] [])]) foedges sonodes soedges))

newDGSONode :: State DGraph Int
newDGSONode = state (\(DGraph fonodes foedges sonodes soedges) -> (length sonodes,DGraph fonodes foedges (sonodes ++ [Just (DGSONode (length sonodes) [] [] [] [])]) soedges))

----------------------------------------------------------------------------------------------------------------------------------------------------
-- Create edges

-- Head, sources and target
newDGFOEdge :: Int -> [Int] -> Int -> State DGraph Int
newDGFOEdge h ss t = state (f_newDGFOEdge h ss t)

f_newDGFOEdge :: Int -> [Int] -> Int -> (DGraph -> (Int,DGraph))
f_newDGFOEdge h ss t (DGraph fonodes foedges sonodes soedges) = (idx,foedges_upd)
	where 
		idx = length foedges;
		s_f_upd = (\(DGFONode pid pout pin) -> DGFONode pid (idx:pout) pin); s_t_upd_f = (\idx -> MTraversal (lens_idx idx)); s_t_upd = lens_fonodes . (runMTraversal (foldMap s_t_upd_f ss)); s_upd = ((s_t_upd ..~) . fmap $ s_f_upd) $ (DGraph fonodes foedges sonodes soedges);
		t_f_upd = (\(DGFONode pid pout pin) -> DGFONode pid pout (idx:pin)); t_t_upd = lens_fonodes . (lens_idx t); t_upd = ((t_t_upd ..~) . fmap $ t_f_upd) $ s_upd;
		h_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid pout pin (idx:pfh) psh); h_t_upd = lens_sonodes . (lens_idx h); h_upd = ((h_t_upd ..~) . fmap $ h_f_upd) $ t_upd;
		foedges_f_upd = (\l -> l ++ [Just (DGFOEdge idx h ss t)]); foedges_upd = lens_foedges ..~ foedges_f_upd $ h_upd

newDGSOEdge :: Int -> [Int] -> Int -> State DGraph Int
newDGSOEdge h ss t = state (f_newDGSOEdge h ss t)

f_newDGSOEdge :: Int -> [Int] -> Int -> (DGraph -> (Int,DGraph))
f_newDGSOEdge h ss t (DGraph fonodes foedges sonodes soedges) = (idx,soedges_upd)
	where 
		idx = length soedges;
		s_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid (idx:pout) pin pfh psh); s_t_upd_f = (\idx -> MTraversal (lens_idx idx)); s_t_upd = lens_sonodes . (runMTraversal (foldMap s_t_upd_f ss)); s_upd = ((s_t_upd ..~) . fmap $ s_f_upd) $ (DGraph fonodes foedges sonodes soedges);
		t_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid pout (idx:pin) pfh psh); t_t_upd = lens_sonodes . (lens_idx t); t_upd = ((t_t_upd ..~) . fmap $ t_f_upd) $ s_upd;
		h_f_upd = (\(DGSONode pid pout pin pfh psh) -> DGSONode pid pout pin pfh (idx:psh)); h_t_upd = lens_sonodes . (lens_idx h); h_upd = ((h_t_upd ..~) . fmap $ h_f_upd) $ t_upd;
		soedges_f_upd = (\l -> l ++ [Just (DGSOEdge idx h ss t)]); soedges_upd = lens_soedges ..~ soedges_f_upd $ h_upd


----------------------------------------------------------------------------------------------------------------------------------------------------
-- Delete nodes

deleteDGFONode :: Int -> State DGraph ()
deleteDGFONode x = state (\dg -> ((),runOps ((emptyOp dg) <+ (DGDeleteFONode x))))

deleteDGSONode :: Int -> State DGraph ()
deleteDGSONode x = state (\dg -> ((),runOps ((emptyOp dg) <+ (DGDeleteSONode x))))

----------------------------------------------------------------------------------------------------------------------------------------------------
-- Delete edges

deleteDGFOEdge :: Int -> State DGraph ()
deleteDGFOEdge x = state (\dg -> ((),runOps ((emptyOp dg) <+ (DGDeleteFOEdge x))))

deleteDGSOEdge :: Int -> State DGraph ()
deleteDGSOEdge x = state (\dg -> ((),runOps ((emptyOp dg) <+ (DGDeleteSOEdge x))))



-- Support for equivalence classes on top of a dependency graph. This is built on top, but it is a direct extension of Dependency Graphs, that is why it goes here.
-- This datatype supports essentially the same operations as DGraph (but directly on elements of the corresponding type), plus merging of nodes. Deletion of nodes is not supported (even though in principle it could), for simplicity reasons, and because it is not really needed. Neither of elements (because once elements are merged they can never be separated again) nor of entire equivalence classes (because just do not access that equivalence class). Deletion of edges is, however, indeed supported; and for that reason, we add utility edge search functions that, given at least a source, a head or a target, and possibly all of them, return all edges that match the given criteria.
-- As shown in the functions below, this datatype is meant to be used with ST on top of it, and with the s parameter forall quantified. Just use runST when you're done with it.
-- The nodes maps are only guaranteed to be defined for the representative elements of each equivalence class. More importantly, the information in the Map is only guaranteed to be correct if applied to the representative elements. This allows us to merge equivalence classes while only updating the Map's entry for the representative element.
-- Use the getEqDGFONode and getEqDGSONode to get correct information without having to manually do this yourself.
-- The edges maps are to keep an updated map when edges are re-added so that old identifiers are still usable after updating the graph.
data EqDGraph s fot sot = EqDGraph {eqdgraph :: DGraph, eqdg_fopoints :: Map fot fot, eqdg_fonodes :: Map fot Int, eqdg_foelements :: Map Int [fot], eqdg_sopoints :: Map sot sot, eqdg_sonodes :: Map sot Int, eqdg_soelements :: Map Int [sot], eqdg_foedges :: Map Int Int, eqdg_soedges :: Map Int Int, eqdg_fomerges :: Map Int Int, eqdg_somerges :: Map Int Int, eqdg_redundant_foedges :: Map Int Bool, eqdg_redundant_soedges :: Map Int Bool}
-- The thing below seems to not be supported by GHCi for now.
--type UseEqDGraph fot sot = forall s. ST s (EqDGraph s fot sot)

lens_eqdgraph :: Lens' (EqDGraph s fot sot) DGraph
lens_eqdgraph f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rdgraph -> EqDGraph rdgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) (f dgraph)

lens_eqdg_fopoints :: Lens' (EqDGraph s fot sot) (Map fot fot)
lens_eqdg_fopoints f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rfopoints -> EqDGraph dgraph rfopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) (f fopoints)

lens_eqdg_fonodes :: Lens' (EqDGraph s fot sot) (Map fot Int)
lens_eqdg_fonodes f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rfonodes -> EqDGraph dgraph fopoints rfonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) (f fonodes)

lens_eqdg_foelements :: Lens' (EqDGraph s fot sot) (Map Int [fot])
lens_eqdg_foelements f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rfoelements -> EqDGraph dgraph fopoints fonodes rfoelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) (f foelements)

lens_eqdg_sopoints :: Lens' (EqDGraph s fot sot) (Map sot sot)
lens_eqdg_sopoints f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rsopoints -> EqDGraph dgraph fopoints fonodes foelements rsopoints sonodes soelements foedges soedges fomerges somerges fored sored) (f sopoints)

lens_eqdg_sonodes :: Lens' (EqDGraph s fot sot) (Map sot Int)
lens_eqdg_sonodes f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rsonodes -> EqDGraph dgraph fopoints fonodes foelements sopoints rsonodes soelements foedges soedges fomerges somerges fored sored) (f sonodes)

lens_eqdg_soelements :: Lens' (EqDGraph s fot sot) (Map Int [sot])
lens_eqdg_soelements f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rsoelements -> EqDGraph dgraph fopoints fonodes foelements sopoints sonodes rsoelements foedges soedges fomerges somerges fored sored) (f soelements)

lens_eqdg_foedges :: Lens' (EqDGraph s fot sot) (Map Int Int)
lens_eqdg_foedges f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rfoedges -> EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements rfoedges soedges fomerges somerges fored sored) (f foedges)

lens_eqdg_soedges :: Lens' (EqDGraph s fot sot) (Map Int Int)
lens_eqdg_soedges f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rsoedges -> EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges rsoedges fomerges somerges fored sored) (f soedges)

lens_eqdg_fomerges :: Lens' (EqDGraph s fot sot) (Map Int Int)
lens_eqdg_fomerges f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rfomerges -> EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges rfomerges somerges fored sored) (f fomerges)

lens_eqdg_somerges :: Lens' (EqDGraph s fot sot) (Map Int Int)
lens_eqdg_somerges f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rsomerges -> EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges rsomerges fored sored) (f somerges)

lens_eqdg_fored :: Lens' (EqDGraph s fot sot) (Map Int Bool)
lens_eqdg_fored f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rfored -> EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges rfored sored) (f fored)

lens_eqdg_sored :: Lens' (EqDGraph s fot sot) (Map Int Bool)
lens_eqdg_sored f (EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored sored) = fmap (\rsored -> EqDGraph dgraph fopoints fonodes foelements sopoints sonodes soelements foedges soedges fomerges somerges fored rsored) (f sored)



show_eqdgraph :: (Show fot, Show sot) => EqDGraph s fot sot -> String
show_eqdgraph eqdg = (show_dgraph foshow soshow efoshow esoshow (eqdgraph eqdg)) where foshow = (\foi -> (show foi) ++ "(FO):: " ++ (show (findWithDefault [] foi (eqdg_foelements eqdg)))); soshow = (\soi -> (show soi) ++ "(SO):: " ++ (show (findWithDefault [] soi (eqdg_soelements eqdg)))); efoshow = (\foei -> if (findWithDefault False foei (eqdg_redundant_foedges eqdg)) then "[R]" else "[NR]"); esoshow = (\soei -> if (findWithDefault False soei (eqdg_redundant_soedges eqdg)) then "[R]" else "[NR]")

-- An alternative version that dumps the entire map structure for debugging purposes
dump_eqdgraph :: (Show fot, Show sot) => EqDGraph s fot sot -> ST s String
dump_eqdgraph eqdg = do
	{
		let {gstr = show_eqdgraph eqdg};

		let {lfopoints = toList (eqdg_fopoints eqdg)};
		--let {ffopoints = (\(fot,point) -> do {rp <- descriptor point; return ("(" ++ (show fot) ++ "," ++ (show rp) ++ ")")})};
		let {ffopoints = return . show};
		strfopoints <- show <$> traverse ffopoints lfopoints;

		let {lfonodes = toList (eqdg_fonodes eqdg)};
		let {ffonodes = return . show};
		strfonodes <- show <$> traverse ffonodes lfonodes;

		let {lfoelements = toList (eqdg_foelements eqdg)};
		let {ffoelements = return . show};
		strfoelements <- show <$> traverse ffoelements lfoelements;

		let {lsopoints = toList (eqdg_sopoints eqdg)};
		--let {fsopoints = (\(sot,point) -> do {rp <- descriptor point; return ("(" ++ (show sot) ++ "," ++ (show rp) ++ ")")})};
		let {fsopoints = return . show};
		strsopoints <- show <$> traverse fsopoints lsopoints;

		let {lsonodes = toList (eqdg_sonodes eqdg)};
		let {fsonodes = return . show};
		strsonodes <- show <$> traverse fsonodes lsonodes;

		let {lsoelements = toList (eqdg_soelements eqdg)};
		let {fsoelements = return . show};
		strsoelements <- show <$> traverse fsoelements lsoelements;

		let {lfoedges = toList (eqdg_foedges eqdg)};
		let {ffoedges = return . show};
		strfoedges <- show <$> traverse ffoedges lfoedges;

		let {lsoedges = toList (eqdg_soedges eqdg)};
		let {fsoedges = return . show};
		strsoedges <- show <$> traverse fsoedges lsoedges;

		let {lfomerges = toList (eqdg_fomerges eqdg)};
		let {ffomerges = return . show};
		strfomerges <- show <$> traverse ffomerges lfomerges;

		let {lsomerges = toList (eqdg_somerges eqdg)};
		let {fsomerges = return . show};
		strsomerges <- show <$> traverse fsomerges lsomerges;

		let {lredfoedges = toList (eqdg_redundant_foedges eqdg)};
		let {fredfoedges = return . show};
		strredfoedges <- show <$> traverse fredfoedges lredfoedges;

		let {lredsoedges = toList (eqdg_redundant_soedges eqdg)};
		let {fredsoedges = return . show};
		strredsoedges <- show <$> traverse fredsoedges lredsoedges;

		let {rstr = "GRAPH:\n\n" ++ gstr ++ "\n\nFOPOINTS:\n\n" ++ strfopoints ++ "\n\nFONODES:\n\n" ++ strfonodes ++ "\n\nFOELEMENTS:\n\n" ++ strfoelements ++ "\n\nSOPOINTS:\n\n" ++ strsopoints ++ "\n\nSONODES:\n\n" ++ strsonodes ++ "\n\nSOELEMENTS:\n\n" ++ strsoelements ++ "\n\nFOEDGES:\n\n" ++ strfoedges ++ "\n\nSOEDGES:\n\n" ++ strsoedges ++ "\n\nFOMERGES:\n\n" ++ strfomerges ++ "\n\nSOMERGES:\n\n" ++ strsomerges ++ "\n\nREDUNDANT FOEDGES:\n\n" ++ strredfoedges ++ "\n\nREDUNDANT SOEDGES:\n\n" ++ strredsoedges};

		return rstr
	}

st_dump_eqdgraph :: (Show fot, Show sot) => StateT (EqDGraph s fot sot) (ST s) String
st_dump_eqdgraph = StateT (\eqdg -> do {str <- dump_eqdgraph eqdg; return (str,eqdg)})


-- All of the functions dealing with EqDGraphs are stateful, so that we can optimize the equivalence class handling. They are going to be used in a stateful way anyway.
emptyEqDG :: EqDGraph s fot sot
emptyEqDG = EqDGraph emptyDG Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty Data.Map.Strict.empty

getEqDGFORId :: EqDGraph s fot sot -> Int -> Int
getEqDGFORId eqdg id = if (rid == id) then rid else (getEqDGFORId eqdg rid) where rid = findWithDefault id id (eqdg_fomerges eqdg)

getEqDGSORId :: EqDGraph s fot sot -> Int -> Int
getEqDGSORId eqdg id = if (rid == id) then rid else (getEqDGSORId eqdg rid) where rid = findWithDefault id id (eqdg_somerges eqdg)

getEqDGFOPoint :: (Ord fot, Eq fot) => EqDGraph s fot sot -> fot -> Maybe fot
getEqDGFOPoint eqdg fot = if (isNothing mb_rfot) then Nothing else (if (rfot == fot) then (Just rfot) else (getEqDGFOPoint eqdg rfot)) where mb_rfot = eqdg_fopoints eqdg !? fot; rfot = fromJust mb_rfot

getEqDGSOPoint :: (Ord sot, Eq sot) => EqDGraph s fot sot -> sot -> Maybe sot
getEqDGSOPoint eqdg sot = if (isNothing mb_rsot) then Nothing else (if (rsot == sot) then (Just rsot) else (getEqDGSOPoint eqdg rsot)) where mb_rsot = eqdg_sopoints eqdg !? sot; rsot = fromJust mb_rsot

getEqDGFONode :: Ord fot => EqDGraph s fot sot -> fot -> ST s (Maybe Int)
--getEqDGFONode eqdg fot = node where mb_pt = (eqdg_fopoints eqdg) !? fot; desc = traverse descriptor mb_pt; node = desc >>= (\mb_desc -> return (((eqdg_fonodes eqdg) !?) =<< mb_desc))
getEqDGFONode eqdg fot = node where mb_pt = getEqDGFOPoint eqdg fot; desc = return mb_pt; node = desc >>= (\mb_desc -> return (((eqdg_fonodes eqdg) !?) =<< mb_desc))

st_getEqDGFONode :: Ord fot => fot -> StateT (EqDGraph s fot sot) (ST s) (Maybe Int)
st_getEqDGFONode fot = StateT (f_getEqDGFONode fot)

f_getEqDGFONode :: Ord fot => fot -> (EqDGraph s fot sot -> ST s (Maybe Int, EqDGraph s fot sot))
f_getEqDGFONode fot eqdg = (,eqdg) <$> stmb_int where stmb_int = getEqDGFONode eqdg fot

getEqDGSONode :: Ord sot => EqDGraph s fot sot -> sot -> ST s (Maybe Int)
getEqDGSONode eqdg sot = do
	{
		gtraceM False "GETEQDGSONODE";
		gtraceM False ("MB_PT: " ++ (show (isJust mb_pt)) ++ "\n");
		mb_desc <- desc;
		gtraceM False ("DESC: " ++ (show (isJust mb_desc)) ++ "\n");
		mb_node <- node;
		gtraceM False ("NODE: " ++ (show (isJust mb_node)) ++ "\n");
		node
	}
	--where mb_pt = (eqdg_sopoints eqdg) !? sot; desc = traverse descriptor mb_pt; node = desc >>= (\mb_desc -> return (((eqdg_sonodes eqdg) !?) =<< mb_desc))
	where mb_pt = getEqDGSOPoint eqdg sot; desc = return mb_pt; node = desc >>= (\mb_desc -> return (((eqdg_sonodes eqdg) !?) =<< mb_desc))

st_getEqDGSONode :: Ord sot => sot -> StateT (EqDGraph s fot sot) (ST s) (Maybe Int)
st_getEqDGSONode sot = StateT (f_getEqDGSONode sot)

f_getEqDGSONode :: Ord sot => sot -> (EqDGraph s fot sot -> ST s (Maybe Int, EqDGraph s fot sot))
f_getEqDGSONode sot eqdg = (,eqdg) <$> stmb_int where stmb_int = getEqDGSONode eqdg sot

getEqDGFORep :: Ord fot => EqDGraph s fot sot -> Int -> ST s (Maybe fot)
--getEqDGFORep eqdg id = desc where rid = getEqDGFORId eqdg id; mb_els = (eqdg_foelements eqdg) !? rid; mb_el = mb_els >>= headMay; mb_pt = mb_el >>= ((eqdg_fopoints eqdg) !?); desc = traverse descriptor mb_pt
getEqDGFORep eqdg id = desc where rid = getEqDGFORId eqdg id; mb_els = (eqdg_foelements eqdg) !? rid; mb_el = mb_els >>= headMay; mb_pt = mb_el >>= (getEqDGFOPoint eqdg); desc = return mb_pt

st_getEqDGFORep :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) (Maybe fot)
st_getEqDGFORep id = StateT (f_getEqDGFORep id)

f_getEqDGFORep :: Ord fot => Int -> (EqDGraph s fot sot -> ST s (Maybe fot, EqDGraph s fot sot))
f_getEqDGFORep id eqdg = (,eqdg) <$> stmb_int where stmb_int = getEqDGFORep eqdg id

getEqDGSORep :: Ord sot => EqDGraph s fot sot -> Int -> ST s (Maybe sot)
--getEqDGSORep eqdg id = desc where rid = getEqDGSORId eqdg id; mb_els = (eqdg_soelements eqdg) !? rid; mb_el = mb_els >>= headMay; mb_pt = mb_el >>= ((eqdg_sopoints eqdg) !?); desc = traverse descriptor mb_pt
getEqDGSORep eqdg id = desc where rid = getEqDGSORId eqdg id; mb_els = (eqdg_soelements eqdg) !? rid; mb_el = mb_els >>= headMay; mb_pt = mb_el >>= (getEqDGSOPoint eqdg); desc = return mb_pt

st_getEqDGSORep :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) (Maybe sot)
st_getEqDGSORep id = StateT (f_getEqDGSORep id)

f_getEqDGSORep :: Ord sot => Int -> (EqDGraph s fot sot -> ST s (Maybe sot, EqDGraph s fot sot))
f_getEqDGSORep id eqdg = (,eqdg) <$> stmb_int where stmb_int = getEqDGSORep eqdg id

add_to_maplist :: Ord k => k -> a -> Map k [a] -> Map k [a]
add_to_maplist k a m = case (m !? k) of {Nothing -> Data.Map.Strict.insert k [a] m; Just l -> Data.Map.Strict.insert k (a:l) m}

-- From now on, we use relative identifiers for nodes, so that we can indistinctively use the labels or the ids.
-- Note that Int is the preferred identifier here. So that we can reference nodes with no terms in them.
-- This means that anywhere that we can use Int, we can use fot; but there may be places where we can use fot and we need to be careful to use fot, because if the node is empty then it will raise an exception. For example, when merging equivalence classes.

-- We unfortunately need to wrap stuff with newtypes to prevent instance overlaps.
newtype EqDGFoId = EqDGFoId {fromEqDGFoId :: Int} deriving (Eq,Show)
newtype EqDGSoId = EqDGSoId {fromEqDGSoId :: Int} deriving (Eq,Show)

instance Ord fot => STRelativeIso (ST s) (EqDGraph s fot sot) EqDGFoId fot where
	strelfw = st_getEqDGFORep . fromEqDGFoId
	strelbw = (EqDGFoId <$>) . doGetEqDGFONode

instance Ord fot => RelativeIso (StateT (EqDGraph s fot sot) (ST s)) (EqDGraph s fot sot) EqDGFoId fot where
	relfw c = ((fromSTRII <$>) <$>) . (relfw c) . STRII
	relbw c = (fromSTRII <$>) . (relbw c) . STRII

instance Ord sot => STRelativeIso (ST s) (EqDGraph s fot sot) EqDGSoId sot where
	strelfw = st_getEqDGSORep . fromEqDGSoId
	strelbw = (EqDGSoId <$>) . doGetEqDGSONode

instance Ord sot => RelativeIso (StateT (EqDGraph s fot sot) (ST s)) (EqDGraph s fot sot) EqDGSoId sot where
	relfw c = ((fromSTRII <$>) <$>) . (relfw c) . STRII
	relbw c = (fromSTRII <$>) . (relbw c) . STRII


type EqDGRelFoId s fot sot = RelativeId (StateT (EqDGraph s fot sot) (ST s)) (EqDGraph s fot sot) EqDGFoId
type EqDGRelSoId s fot sot = RelativeId (StateT (EqDGraph s fot sot) (ST s)) (EqDGraph s fot sot) EqDGSoId

getSTRelativeEqDGFoId :: Ord fot => EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Int
getSTRelativeEqDGFoId relid = fromEqDGFoId <$> (getSTRelativeId relid)

getSTRelativeEqDGSoId :: Ord sot => EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Int
getSTRelativeEqDGSoId relid = fromEqDGSoId <$> (getSTRelativeId relid)

getSTRelativeEqDGFoCoId :: Ord fot => EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) (Maybe fot)
getSTRelativeEqDGFoCoId = getSTRelativeCoId

getSTRelativeEqDGSoCoId :: Ord sot => EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) (Maybe sot)
getSTRelativeEqDGSoCoId = getSTRelativeCoId

compareEqDGFoId :: Ord fot => EqDGraph s fot sot -> EqDGFoId -> EqDGFoId -> Bool
compareEqDGFoId eqdg a b = (getEqDGFORId eqdg (fromEqDGFoId a)) == (getEqDGFORId eqdg (fromEqDGFoId b))

compareEqDGSoId :: Ord fot => EqDGraph s fot sot -> EqDGSoId -> EqDGSoId -> Bool
compareEqDGSoId eqdg a b = (getEqDGSORId eqdg (fromEqDGSoId a)) == (getEqDGSORId eqdg (fromEqDGSoId b))

eqSTRelativeEqDGFoIds :: Ord fot => EqDGRelFoId s fot sot -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Bool
eqSTRelativeEqDGFoIds a b = StateT (\eqdg -> runStateT (compareSTRelativeIds (compareEqDGFoId eqdg) a b) eqdg)

eqSTRelativeEqDGSoIds :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Bool
eqSTRelativeEqDGSoIds a b = StateT (\eqdg -> runStateT (compareSTRelativeIds (compareEqDGSoId eqdg) a b) eqdg)

directEqDGFoId :: Int -> EqDGRelFoId s fot sot
directEqDGFoId = DirectId . EqDGFoId

directEqDGSoId :: Int -> EqDGRelSoId s fot sot
directEqDGSoId = DirectId . EqDGSoId

relbwEqDGFoId :: Ord fot => fot -> EqDGRelFoId s fot sot
relbwEqDGFoId = RelBwId

relbwEqDGSoId :: Ord sot => sot -> EqDGRelSoId s fot sot
relbwEqDGSoId = RelBwId

getCurEqDGFOEdge :: Ord fot => EqDGraph s fot sot -> Int -> Int
getCurEqDGFOEdge eqdg eid = if (m == eid) then eid else (getCurEqDGFOEdge eqdg m) where m = findWithDefault eid eid (eqdg_foedges eqdg)

st_getCurEqDGFOEdge :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) Int
st_getCurEqDGFOEdge eid = StateT (\eqdg -> return (getCurEqDGFOEdge eqdg eid,eqdg))

--f_getCurEqDGFOEdge :: Ord fot => Int -> (EqDGraph s fot sot -> ST s (Int,EqDGraph s fot sot))
--f_getCurEqDGFOEdge eid eqdg = if (m == eid) then (return (eid,eqdg)) else (f_getCurEqDGFOEdge m eqdg) where m = findWithDefault eid eid (eqdg_foedges eqdg)

getCurEqDGSOEdge :: Ord sot => EqDGraph s fot sot -> Int -> Int
getCurEqDGSOEdge eqdg eid = if (m == eid) then eid else (getCurEqDGSOEdge eqdg m) where m = findWithDefault eid eid (eqdg_soedges eqdg)

st_getCurEqDGSOEdge :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) Int
st_getCurEqDGSOEdge eid = StateT (\eqdg -> return (getCurEqDGSOEdge eqdg eid,eqdg))

--f_getCurEqDGSOEdge :: Ord fot => Int -> (EqDGraph s fot sot -> ST s (Int,EqDGraph s fot sot))
--f_getCurEqDGSOEdge eid eqdg = if (m == eid) then (return (eid,eqdg)) else (f_getCurEqDGSOEdge m eqdg) where m = findWithDefault eid eid (eqdg_soedges eqdg)


-- Using the functions for navigating the graph nodes and edges with relative ids
checkEqDGFOEdge :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) Bool
checkEqDGFOEdge eid = StateT (\eqdg -> return (f_checkEqDGFOEdge eid eqdg))

f_checkEqDGFOEdge :: Ord fot => Int -> (EqDGraph s fot sot -> (Bool,EqDGraph s fot sot))
f_checkEqDGFOEdge eid eqdg = ((isJust mb_edge) && (not red),eqdg) where reid = getCurEqDGFOEdge eqdg eid; mb_edge = getDGFOEdge (eqdgraph eqdg) reid; red = findWithDefault False reid (eqdg_redundant_foedges eqdg)

checkAllEqDGFOEdge :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) Bool
checkAllEqDGFOEdge eid = StateT (\eqdg -> return (f_checkAllEqDGFOEdge eid eqdg))

f_checkAllEqDGFOEdge :: Ord fot => Int -> (EqDGraph s fot sot -> (Bool,EqDGraph s fot sot))
f_checkAllEqDGFOEdge eid eqdg = (isJust mb_edge,eqdg) where reid = getCurEqDGFOEdge eqdg eid; mb_edge = getDGFOEdge (eqdgraph eqdg) reid

eqDGFOEdge_head :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
eqDGFOEdge_head eid = StateT (\eqdg -> return (f_eqDGFOEdge_head eid eqdg))

f_eqDGFOEdge_head :: Ord fot => Int -> (EqDGraph s fot sot -> (EqDGRelSoId s fot sot, EqDGraph s fot sot))
f_eqDGFOEdge_head eid eqdg = (directEqDGSoId headid, eqdg) where reid = getCurEqDGFOEdge eqdg eid; edge = fromJustErr ("Edge with id " ++ (show eid) ++ " could not be found.") (getDGFOEdge (eqdgraph eqdg) reid); headid = edge ^. lens_dgfoedge_head

eqDGFOEdge_sources :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) [EqDGRelFoId s fot sot]
eqDGFOEdge_sources eid = StateT (\eqdg -> return (f_eqDGFOEdge_sources eid eqdg))

f_eqDGFOEdge_sources :: Ord fot => Int -> (EqDGraph s fot sot -> ([EqDGRelFoId s fot sot], EqDGraph s fot sot))
f_eqDGFOEdge_sources eid eqdg = (directEqDGFoId <$> sids, eqdg) where reid = getCurEqDGFOEdge eqdg eid; edge = fromJustErr ("Edge with id " ++ (show eid) ++ " could not be found.") (getDGFOEdge (eqdgraph eqdg) reid); sids = edge ^. lens_dgfoedge_sources

eqDGFOEdge_target :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelFoId s fot sot)
eqDGFOEdge_target eid = StateT (\eqdg -> return (f_eqDGFOEdge_target eid eqdg))

f_eqDGFOEdge_target :: Ord fot => Int -> (EqDGraph s fot sot -> (EqDGRelFoId s fot sot, EqDGraph s fot sot))
f_eqDGFOEdge_target eid eqdg = (directEqDGFoId tid, eqdg) where reid = getCurEqDGFOEdge eqdg eid; edge = fromJustErr ("Edge with id " ++ (show eid) ++ " could not be found.") (getDGFOEdge (eqdgraph eqdg) reid); tid = edge ^. lens_dgfoedge_target

checkEqDGSOEdge :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) Bool
checkEqDGSOEdge eid = StateT (\eqdg -> return (f_checkEqDGSOEdge eid eqdg))

f_checkEqDGSOEdge :: Ord sot => Int -> (EqDGraph s fot sot -> (Bool,EqDGraph s fot sot))
f_checkEqDGSOEdge eid eqdg = ((isJust mb_edge) && (not red),eqdg) where reid = getCurEqDGSOEdge eqdg eid; mb_edge = getDGSOEdge (eqdgraph eqdg) reid; red = findWithDefault False reid (eqdg_redundant_soedges eqdg)

checkAllEqDGSOEdge :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) Bool
checkAllEqDGSOEdge eid = StateT (\eqdg -> return (f_checkAllEqDGSOEdge eid eqdg))

f_checkAllEqDGSOEdge :: Ord sot => Int -> (EqDGraph s fot sot -> (Bool,EqDGraph s fot sot))
f_checkAllEqDGSOEdge eid eqdg = (isJust mb_edge,eqdg) where reid = getCurEqDGSOEdge eqdg eid; mb_edge = getDGSOEdge (eqdgraph eqdg) reid

eqDGSOEdge_head :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
eqDGSOEdge_head eid = StateT (\eqdg -> return (f_eqDGSOEdge_head eid eqdg))

f_eqDGSOEdge_head :: Ord sot => Int -> (EqDGraph s fot sot -> (EqDGRelSoId s fot sot, EqDGraph s fot sot))
f_eqDGSOEdge_head eid eqdg = (directEqDGSoId hid, eqdg) where reid = getCurEqDGSOEdge eqdg eid; edge = fromJustErr ("Edge with id " ++ (show eid) ++ " could not be found.") (getDGSOEdge (eqdgraph eqdg) reid); hid = edge ^. lens_dgsoedge_head

eqDGSOEdge_sources :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) [EqDGRelSoId s fot sot]
eqDGSOEdge_sources eid = StateT (\eqdg -> return (f_eqDGSOEdge_sources eid eqdg))

f_eqDGSOEdge_sources :: Ord sot => Int -> (EqDGraph s fot sot -> ([EqDGRelSoId s fot sot], EqDGraph s fot sot))
f_eqDGSOEdge_sources eid eqdg = (directEqDGSoId <$> sids, eqdg) where reid = getCurEqDGSOEdge eqdg eid; edge = fromJustErr ("Edge with id " ++ (show eid) ++ " could not be found.") (getDGSOEdge (eqdgraph eqdg) reid); sids = edge ^. lens_dgsoedge_sources

eqDGSOEdge_target :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
eqDGSOEdge_target eid = StateT (\eqdg -> return (f_eqDGSOEdge_target eid eqdg))

f_eqDGSOEdge_target :: Ord sot => Int -> (EqDGraph s fot sot -> (EqDGRelSoId s fot sot, EqDGraph s fot sot))
f_eqDGSOEdge_target eid eqdg = (directEqDGSoId tid, eqdg) where reid = getCurEqDGSOEdge eqdg eid; edge = fromJustErr ("Edge with id " ++ (show eid) ++ " could not be found.") (getDGSOEdge (eqdgraph eqdg) reid); tid = edge ^. lens_dgsoedge_target



raw_newEqDGFONode :: Ord fot => fot -> StateT (EqDGraph s fot sot) (ST s) Int
raw_newEqDGFONode fot = StateT (f_raw_newEqDGFONode fot)

f_raw_newEqDGFONode :: Ord fot => fot -> (EqDGraph s fot sot -> ST s (Int, EqDGraph s fot sot))
--f_raw_newEqDGFONode fot eqdg = do {apt <- fresh fot; let {with_st = mzoom lens_eqdgraph newDGFONode; (nn,eqdg1) = runState with_st eqdg; eqdg2 = lens_eqdg_fopoints ..~ Data.Map.Strict.insert fot apt $ eqdg1; eqdg3 = lens_eqdg_fonodes ..~ Data.Map.Strict.insert fot nn $ eqdg2; eqdg4 = lens_eqdg_foelements ..~ (add_to_maplist nn fot) $ eqdg3}; return (nn,eqdg4)}
f_raw_newEqDGFONode fot eqdg = do {let {with_st = mzoom lens_eqdgraph newDGFONode; (nn,eqdg1) = runState with_st eqdg; eqdg2 = lens_eqdg_fopoints ..~ Data.Map.Strict.insert fot fot $ eqdg1; eqdg3 = lens_eqdg_fonodes ..~ Data.Map.Strict.insert fot nn $ eqdg2; eqdg4 = lens_eqdg_foelements ..~ (add_to_maplist nn fot) $ eqdg3}; return (nn,eqdg4)}

-- Creates the node if necessary.
doGetEqDGFONode :: Ord fot => fot -> StateT (EqDGraph s fot sot) (ST s) Int
doGetEqDGFONode fot = StateT (\eqdg -> do {mb_exist <- getEqDGFONode eqdg fot; if (isNothing mb_exist) then (runStateT (raw_newEqDGFONode fot) eqdg) else (return (fromJust mb_exist,eqdg))})

newEqDGFONode :: Ord fot => fot -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelFoId s fot sot)
newEqDGFONode fot = directEqDGFoId <$> (doGetEqDGFONode fot)

-- Create a new anonymous node and return its identifier
newAnonEqDGFONode :: StateT (EqDGraph s fot sot) (ST s) (EqDGRelFoId s fot sot)
newAnonEqDGFONode = directEqDGFoId <$> raw_newAnonEqDGFONode

raw_newAnonEqDGFONode :: StateT (EqDGraph s fot sot) (ST s) Int
raw_newAnonEqDGFONode = StateT (\eqdg -> return (f_newAnonEqDGFONode eqdg))

f_newAnonEqDGFONode :: EqDGraph s fot sot -> (Int, EqDGraph s fot sot)
f_newAnonEqDGFONode eqdg = (nn,eqdg1) where with_st = mzoom lens_eqdgraph newDGFONode; (nn,eqdg1) = runState with_st eqdg

raw_newEqDGSONode :: Ord sot => sot -> StateT (EqDGraph s fot sot) (ST s) Int
raw_newEqDGSONode sot = StateT (f_raw_newEqDGSONode sot)

f_raw_newEqDGSONode :: Ord sot => sot -> (EqDGraph s fot sot -> ST s (Int, EqDGraph s fot sot))
--f_raw_newEqDGSONode sot eqdg = do {apt <- (fresh sot); let {with_st = (mzoom lens_eqdgraph newDGSONode); (nn,eqdg1) = (runState with_st eqdg); eqdg2 = (lens_eqdg_sopoints ..~ Data.Map.Strict.insert sot apt $ eqdg1); eqdg3 = (lens_eqdg_sonodes ..~ Data.Map.Strict.insert sot nn $ eqdg2); eqdg4 = (lens_eqdg_soelements ..~ (add_to_maplist nn sot) $ eqdg3)}; (return (nn,eqdg4))}
f_raw_newEqDGSONode sot eqdg = do {let {with_st = (mzoom lens_eqdgraph newDGSONode); (nn,eqdg1) = (runState with_st eqdg); eqdg2 = (lens_eqdg_sopoints ..~ Data.Map.Strict.insert sot sot $ eqdg1); eqdg3 = (lens_eqdg_sonodes ..~ Data.Map.Strict.insert sot nn $ eqdg2); eqdg4 = (lens_eqdg_soelements ..~ (add_to_maplist nn sot) $ eqdg3)}; (return (nn,eqdg4))}

-- Creates the node if necessary.
doGetEqDGSONode :: Ord sot => sot -> StateT (EqDGraph s fot sot) (ST s) Int
doGetEqDGSONode sot = StateT (\eqdg -> do
	{
		mb_exist <- getEqDGSONode eqdg sot;
		if (isNothing mb_exist) then (runStateT (raw_newEqDGSONode sot) eqdg) else (return (fromJust mb_exist,eqdg))
	})

newEqDGSONode :: Ord sot => sot -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
newEqDGSONode sot = directEqDGSoId <$> (doGetEqDGSONode sot)

-- Create a new anonymous node and return its identifier
newAnonEqDGSONode :: StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
newAnonEqDGSONode = directEqDGSoId <$> raw_newAnonEqDGSONode

raw_newAnonEqDGSONode :: StateT (EqDGraph s fot sot) (ST s) Int
raw_newAnonEqDGSONode = StateT (\eqdg -> return (f_newAnonEqDGSONode eqdg))

f_newAnonEqDGSONode :: EqDGraph s fot sot -> (Int, EqDGraph s fot sot)
f_newAnonEqDGSONode eqdg = (nn,eqdg1) where with_st = mzoom lens_eqdgraph newDGSONode; (nn,eqdg1) = runState with_st eqdg

raw_newEqDGFOEdge :: (Ord fot, Ord sot) => Int -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) Int
raw_newEqDGFOEdge h ss t = StateT (\eqdg -> return (f_newEqDGFOEdge h ss t eqdg))

f_newEqDGFOEdge :: (Ord fot, Ord sot) => Int -> [Int] -> Int -> (EqDGraph s fot sot -> (Int, EqDGraph s fot sot))
f_newEqDGFOEdge h ss t eqdg = (edge, eqdg1) where rh = getEqDGSORId eqdg h; rss = Prelude.map (getEqDGFORId eqdg) ss; rt = getEqDGFORId eqdg t; edge_st = newDGFOEdge rh rss rt; (edge,eqdg1) = runState (mzoom lens_eqdgraph edge_st) eqdg

newEqDGFOEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Int
newEqDGFOEdge h ss t = do {rh <- getSTRelativeEqDGSoId h; rss <- traverse getSTRelativeEqDGFoId ss; rt <- getSTRelativeEqDGFoId t; raw_newEqDGFOEdge rh rss rt}

-- Create a new anonymous node and an edge whose target it is. Return the node identifier.
raw_newAnonEqDGFOEdge :: (Ord fot, Ord sot) => Int -> [Int] -> StateT (EqDGraph s fot sot) (ST s) Int
raw_newAnonEqDGFOEdge h ss = StateT (f_newAnonEqDGFOEdge h ss)

newAnonEqDGFOEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelFoId s fot sot] -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelFoId s fot sot)
newAnonEqDGFOEdge h ss = do {rh <- getSTRelativeEqDGSoId h; rss <- traverse getSTRelativeEqDGFoId ss; directEqDGFoId <$> (raw_newAnonEqDGFOEdge rh rss)}

f_newAnonEqDGFOEdge :: (Ord fot, Ord sot) => Int -> [Int] -> (EqDGraph s fot sot -> ST s (Int, EqDGraph s fot sot))
f_newAnonEqDGFOEdge h ss eqdg = do {(t,eqdg1) <- runStateT raw_newAnonEqDGFONode eqdg; let {rh = getEqDGSORId eqdg1 h; rss = Prelude.map (getEqDGFORId eqdg1) ss; edge_st = newDGFOEdge rh rss t; (edge,eqdg2) = runState (mzoom lens_eqdgraph edge_st) eqdg1}; return (t,eqdg2)}

raw_newEqDGSOEdge :: Ord sot => Int -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) Int
raw_newEqDGSOEdge h ss t = StateT (\eqdg -> return (f_newEqDGSOEdge h ss t eqdg))

f_newEqDGSOEdge :: Ord sot => Int -> [Int] -> Int -> (EqDGraph s fot sot -> (Int, EqDGraph s fot sot))
f_newEqDGSOEdge h ss t eqdg = (edge, eqdg1) where rh = getEqDGSORId eqdg h; rss = Prelude.map (getEqDGSORId eqdg) ss; rt = getEqDGSORId eqdg t; edge_st = newDGSOEdge rh rss rt; (edge,eqdg1) = runState (mzoom lens_eqdgraph edge_st) eqdg

newEqDGSOEdge :: Ord sot => EqDGRelSoId s fot sot -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Int
newEqDGSOEdge h ss t = do {rh <- getSTRelativeEqDGSoId h; rss <- traverse getSTRelativeEqDGSoId ss; rt <- getSTRelativeEqDGSoId t; raw_newEqDGSOEdge rh rss rt}

-- Create a new anonymous node and an edge whose target it is. Return the node identifier.
raw_newAnonEqDGSOEdge :: Ord sot => Int -> [Int] -> StateT (EqDGraph s fot sot) (ST s) Int
raw_newAnonEqDGSOEdge h ss = StateT (f_newAnonEqDGSOEdge h ss)

newAnonEqDGSOEdge :: Ord sot => EqDGRelSoId s fot sot -> [EqDGRelSoId s fot sot] -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
newAnonEqDGSOEdge h ss = do {rh <- getSTRelativeEqDGSoId h; rss <- traverse getSTRelativeEqDGSoId ss; directEqDGSoId <$> (raw_newAnonEqDGSOEdge rh rss)}

f_newAnonEqDGSOEdge :: Ord sot => Int -> [Int] -> (EqDGraph s fot sot -> ST s (Int, EqDGraph s fot sot))
f_newAnonEqDGSOEdge h ss eqdg = do {(t,eqdg1) <- runStateT raw_newAnonEqDGSONode eqdg; let {rh = getEqDGSORId eqdg1 h; rss = Prelude.map (getEqDGSORId eqdg1) ss; edge_st = newDGSOEdge rh rss t; (edge,eqdg2) = runState (mzoom lens_eqdgraph edge_st) eqdg1}; return (t,eqdg2)}

isFORedundant :: Int -> StateT (EqDGraph s fot sot) (ST s) Bool
isFORedundant eid = hoist (return . runIdentity) (do {eqdg <- get; return (findWithDefault False eid (eqdg_redundant_foedges eqdg))})

isSORedundant :: Int -> StateT (EqDGraph s fot sot) (ST s) Bool
isSORedundant eid = hoist (return . runIdentity) (do {eqdg <- get; return (findWithDefault False eid (eqdg_redundant_soedges eqdg))})

deleteEqDGFOEdge :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) ()
deleteEqDGFOEdge eid = hoist (return . runIdentity) (do {eqdg <- get; let {rid = getCurEqDGFOEdge eqdg eid}; put (lens_eqdg_fored ..~ (Data.Map.Strict.insert rid True) $ eqdg)})

deleteEqDGSOEdge :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) ()
deleteEqDGSOEdge eid = hoist (return . runIdentity) (do {eqdg <- get; let {rid = getCurEqDGSOEdge eqdg eid}; put (lens_eqdg_sored ..~ (Data.Map.Strict.insert rid True) $ eqdg)})

doDeleteEqDGFOEdge :: Ord fot => Int -> StateT (EqDGraph s fot sot) (ST s) ()
doDeleteEqDGFOEdge id = hoist (return . runIdentity) (do {eqdg <- get; let {rid = getCurEqDGFOEdge eqdg id}; (mzoom lens_eqdgraph (deleteDGFOEdge rid))})

doDeleteEqDGSOEdge :: Ord sot => Int -> StateT (EqDGraph s fot sot) (ST s) ()
doDeleteEqDGSOEdge id = hoist (return . runIdentity) (do {eqdg <- get; let {rid = getCurEqDGSOEdge eqdg id}; (mzoom lens_eqdgraph (deleteDGSOEdge rid))})


-- Valid heads, valid sources, valid targets.
in_filterEqDGFOEdges :: (Ord fot, Ord sot) => [sot] -> [fot] -> [fot] -> Bool -> EqDGraph s fot sot -> [Int] -> ST s [Int]
in_filterEqDGFOEdges hs ss ts fred eqdg es = do
	{
		mb_hids <- traverse (getEqDGSONode eqdg) hs;
		mb_sids <- traverse (getEqDGFONode eqdg) ss;
		mb_tids <- traverse (getEqDGFONode eqdg) ts;
		let {hids = fmap fromJust $ Prelude.filter isJust mb_hids};
		let {sids = fmap fromJust $ Prelude.filter isJust mb_sids};
		let {tids = fmap fromJust $ Prelude.filter isJust mb_tids};
		return (in_filterIdEqDGFOEdges hids sids tids fred eqdg es)
	}
		

in_filterIdEqDGFOEdges :: [Int] -> [Int] -> [Int] -> Bool -> EqDGraph s fot sot -> [Int] -> [Int]
in_filterIdEqDGFOEdges hs ss ts fred eqdg es = Prelude.filter (in_filterIdEqDGFOEdge hs ss ts fred eqdg) es

in_filterIdEqDGFOEdge :: [Int] -> [Int] -> [Int] -> Bool -> EqDGraph s fot sot -> Int -> Bool
in_filterIdEqDGFOEdge hs ss ts fred eqdg e = (isJust mb_edge) && (elem_or_empty frh fhs) && ((Prelude.null frss) || (any (\s -> elem_or_empty s fss) frss)) && (elem_or_empty frt fts) && ((not fred) || (not (findWithDefault False e (eqdg_redundant_foedges eqdg)))) where mb_edge = getDGFOEdge (eqdg ^. lens_eqdgraph) e; (DGFOEdge _ rh rss rt) = fromJust mb_edge; fhs = Prelude.map (getEqDGSORId eqdg) hs; fss = Prelude.map (getEqDGFORId eqdg) ss; fts = Prelude.map (getEqDGFORId eqdg) ts; frh = getEqDGSORId eqdg rh; frss = Prelude.map (getEqDGFORId eqdg) rss; frt = getEqDGFORId eqdg rt

in_filterEqDGSOEdges :: Ord sot => [sot] -> [sot] -> [sot] -> Bool -> EqDGraph s fot sot -> [Int] -> ST s [Int]
in_filterEqDGSOEdges hs ss ts fred eqdg es = do
	{
		mb_hids <- traverse (getEqDGSONode eqdg) hs;
		mb_sids <- traverse (getEqDGSONode eqdg) ss;
		mb_tids <- traverse (getEqDGSONode eqdg) ts;
		let {hids = fmap fromJust $ Prelude.filter isJust mb_hids};
		let {sids = fmap fromJust $ Prelude.filter isJust mb_sids};
		let {tids = fmap fromJust $ Prelude.filter isJust mb_tids};
		return (in_filterIdEqDGSOEdges hids sids tids fred eqdg es)
	}
		

in_filterIdEqDGSOEdges :: [Int] -> [Int] -> [Int] -> Bool -> EqDGraph s fot sot -> [Int] -> [Int]
in_filterIdEqDGSOEdges hs ss ts fred eqdg es = Prelude.filter (in_filterIdEqDGSOEdge hs ss ts fred eqdg) es

in_filterIdEqDGSOEdge :: [Int] -> [Int] -> [Int] -> Bool -> EqDGraph s fot sot -> Int -> Bool
in_filterIdEqDGSOEdge hs ss ts fred eqdg e = (isJust mb_edge) && (elem_or_empty frh fhs) && ((Prelude.null frss) || (any (\s -> elem_or_empty s fss) frss)) && (elem_or_empty frt fts) && ((not fred) || (not (findWithDefault False e (eqdg_redundant_soedges eqdg)))) where mb_edge = getDGSOEdge (eqdg ^. lens_eqdgraph) e; (DGSOEdge _ rh rss rt) = fromJust mb_edge; fhs = Prelude.map (getEqDGSORId eqdg) hs; fss = Prelude.map (getEqDGSORId eqdg) ss; fts = Prelude.map (getEqDGSORId eqdg) ts; frh = getEqDGSORId eqdg rh; frss = Prelude.map (getEqDGSORId eqdg) rss; frt = getEqDGSORId eqdg rt

searchOutEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchOutEqDGFOEdges hs ts eqdg s = if (isNothing mb_node) then [] else (in_filterIdEqDGFOEdges hs [] ts True eqdg out) where rs = getEqDGFORId eqdg s; mb_node = getDGFONode (eqdg ^. lens_eqdgraph) rs; (DGFONode _ out _) = fromJust mb_node;

searchAllOutEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchAllOutEqDGFOEdges hs ts eqdg s = if (isNothing mb_node) then [] else (in_filterIdEqDGFOEdges hs [] ts False eqdg out) where rs = getEqDGFORId eqdg s; mb_node = getDGFONode (eqdg ^. lens_eqdgraph) rs; (DGFONode _ out _) = fromJust mb_node;

raw_st_searchOutEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchOutEqDGFOEdges hs ts s = StateT (f_searchOutEqDGFOEdges hs ts s)

st_searchOutEqDGFOEdges :: (Ord fot, Ord sot) => [EqDGRelSoId s fot sot] -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchOutEqDGFOEdges hs ts s = do {rhs <- traverse getSTRelativeEqDGSoId hs; rts <- traverse getSTRelativeEqDGFoId ts; rs <- getSTRelativeEqDGFoId s; raw_st_searchOutEqDGFOEdges rhs rts rs}

f_searchOutEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchOutEqDGFOEdges hs ts s eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchOutEqDGFOEdges hs ts eqdg s)

raw_st_searchAllOutEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchAllOutEqDGFOEdges hs ts s = StateT (f_searchAllOutEqDGFOEdges hs ts s)

st_searchAllOutEqDGFOEdges :: (Ord fot, Ord sot) => [EqDGRelSoId s fot sot] -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchAllOutEqDGFOEdges hs ts s = do {rhs <- traverse getSTRelativeEqDGSoId hs; rts <- traverse getSTRelativeEqDGFoId ts; rs <- getSTRelativeEqDGFoId s; raw_st_searchAllOutEqDGFOEdges rhs rts rs}

f_searchAllOutEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchAllOutEqDGFOEdges hs ts s eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchAllOutEqDGFOEdges hs ts eqdg s)

searchInEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchInEqDGFOEdges hs ss eqdg t = if (isNothing mb_node) then [] else (in_filterIdEqDGFOEdges hs ss [] True eqdg iin) where rt = getEqDGFORId eqdg t; mb_node = getDGFONode (eqdg ^. lens_eqdgraph) rt; (DGFONode _ _ iin) = fromJust mb_node;

searchAllInEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchAllInEqDGFOEdges hs ss eqdg t = if (isNothing mb_node) then [] else (in_filterIdEqDGFOEdges hs ss [] False eqdg iin) where rt = getEqDGFORId eqdg t; mb_node = getDGFONode (eqdg ^. lens_eqdgraph) rt; (DGFONode _ _ iin) = fromJust mb_node;

raw_st_searchInEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchInEqDGFOEdges hs ss t = StateT (f_searchInEqDGFOEdges hs ss t)

st_searchInEqDGFOEdges :: (Ord fot, Ord sot) => [EqDGRelSoId s fot sot] -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchInEqDGFOEdges hs ss t = do {rhs <- traverse getSTRelativeEqDGSoId hs; rss <- traverse getSTRelativeEqDGFoId ss; rt <- getSTRelativeEqDGFoId t; raw_st_searchInEqDGFOEdges rhs rss rt}

f_searchInEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchInEqDGFOEdges hs ss t eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchInEqDGFOEdges hs ss eqdg t)

raw_st_searchAllInEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchAllInEqDGFOEdges hs ss t = StateT (f_searchAllInEqDGFOEdges hs ss t)

st_searchAllInEqDGFOEdges :: (Ord fot, Ord sot) => [EqDGRelSoId s fot sot] -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchAllInEqDGFOEdges hs ss t = do {rhs <- traverse getSTRelativeEqDGSoId hs; rss <- traverse getSTRelativeEqDGFoId ss; rt <- getSTRelativeEqDGFoId t; raw_st_searchAllInEqDGFOEdges rhs rss rt}

f_searchAllInEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchAllInEqDGFOEdges hs ss t eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchAllInEqDGFOEdges hs ss eqdg t)

searchHEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchHEqDGFOEdges ss ts eqdg h = if (isNothing mb_node) then [] else (in_filterIdEqDGFOEdges [] ss ts True eqdg foh) where rh = getEqDGSORId eqdg h; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rh; (DGSONode _ _ _ foh _) = fromJust mb_node;

searchAllHEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchAllHEqDGFOEdges ss ts eqdg h = if (isNothing mb_node) then [] else (in_filterIdEqDGFOEdges [] ss ts False eqdg foh) where rh = getEqDGSORId eqdg h; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rh; (DGSONode _ _ _ foh _) = fromJust mb_node;

raw_st_searchHEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchHEqDGFOEdges ss ts h = StateT (f_searchHEqDGFOEdges ss ts h)

st_searchHEqDGFOEdges :: (Ord fot, Ord sot) => [EqDGRelFoId s fot sot] -> [EqDGRelFoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchHEqDGFOEdges ss ts h = do {rss <- traverse getSTRelativeEqDGFoId ss; rts <- traverse getSTRelativeEqDGFoId ts; rh <- getSTRelativeEqDGSoId h; raw_st_searchHEqDGFOEdges rss rts rh}

f_searchHEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchHEqDGFOEdges ss ts h eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchHEqDGFOEdges ss ts eqdg h)

raw_st_searchAllHEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchAllHEqDGFOEdges ss ts h = StateT (f_searchAllHEqDGFOEdges ss ts h)

st_searchAllHEqDGFOEdges :: (Ord fot, Ord sot) => [EqDGRelFoId s fot sot] -> [EqDGRelFoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchAllHEqDGFOEdges ss ts h = do {rss <- traverse getSTRelativeEqDGFoId ss; rts <- traverse getSTRelativeEqDGFoId ts; rh <- getSTRelativeEqDGSoId h; raw_st_searchAllHEqDGFOEdges rss rts rh}

f_searchAllHEqDGFOEdges :: (Ord fot, Ord sot) => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchAllHEqDGFOEdges ss ts h eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchAllHEqDGFOEdges ss ts eqdg h)

st_checkEqDGFOEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Bool
st_checkEqDGFOEdge h ss t = do {es <- st_searchHEqDGFOEdges ss [t] h; let {ecs = Prelude.map (st_checkEqDGFOSingleEdge h ss t) es}; Prelude.foldr (>>=|) (return False) ecs}

st_checkAllEqDGFOEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Bool
st_checkAllEqDGFOEdge h ss t = do {es <- st_searchAllHEqDGFOEdges ss [t] h; let {ecs = Prelude.map (st_checkEqDGFOSingleEdge h ss t) es}; Prelude.foldr (>>=|) (return False) ecs}

st_checkEqDGFOSingleEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelFoId s fot sot] -> EqDGRelFoId s fot sot -> Int -> StateT (EqDGraph s fot sot) (ST s) Bool
st_checkEqDGFOSingleEdge h ss t e = do {eh <- eqDGFOEdge_head e; ess <- eqDGFOEdge_sources e; et <- eqDGFOEdge_target e; let {sscs = Prelude.map (uncurry eqSTRelativeEqDGFoIds) (zip ess ss)}; ssb <- Prelude.foldr (>>=&) (return True) sscs; if ((length ss) == (length ess)) then ((return ssb) >>=& (eqSTRelativeEqDGSoIds eh h) >>=& (eqSTRelativeEqDGFoIds et t)) else (return False)}

searchOutEqDGSOEdges :: Ord sot => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchOutEqDGSOEdges hs ts eqdg s = if (isNothing mb_node) then [] else (in_filterIdEqDGSOEdges hs [] ts True eqdg out) where rs = getEqDGSORId eqdg s; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rs; (DGSONode _ out _ _ _) = fromJust mb_node;

searchAllOutEqDGSOEdges :: Ord sot => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchAllOutEqDGSOEdges hs ts eqdg s = if (isNothing mb_node) then [] else (in_filterIdEqDGSOEdges hs [] ts False eqdg out) where rs = getEqDGSORId eqdg s; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rs; (DGSONode _ out _ _ _) = fromJust mb_node;

raw_st_searchOutEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchOutEqDGSOEdges hs ts s = StateT (f_searchOutEqDGSOEdges hs ts s)

st_searchOutEqDGSOEdges :: Ord sot => [EqDGRelSoId s fot sot] -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchOutEqDGSOEdges hs ts s = do {rhs <- traverse getSTRelativeEqDGSoId hs; rts <- traverse getSTRelativeEqDGSoId ts; rs <- getSTRelativeEqDGSoId s; raw_st_searchOutEqDGSOEdges rhs rts rs}

f_searchOutEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchOutEqDGSOEdges hs ts s eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchOutEqDGSOEdges hs ts eqdg s)

raw_st_searchAllOutEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchAllOutEqDGSOEdges hs ts s = StateT (f_searchAllOutEqDGSOEdges hs ts s)

st_searchAllOutEqDGSOEdges :: Ord sot => [EqDGRelSoId s fot sot] -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchAllOutEqDGSOEdges hs ts s = do {rhs <- traverse getSTRelativeEqDGSoId hs; rts <- traverse getSTRelativeEqDGSoId ts; rs <- getSTRelativeEqDGSoId s; raw_st_searchAllOutEqDGSOEdges rhs rts rs}

f_searchAllOutEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchAllOutEqDGSOEdges hs ts s eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchAllOutEqDGSOEdges hs ts eqdg s)

searchInEqDGSOEdges :: Ord sot => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchInEqDGSOEdges hs ss eqdg t = if (isNothing mb_node) then [] else (in_filterIdEqDGSOEdges hs ss [] True eqdg iin) where rt = getEqDGSORId eqdg t; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rt; (DGSONode _ _ iin _ _) = fromJust mb_node;

searchAllInEqDGSOEdges :: Ord sot => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchAllInEqDGSOEdges hs ss eqdg t = if (isNothing mb_node) then [] else (in_filterIdEqDGSOEdges hs ss [] False eqdg iin) where rt = getEqDGSORId eqdg t; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rt; (DGSONode _ _ iin _ _) = fromJust mb_node;

raw_st_searchInEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchInEqDGSOEdges hs ss t = StateT (f_searchInEqDGSOEdges hs ss t)

st_searchInEqDGSOEdges :: Ord sot => [EqDGRelSoId s fot sot] -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchInEqDGSOEdges hs ss t = do {rhs <- traverse getSTRelativeEqDGSoId hs; rss <- traverse getSTRelativeEqDGSoId ss; rt <- getSTRelativeEqDGSoId t; raw_st_searchInEqDGSOEdges rhs rss rt}

f_searchInEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchInEqDGSOEdges hs ss t eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchInEqDGSOEdges hs ss eqdg t)

raw_st_searchAllInEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchAllInEqDGSOEdges hs ss t = StateT (f_searchAllInEqDGSOEdges hs ss t)

st_searchAllInEqDGSOEdges :: Ord sot => [EqDGRelSoId s fot sot] -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchAllInEqDGSOEdges hs ss t = do {rhs <- traverse getSTRelativeEqDGSoId hs; rss <- traverse getSTRelativeEqDGSoId ss; rt <- getSTRelativeEqDGSoId t; raw_st_searchAllInEqDGSOEdges rhs rss rt}

f_searchAllInEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchAllInEqDGSOEdges hs ss t eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchAllInEqDGSOEdges hs ss eqdg t)

searchHEqDGSOEdges :: Ord sot => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchHEqDGSOEdges ss ts eqdg h = if (isNothing mb_node) then [] else (in_filterIdEqDGSOEdges [] ss ts True eqdg soh) where rh = getEqDGSORId eqdg h; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rh; (DGSONode _ _ _ _ soh) = fromJust mb_node;

searchAllHEqDGSOEdges :: Ord sot => [Int] -> [Int] -> EqDGraph s fot sot -> Int -> [Int]
searchAllHEqDGSOEdges ss ts eqdg h = if (isNothing mb_node) then [] else (in_filterIdEqDGSOEdges [] ss ts False eqdg soh) where rh = getEqDGSORId eqdg h; mb_node = getDGSONode (eqdg ^. lens_eqdgraph) rh; (DGSONode _ _ _ _ soh) = fromJust mb_node;

raw_st_searchHEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchHEqDGSOEdges ss ts h = StateT (f_searchHEqDGSOEdges ss ts h)

st_searchHEqDGSOEdges :: Ord sot => [EqDGRelSoId s fot sot] -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchHEqDGSOEdges ss ts h = do {rss <- traverse getSTRelativeEqDGSoId ss; rts <- traverse getSTRelativeEqDGSoId ts; rh <- getSTRelativeEqDGSoId h; raw_st_searchHEqDGSOEdges rss rts rh}

f_searchHEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchHEqDGSOEdges ss ts h eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchHEqDGSOEdges ss ts eqdg h)

raw_st_searchAllHEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> StateT (EqDGraph s fot sot) (ST s) [Int]
raw_st_searchAllHEqDGSOEdges ss ts h = StateT (f_searchAllHEqDGSOEdges ss ts h)

st_searchAllHEqDGSOEdges :: Ord sot => [EqDGRelSoId s fot sot] -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [Int]
st_searchAllHEqDGSOEdges ss ts h = do {rss <- traverse getSTRelativeEqDGSoId ss; rts <- traverse getSTRelativeEqDGSoId ts; rh <- getSTRelativeEqDGSoId h; raw_st_searchAllHEqDGSOEdges rss rts rh}

f_searchAllHEqDGSOEdges :: Ord sot => [Int] -> [Int] -> Int -> (EqDGraph s fot sot -> ST s ([Int], EqDGraph s fot sot))
f_searchAllHEqDGSOEdges ss ts h eqdg = (,eqdg) <$> stmb_int where stmb_int = return (searchAllHEqDGSOEdges ss ts eqdg h)

st_checkEqDGSOEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Bool
st_checkEqDGSOEdge h ss t = do {es <- st_searchHEqDGSOEdges ss [t] h; let {ecs = Prelude.map (st_checkEqDGSOSingleEdge h ss t) es}; Prelude.foldr (>>=|) (return False) ecs}

st_checkAllEqDGSOEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) Bool
st_checkAllEqDGSOEdge h ss t = do {es <- st_searchAllHEqDGSOEdges ss [t] h; let {ecs = Prelude.map (st_checkEqDGSOSingleEdge h ss t) es}; Prelude.foldr (>>=|) (return False) ecs}

st_checkEqDGSOSingleEdge :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> [EqDGRelSoId s fot sot] -> EqDGRelSoId s fot sot -> Int -> StateT (EqDGraph s fot sot) (ST s) Bool
st_checkEqDGSOSingleEdge h ss t e = do {eh <- eqDGSOEdge_head e; ess <- eqDGSOEdge_sources e; et <- eqDGSOEdge_target e; let {sscs = Prelude.map (uncurry eqSTRelativeEqDGSoIds) (zip ess ss)}; ssb <- Prelude.foldr (>>=&) (return True) sscs; if ((length ss) == (length ess)) then ((return ssb) >>=& (eqSTRelativeEqDGSoIds eh h) >>=& (eqSTRelativeEqDGSoIds et t)) else (return False)}


raw_getEquivDGFONodes :: Ord fot => EqDGraph s fot sot -> fot -> ST s [fot]
raw_getEquivDGFONodes eqdg fot = do {(nid,eqdg1) <- runStateT (doGetEqDGFONode fot) eqdg; return (fromMaybe [] (eqdg1 ^. lens_eqdg_foelements . (at nid)))}

raw_st_getEquivDGFONodes :: Ord fot => fot -> StateT (EqDGraph s fot sot) (ST s) [fot]
raw_st_getEquivDGFONodes fot = StateT (f_getEquivDGFONodes fot)

getEquivDGFONodes :: Ord fot => EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [fot]
getEquivDGFONodes fot = do {mb_coid <- getSTRelativeEqDGFoCoId fot; let {coid = fromJustErr "getEquivDGFONodes" mb_coid}; equivs <- if (isNothing mb_coid) then (return []) else (raw_st_getEquivDGFONodes coid); return equivs}

f_getEquivDGFONodes :: Ord fot => fot -> (EqDGraph s fot sot -> ST s ([fot], EqDGraph s fot sot))
f_getEquivDGFONodes fot eqdg = (,eqdg) <$> stmb_int where stmb_int = raw_getEquivDGFONodes eqdg fot

raw_getEquivDGSONodes :: Ord sot => EqDGraph s fot sot -> sot -> ST s [sot]
raw_getEquivDGSONodes eqdg sot = do {(nid,eqdg1) <- runStateT (doGetEqDGSONode sot) eqdg; return (fromMaybe [] (eqdg1 ^. lens_eqdg_soelements . (at nid)))}

raw_st_getEquivDGSONodes :: Ord sot => sot -> StateT (EqDGraph s fot sot) (ST s) [sot]
raw_st_getEquivDGSONodes sot = StateT (f_getEquivDGSONodes sot)

getEquivDGSONodes :: Ord sot => EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) [sot]
getEquivDGSONodes sot = do {mb_coid <- getSTRelativeEqDGSoCoId sot; let {coid = fromJustErr "getEquivDGSONodes" mb_coid}; equivs <- if (isNothing mb_coid) then (return []) else (raw_st_getEquivDGSONodes coid); return equivs}

f_getEquivDGSONodes :: Ord sot => sot -> (EqDGraph s fot sot -> ST s ([sot], EqDGraph s fot sot))
f_getEquivDGSONodes sot eqdg = (,eqdg) <$> stmb_int where stmb_int = raw_getEquivDGSONodes eqdg sot

-- Clear the elements pointed to at a node. This is an internal function that should not be used directly!! It is part of the merge.
clearElementsDGFONode :: Ord fot => EqDGraph s fot sot -> Int -> EqDGraph s fot sot
clearElementsDGFONode eqdg nid = lens_eqdg_foelements . (at nid) .~ Just [] $ eqdg

clearElementsDGSONode :: Ord sot => EqDGraph s fot sot -> Int -> EqDGraph s fot sot
clearElementsDGSONode eqdg nid = lens_eqdg_soelements . (at nid) .~ Just [] $ eqdg

-- Similarly, add a bunch of elements to a node.
addElementsDGFONode :: Ord fot => EqDGraph s fot sot -> Int -> [fot] -> EqDGraph s fot sot
addElementsDGFONode eqdg nid els = lens_eqdg_foelements . (at nid) ..~ (\l -> Just (append_to_mblist l els)) $ eqdg

addElementsDGSONode :: Ord sot => EqDGraph s fot sot -> Int -> [sot] -> EqDGraph s fot sot
addElementsDGSONode eqdg nid els = lens_eqdg_soelements . (at nid) ..~ (\l -> Just (append_to_mblist l els)) $ eqdg

-- If either of the nodes do not exist yet, they get created before being merged.
raw_mergeEqDGFONodes :: (Ord fot, Ord sot) => Int -> Int -> StateT (EqDGraph s fot sot) (ST s) Int
raw_mergeEqDGFONodes lnid rnid = StateT (f_mergeEqDGFONodes lnid rnid)

mergeEqDGFONodes :: (Ord fot, Ord sot) => EqDGRelFoId s fot sot -> EqDGRelFoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelFoId s fot sot)
mergeEqDGFONodes lfot rfot = do {lnid <- getSTRelativeEqDGFoId lfot; rnid <- getSTRelativeEqDGFoId rfot; directEqDGFoId <$> (raw_mergeEqDGFONodes lnid rnid)}

f_mergeEqDGFONodes :: (Ord fot, Ord sot) => Int -> Int -> (EqDGraph s fot sot -> ST s (Int,EqDGraph s fot sot))
f_mergeEqDGFONodes lnid rnid eqdg | (getEqDGFORId eqdg lnid) == (getEqDGFORId eqdg rnid) = return (lnid,eqdg)
f_mergeEqDGFONodes lnid rnid eqdg = 
	do
	{
		let {rlnid = getEqDGFORId eqdg lnid; rrnid = getEqDGFORId eqdg rnid};
		mb_lfot <- getEqDGFORep eqdg rlnid;
		mb_rfot <- getEqDGFORep eqdg rrnid;
		let {lfot = fromJust mb_lfot; rfot = fromJust mb_rfot};
		--let {lpt = fromJust (eqdg ^. lens_eqdg_fopoints . (at lfot)); rpt = fromJust (eqdg ^. lens_eqdg_fopoints . (at rfot))};
		let {lpt = fromJust (getEqDGFOPoint eqdg lfot); rpt = fromJust (getEqDGFOPoint eqdg rfot)};						
		-- We need to do both directions to consider the cases where one of the nodes has elements and the other not: we never update the fonodes map, 
		-- and in order to merge a node with elements in it into one without elements would require so, because those elements are changing node and we
		-- cannot deal with that with union because there is nothing to unite with.		
		if (isNothing mb_rfot) then do
		{
			let {eout = searchAllOutEqDGFOEdges [] [] eqdg rrnid};
			let {ein = searchAllInEqDGFOEdges [] [] eqdg rrnid};
			gtraceM False "EIN";
			gtraceM False (show ein);
			gtraceM False "EIN//";
			let {alle = nub (eout ++ ein)};
			let {allee = (fromJust <$>) . (Prelude.filter isJust) . (Prelude.map (getDGFOEdge (eqdg ^. lens_eqdgraph))) $ alle};
			let {ralle = Prelude.map (\(DGFOEdge id h ss t) -> DGFOEdge id h (replaceAll rrnid rlnid ss) (replaceIf rrnid rlnid t)) allee};
			(_,eqdg2) <- runStateT (traverse doDeleteEqDGFOEdge alle) eqdg;
			let {(_,eqdg3) = runState (traverse (\(DGFOEdge previd h ss t) -> do {newid <- mzoom lens_eqdgraph (newDGFOEdge h ss t); seqdg <- get; put ((lens_eqdg_foedges . (at previd)) .~ (Just newid) $ ((lens_eqdg_fored . (at newid)) .~ (Just (findWithDefault False previd (eqdg_redundant_foedges eqdg))) $ seqdg))}) ralle) eqdg2};			
			eqdg5 <- (return eqdg3);
			(_,eqdg5_2) <- runStateT (zoom_on_dgraph (deleteDGFONode rrnid)) eqdg5;			
			let {eqdg7 = (lens_eqdg_fomerges . (at rrnid)) .~ (Just rlnid) $ eqdg5_2};			
			return (rlnid,eqdg7)
		}
		else do
		{
			let {eout = searchAllOutEqDGFOEdges [] [] eqdg rlnid};
			let {ein = searchAllInEqDGFOEdges [] [] eqdg rlnid};
			let {alle = nub (eout ++ ein)};
			let {allee = (fromJust <$>) . (Prelude.filter isJust) . (Prelude.map (getDGFOEdge (eqdg ^. lens_eqdgraph))) $ alle};
			let {ralle = Prelude.map (\(DGFOEdge id h ss t) -> DGFOEdge id h (replaceAll rlnid rrnid ss) (replaceIf rlnid rrnid t)) allee};
			(_,eqdg2) <- runStateT (traverse doDeleteEqDGFOEdge alle) eqdg;
			let {(_,eqdg3) = runState (traverse (\(DGFOEdge previd h ss t) -> do {newid <- mzoom lens_eqdgraph (newDGFOEdge h ss t); seqdg <- get; put ((lens_eqdg_foedges . (at previd)) .~ (Just newid) $ ((lens_eqdg_fored . (at newid)) .~ (Just (findWithDefault False previd (eqdg_redundant_foedges eqdg))) $ seqdg))}) ralle) eqdg2};			
			eqdg5 <- if (isJust mb_lfot) then do
			{
				lfots <- raw_getEquivDGFONodes eqdg3 lfot;
				let {eqdg4 = addElementsDGFONode eqdg3 rrnid lfots; eqdg5 = clearElementsDGFONode eqdg4 rlnid};
				return eqdg5
			}
			else (return eqdg3);
			(_,eqdg5_2) <- runStateT (zoom_on_dgraph (deleteDGFONode rlnid)) eqdg5;			
			--when (isJust mb_lfot) (check_union lpt rpt);
			let {eqdg6 = if (isJust mb_lfot) then ((lens_eqdg_fopoints . (at lpt)) .~ (Just rpt) $ eqdg5_2) else eqdg5_2};
			let {eqdg7 = (lens_eqdg_fomerges . (at rlnid)) .~ (Just rrnid) $ eqdg6};
			return (rrnid,eqdg7)
		}
	}

raw_mergeEqDGSONodes :: (Ord fot, Ord sot) => Int -> Int -> StateT (EqDGraph s fot sot) (ST s) Int
raw_mergeEqDGSONodes lnid rnid = StateT (f_mergeEqDGSONodes lnid rnid)

mergeEqDGSONodes :: (Ord fot, Ord sot) => EqDGRelSoId s fot sot -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
mergeEqDGSONodes lsot rsot = do {lnid <- getSTRelativeEqDGSoId lsot; rnid <- getSTRelativeEqDGSoId rsot; directEqDGSoId <$> (raw_mergeEqDGSONodes lnid rnid)}

f_mergeEqDGSONodes :: (Ord fot, Ord sot) => Int -> Int -> (EqDGraph s fot sot -> ST s (Int,EqDGraph s fot sot))
f_mergeEqDGSONodes lnid rnid eqdg | (getEqDGSORId eqdg lnid) == (getEqDGSORId eqdg rnid) = return (lnid,eqdg)
f_mergeEqDGSONodes lnid rnid eqdg = 
	do
	{
		let {rlnid = getEqDGSORId eqdg lnid; rrnid = getEqDGSORId eqdg rnid};
		mb_lsot <- getEqDGSORep eqdg rlnid;
		mb_rsot <- getEqDGSORep eqdg rrnid;
		let {lsot = fromJust mb_lsot; rsot = fromJust mb_rsot};
		--let {lpt = fromJust (eqdg ^. lens_eqdg_sopoints . (at lsot)); rpt = fromJust (eqdg ^. lens_eqdg_sopoints . (at rsot))};
		let {lpt = fromJust (getEqDGSOPoint eqdg lsot); rpt = fromJust (getEqDGSOPoint eqdg rsot)};
		-- We need to do both directions to consider the cases where one of the nodes has elements and the other not: we never update the sonodes map, 
		-- and in order to merge a node with elements in it into one without elements would require so, because those elements are changing node and we
		-- cannot deal with that with union because there is nothing to unite with.
		if (isNothing mb_rsot) then do
		{
			let {eout = searchAllOutEqDGSOEdges [] [] eqdg rrnid};
			let {ein = searchAllInEqDGSOEdges [] [] eqdg rrnid};
			let {efoh = searchAllHEqDGFOEdges [] [] eqdg rrnid};
			let {esoh = searchAllHEqDGSOEdges [] [] eqdg rrnid};
			let {allse = nub (eout ++ ein ++ esoh); allfe = nub efoh};
			let {allsee = (fromJust <$>) . (Prelude.filter isJust) . (Prelude.map (getDGSOEdge (eqdg ^. lens_eqdgraph))) $ allse; allfee = (fromJust <$>) . (Prelude.filter isJust) . (Prelude.map (getDGFOEdge (eqdg ^. lens_eqdgraph))) $ allfe};
			let {rallse = Prelude.map (\(DGSOEdge id h ss t) -> DGSOEdge id (replaceIf rrnid rlnid h) (replaceAll rrnid rlnid ss) (replaceIf rrnid rlnid t)) allsee; rallfe = Prelude.map (\(DGFOEdge id h ss t) -> DGFOEdge id (replaceIf rrnid rlnid h) ss t) allfee};
			(_,eqdg2) <- runStateT (traverse doDeleteEqDGSOEdge allse) eqdg;
			(_,eqdg2_2) <- runStateT (traverse doDeleteEqDGFOEdge allfe) eqdg2;			
			let {(_,eqdg3) = runState (traverse (\(DGSOEdge previd h ss t) -> do {newid <- mzoom lens_eqdgraph (newDGSOEdge h ss t); seqdg <- get; put ((lens_eqdg_soedges . (at previd)) .~ (Just newid) $ ((lens_eqdg_sored . (at newid)) .~ (Just (findWithDefault False previd (eqdg_redundant_soedges eqdg))) $ seqdg))}) rallse) eqdg2_2; (_,eqdg3_2) = runState (traverse (\(DGFOEdge previd h ss t) -> do {newid <- mzoom lens_eqdgraph (newDGFOEdge h ss t); seqdg <- get; put ((lens_eqdg_foedges . (at previd)) .~ (Just newid) $ ((lens_eqdg_fored . (at newid)) .~ (Just (findWithDefault False previd (eqdg_redundant_foedges eqdg))) $ seqdg))}) rallfe) eqdg3};
			eqdg5 <- (return eqdg3_2);
			(_,eqdg5_2) <- runStateT (zoom_on_dgraph (deleteDGSONode rrnid)) eqdg5;			
			let {eqdg7 = (lens_eqdg_somerges . (at rrnid)) .~ (Just rlnid) $ eqdg5_2};
			return (rlnid,eqdg7)
		}
		else do
		{
			let {eout = searchAllOutEqDGSOEdges [] [] eqdg rlnid};
			let {ein = searchAllInEqDGSOEdges [] [] eqdg rlnid};
			let {efoh = searchAllHEqDGFOEdges [] [] eqdg rlnid};
			let {esoh = searchAllHEqDGSOEdges [] [] eqdg rlnid};
			let {allse = nub (eout ++ ein ++ esoh); allfe = nub efoh};
			let {allsee = (fromJust <$>) . (Prelude.filter isJust) . (Prelude.map (getDGSOEdge (eqdg ^. lens_eqdgraph))) $ allse; allfee = (fromJust <$>) . (Prelude.filter isJust) . (Prelude.map (getDGFOEdge (eqdg ^. lens_eqdgraph))) $ allfe};
			let {rallse = Prelude.map (\(DGSOEdge id h ss t) -> DGSOEdge id (replaceIf rlnid rrnid h) (replaceAll rlnid rrnid ss) (replaceIf rlnid rrnid t)) allsee; rallfe = Prelude.map (\(DGFOEdge id h ss t) -> DGFOEdge id (replaceIf rlnid rrnid h) ss t) allfee};
			(_,eqdg2) <- runStateT (traverse doDeleteEqDGSOEdge allse) eqdg;
			(_,eqdg2_2) <- runStateT (traverse doDeleteEqDGFOEdge allfe) eqdg2;			
			let {(_,eqdg3) = runState (traverse (\(DGSOEdge previd h ss t) -> do {newid <- mzoom lens_eqdgraph (newDGSOEdge h ss t); seqdg <- get; put ((lens_eqdg_soedges . (at previd)) .~ (Just newid) $ ((lens_eqdg_sored . (at newid)) .~ (Just (findWithDefault False previd (eqdg_redundant_soedges eqdg))) $ seqdg))}) rallse) eqdg2_2; (_,eqdg3_2) = runState (traverse (\(DGFOEdge previd h ss t) -> do {newid <- mzoom lens_eqdgraph (newDGFOEdge h ss t); seqdg <- get; put ((lens_eqdg_foedges . (at previd)) .~ (Just newid) $ ((lens_eqdg_fored . (at newid)) .~ (Just (findWithDefault False previd (eqdg_redundant_foedges eqdg))) $ seqdg))}) rallfe) eqdg3};				
			eqdg5 <- if (isJust mb_lsot) then do
			{
				lsots <- raw_getEquivDGSONodes eqdg3_2 lsot;
				let {eqdg4 = addElementsDGSONode eqdg3_2 rrnid lsots; eqdg5 = clearElementsDGSONode eqdg4 rlnid};
				return eqdg5
			}
			else (return eqdg3_2);
			(_,eqdg5_2) <- runStateT (zoom_on_dgraph (deleteDGSONode rlnid)) eqdg5;			
			--when (isJust mb_lsot) (check_union lpt rpt);
			let {eqdg6 = if (isJust mb_lsot) then ((lens_eqdg_sopoints . (at lpt)) .~ (Just rpt) $ eqdg5_2) else eqdg5_2};
			let {eqdg7 = (lens_eqdg_somerges . (at rlnid)) .~ (Just rrnid) $ eqdg6};
			return (rrnid,eqdg7)
		}
	}

find_eqdgraph_foleaves :: StateT (EqDGraph s fot sot) (ST s) [EqDGRelFoId s fot sot]
find_eqdgraph_foleaves = do
	{
		eqdg <- get;
		let {nodes = (eqdgraph eqdg) ^. lens_fonodes; fnodes = Prelude.map fromJust (Prelude.filter isJust nodes)};
		let {fil = (\node -> Prelude.null (node ^. lens_dgfonode_out)); ffnodes = Prelude.filter fil fnodes};
		return (Prelude.map (DirectId . EqDGFoId . dgid) ffnodes)
	}

find_eqdgraph_soleaves :: StateT (EqDGraph s fot sot) (ST s) [EqDGRelSoId s fot sot]
find_eqdgraph_soleaves = do
	{
		eqdg <- get;
		let {nodes = (eqdgraph eqdg) ^. lens_sonodes; fnodes = Prelude.map fromJust (Prelude.filter isJust nodes)};
		let {fil = (\node -> (Prelude.null (node ^. lens_dgsonode_out)) && (Prelude.null (node ^. lens_dgsonode_soh))); ffnodes = Prelude.filter fil fnodes};
		return (Prelude.map (DirectId . EqDGSoId . dgid) ffnodes)
	}

zoom_on_dgraph :: State DGraph c -> StateT (EqDGraph s fot sot) (ST s) c
zoom_on_dgraph st = hoist (return . runIdentity) (mzoom lens_eqdgraph st)

elem_or_empty :: Eq a => a -> [a] -> Bool
elem_or_empty _ [] = True
elem_or_empty a as = elem a as

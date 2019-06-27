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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
module Algorithm where

import Data.Maybe
import HaskellPlus
import EnumProc
import Provenance

-- In some sense this generalizes EnumProc to allow arbitrary search strategies. To get the full generalization without committing to any particular search strategy, use only the most basic functions of EnumProc, and everything else from Algorithm. That is, don't produce EnumProcs by combining other EnumProcs, but only directly, and let ExecOrder do the combining.
data Algorithm a b = AlgDir (a -> b) | forall c. AlgStep (Algorithm c b) (Algorithm a c) | AlgFork (a -> EnumProc b)

type Computation a = (() .-> a)

type (a .-> b) = Algorithm a b
infixr 0 .->

alg :: (a -> b) -> a .-> b
alg = AlgDir

comp :: a -> Computation a
comp x = alg (\_ -> x)

(...) :: (b .-> c) -> (a .-> b) -> (a .-> c)
x ... y = AlgStep x y
infixr 0 ...

fork :: (a -> EnumProc b) -> a .-> b
fork = AlgFork

class ExecOrder t where
	execorder :: t -> (a -> EnumProc b) -> EnumProc a -> EnumProc b

runorder :: ExecOrder t => t -> (a .-> b) -> a -> EnumProc b
runorder x (AlgDir f) = (\y -> single_enum (f y))
runorder x (AlgFork f) = f
runorder x (AlgStep f g) = (\y -> execorder x (runorder x f) (runorder x g y))

data DFS = DFS

dfs :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
dfs f Empty = Empty
dfs f Halt = Halt
dfs f (Error str) = Error str
dfs f (Continue x) = Continue (dfs f x)
dfs f (Produce v x) = uns_append (f v) (dfs f x)

instance ExecOrder DFS where
	execorder DFS = dfs

(|$) :: (a .-> b) -> a -> EnumProc b
f |$ a = runorder DFS f a
infix 0 |$

-- The bool indicates whether it is necessary to do it in the same order at every level, or we can reverse it at every level (which is more efficient)
data BFS = BFS Bool

bfs :: Bool -> (a -> EnumProc b) -> EnumProc a -> EnumProc b
bfs fl f e = bfs_rec fl Empty (fmap f e)

bfs_rec :: Bool -> EnumProc (EnumProc b) -> EnumProc (EnumProc b) -> EnumProc b
bfs_rec fl Empty Empty = Empty
bfs_rec True prev Empty = bfs_rec True Empty (uns_ereverse prev)
bfs_rec False prev Empty = bfs_rec False Empty prev
bfs_rec fl prev Halt = Halt
bfs_rec fl prev (Error str) = Error str
bfs_rec fl prev (Continue x) = Continue (bfs_rec fl prev x)
bfs_rec fl prev (Produce Empty x) = Continue (bfs_rec fl prev x)
bfs_rec fl prev (Produce Halt x) = Halt
bfs_rec fl prev (Produce (Error str) x) = Error str
bfs_rec fl prev (Produce (Continue y) x) = Continue (bfs_rec fl (y --> prev) x)
bfs_rec fl prev (Produce (Produce v y) x) = Produce v (bfs_rec fl (y --> prev) x)

instance ExecOrder BFS where
	execorder (BFS fl) = bfs fl

(-$) :: (a .-> b) -> a -> EnumProc b
f -$ a = runorder (BFS True) f a
infix 0 -$

-- Iterative deepening: Same order as BFS, but trades time for space.
data ITD = ITD

itd :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
itd f en = itd_rec 0 en False f en

-- In order to be able to stop when the enumeration has terminated, we carry a flag that says whether we produced any new value at all in this iteration.
itd_rec :: Int -> EnumProc a -> Bool -> (a -> EnumProc b) -> EnumProc a -> EnumProc b
itd_rec n full False f Empty = Empty
itd_rec n full True f Empty = itd_rec (n+1) full False f full
itd_rec n full fl f Halt = Halt
itd_rec n full fl f (Error str) = Error str
itd_rec n full fl f (Continue x) = Continue (itd_rec n full fl f x)
itd_rec n full fl f (Produce a x) = (itd_rec_one n full fl f a x)

itd_rec_one :: Int -> EnumProc a -> Bool -> (a -> EnumProc b) -> a -> EnumProc a -> EnumProc b
itd_rec_one n full fl f a x = case (nstep n (f a)) of 
				{
					Empty -> Continue (itd_rec n full fl f x);
					Halt -> Halt;
					(Error str) -> Error str;
					(Continue y) -> Continue (itd_rec n full True f x);
					(Produce v y) -> v --> (itd_rec n full True f x)
				}


instance ExecOrder ITD where
	execorder ITD = itd

(|-$) :: (a .-> b) -> a -> EnumProc b
f |-$ a = runorder ITD f a
infix 0 |-$

-- Diagonalization :: Eager/lazy, proportion horizontal/vertical.

-- Give me a function f that, given n elements of type a and a continuation (an enumeration of a's), returns the enumeration product of applying something to those a's and then (typically, recursively) applying something to the rest of the a's.
-- I will apply f on the next elements of type a that I find, if I do, with the tail of b's that I should be producing, producing an enumeration of b's.
-- Note that the reason this is not simply done by compressing the first n is that the result of this is an EnumProc that will have Continues corresponding to any Continues that the source EnumProcs may have, meaning that the result will be safe (each step will be finite) even when the EnumProc given does not have n elements.
eager :: Int -> ([a] -> EnumProc a -> EnumProc b) -> EnumProc a -> EnumProc b
eager _ _ Empty = Empty
eager _ _ Halt = Halt
eager _ _ (Error str) = Error str
eager n f x = eager_help f rf rr where (rf,rr) = list_n_from_enum_strict_full n x

eager_help :: ([a] -> EnumProc a -> EnumProc b) -> EnumProc [a] -> EnumProc a -> EnumProc b
eager_help f rf rr = apply_next (\x -> f x rr) rf



data Diagonalize = Diagonalize Bool Bool Int Int Bool

-- First argument: Is it vertically (depth) eager?
-- Second argument: Is it horizontally (width) eager?
-- Third argument: Depth to explore each branch before jumping to next.
-- Fourth argument: Width to increase before doing the next cycle.
-- Fifth argument: Reverse before each cycle, to keep the order, or is it not necessary?
gen_diagonalize :: Bool -> Bool -> Int -> Int -> Bool -> (a -> EnumProc b) -> EnumProc a -> EnumProc b
gen_diagonalize veag heag depth width fl f en = gen_diagonalize_rec veag heag depth width fl f en [] []

gen_diagonalize_rec :: Bool -> Bool -> Int -> Int -> Bool -> (a -> EnumProc b) -> EnumProc a -> [EnumProc b] -> [EnumProc b] -> EnumProc b
gen_diagonalize_rec veag heag depth width fl f Halt prev [] = Halt
gen_diagonalize_rec veag heag depth width fl f (Error str) prev [] = Error str
gen_diagonalize_rec veag heag depth width fl f Empty [] [] = Empty
gen_diagonalize_rec veag heag depth width fl f Empty prev [] = gen_diagonalize_rec veag heag depth width fl f Empty [] prev
gen_diagonalize_rec veag False depth width True f en prev [] = gen_diagonalize_rec veag False depth width True f r [] fnew where (new,r) = get_nstep_full width en; fnew = (reverse prev) ++ (map f new)
gen_diagonalize_rec veag False depth width False f en prev [] = gen_diagonalize_rec veag False depth width True f r [] fnew where (new,r) = get_nstep_full width en; fnew = (map f new) ++ prev
gen_diagonalize_rec veag True depth width True f en prev [] = eager width f1 en where f1 = (\new -> \r -> gen_diagonalize_rec veag True depth width True f r [] ((reverse prev) ++ (map f new)))
gen_diagonalize_rec veag True depth width False f en prev [] = eager width f1 en where f1 = (\new -> \r -> gen_diagonalize_rec veag True depth width False f r [] ((map f new) ++ prev))
gen_diagonalize_rec veag heag depth width fl f en prev (Empty:xs) = gen_diagonalize_rec veag heag depth width fl f en prev xs
gen_diagonalize_rec veag heag depth width fl f en prev (Halt:xs) = Halt
gen_diagonalize_rec veag heag depth width fl f en prev ((Error str):xs) = Error str
gen_diagonalize_rec False heag depth width fl f en prev (x:xs) = uns_append (uns_enum_from_list new) (gen_diagonalize_rec False heag depth width fl f en (r:prev) xs) where (new,r) = get_nstep_full depth x
gen_diagonalize_rec True heag depth width fl f en prev (x:xs) = eager depth f1 x where f1 = (\new -> \r -> uns_append (uns_enum_from_list new) (gen_diagonalize_rec True heag depth width fl f en (r:prev) xs))

instance ExecOrder Diagonalize where
	execorder (Diagonalize veag heag depth width fl) = gen_diagonalize veag heag depth width fl

(\$) :: (a .-> b) -> a -> EnumProc b
f \$ a = runorder (Diagonalize False False 1 1 False) f a
infix 0 \$




(.|$) :: (a .-> b) -> EnumProc a -> EnumProc b
alg .|$ en = (alg ... (fork (\_ -> en))) |$ ()
infix 0 .|$

(|$.) :: (a -> EnumProc b) -> Computation a -> EnumProc b
fen |$. comp = ((fork fen) ... comp) |$ ()
infix 0 |$.

(.-$) :: (a .-> b) -> EnumProc a -> EnumProc b
alg .-$ en = (alg ... (fork (\_ -> en))) -$ ()
infix 0 .-$

(-$.) :: (a -> EnumProc b) -> Computation a -> EnumProc b
fen -$. comp = ((fork fen) ... comp) -$ ()
infix 0 -$.

(.|-$) :: (a .-> b) -> EnumProc a -> EnumProc b
alg .|-$ en = (alg ... (fork (\_ -> en))) |-$ ()
infix 0 .|-$

(|-$.) :: (a -> EnumProc b) -> Computation a -> EnumProc b
fen |-$. comp = ((fork fen) ... comp) |-$ ()
infix 0 |-$.

(.\$) :: (a .-> b) -> EnumProc a -> EnumProc b
alg .\$ en = (alg ... (fork (\_ -> en))) \$ ()
infix 0 .\$

(\$.) :: (a -> EnumProc b) -> Computation a -> EnumProc b
fen \$. comp = ((fork fen) ... comp) \$ ()
infix 0 \$.

(.|) :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
en1 .| en2 = (fork en1) .|$ en2
infix 0 .|

(.-) :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
en1 .- en2 = (fork en1) .-$ en2
infix 0 .-

(.|-) :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
en1 .|- en2 = (fork en1) .|-$ en2
infix 0 .|-

(.\) :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
en1 .\ en2 = (fork en1) .\$ en2
infix 0 .\

-- To be honest, Computation could be a Monad, but semantically, it makes no sense, as it has no side effects or any relevant semantics that composition of computations does not already have. If you want to compose computations, use the compose function, no need for a monad.

-- W/Provenance operators

type ProvAlgorithm a b p = (a :- p) .-> (b :- p)

provalg :: Semigroup p => (a -> (b :- p)) -> ((a :- p) .-> (b :- p))
provalg f = alg (f $:)

provfork :: Semigroup p => (a -> EnumProc (b :- p)) -> ((a :- p) .-> (b :- p))
provfork f = fork (fflatten_provenance . (fmap f))

(-:>) :: Semigroup p => ((a :- p) .-> (b :- p)) -> p -> ((a :- p) .-> (b :-p))
f -:> p = (alg (>>: p)) ... f
infix 0 -:>

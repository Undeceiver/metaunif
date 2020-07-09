{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Algorithm where

import Control.Monad.Trans
import Control.Monad.Morph
import Data.Maybe
import HaskellPlus
import EnumProc
import Provenance
import Data.Tuple
import Control.Monad.Trans.State
import qualified Control.Lens

-- In some sense this generalizes EnumProc to allow arbitrary search strategies. To get the full generalization without committing to any particular search strategy, use only the most basic functions of EnumProc, and everything else from Algorithm. That is, don't produce EnumProcs by combining other EnumProcs, but only directly, and let ExecOrder do the combining.
data Algorithm a b = AlgDir (a -> b) | forall c. AlgStep (Algorithm c b) (Algorithm a c) | AlgFork (a -> EnumProc b) | AlgFilter (a -> Maybe b) | AlgEval (forall t. ExecOrder t => t -> a -> EnumProc b)

type Computation = Algorithm ()

type (a .-> b) = Algorithm a b
infixr 0 .->

idalg :: a .-> a
idalg = alg id

alg :: (a -> b) -> a .-> b
alg = AlgDir

algfilter :: (a -> Maybe b) -> a .-> b
algfilter = AlgFilter

comp :: a -> Computation a
comp x = alg (\_ -> x)

ecomp :: EnumProc a -> Computation a
ecomp x = fork (\_ -> x)

(...) :: (b .-> c) -> (a .-> b) -> (a .-> c)
x ... y = AlgStep x y
infixr 0 ...

withorder :: (forall t. ExecOrder t => t -> a -> EnumProc b) -> Algorithm a b
withorder = AlgEval

-- Lifts a transformation on enumerations into a transformation on algorithms.
withenum :: ((a -> EnumProc b) -> (c -> EnumProc d)) -> (a .-> b) -> (c .-> d)
withenum f alg = withorder (\t -> f (runorder t alg))

withenumcomp :: (EnumProc a -> EnumProc b) -> Computation a -> Computation b
withenumcomp f comp = withenum (\g -> (\() -> f (g ()))) comp

-- To lift EnumProc functions to algorithms when pattern matching, without doing any search order combining.
alg_empty :: Algorithm a b
alg_empty = withorder (\_ -> \_ -> Empty)

alg_halt :: Algorithm a b
alg_halt = withorder (\_ -> \_ -> Halt)

alg_error :: String -> Algorithm a b
alg_error str = withorder (\_ -> \_ -> Error str)

alg_continue :: Algorithm a b -> Algorithm a b
alg_continue alg = withorder (\x -> \a -> Continue (runorder x alg a))

alg_produce :: (a -> b) -> Algorithm a b -> Algorithm a b
alg_produce b alg = withorder (\x -> \a -> Produce (b a) (runorder x alg a))



alg_uncurry :: (a .-> b .-> c) -> (a,b) .-> c
alg_uncurry f = withorder (alg_uncurry_order f)

alg_uncurry_order :: ExecOrder t => (a .-> b .-> c) -> t -> (a,b) -> EnumProc c
alg_uncurry_order f x (a,b) = execorder x (\g -> runorder x g b) (runorder x f a)

alg_curry :: ((a,b) .-> c) -> a .-> b .-> c
alg_curry f = alg (\a -> f ... (alg (a,)))

cfactor :: (a .-> b) -> (a -> () .-> b)
cfactor f a = f ... (comp a)

cunfactor :: (a -> () .-> b) -> (a .-> b)
cunfactor f = withorder (cunfactor_order f)

cunfactor_order :: ExecOrder t => (a -> () .-> b) -> t -> a -> EnumProc b
cunfactor_order f x a = runorder x (f a) ()

-- Weak versions of curry/uncurry, where only one Algorithm layer exists.
cuncurry :: (a -> b .-> c) -> (a,b) .-> c
cuncurry = cunfactor . uncurry . (cfactor <$>)

ccurry :: ((a,b) .-> c) -> (a -> b .-> c)
ccurry = (cunfactor <$>) . curry . cfactor

fork :: (a -> EnumProc b) -> a .-> b
fork = AlgFork

compalg :: Computation (a .-> b) -> a .-> b
compalg c = withorder (compalg_order c)

compalg_order :: ExecOrder t => Computation (a .-> b) -> t -> a -> EnumProc b
compalg_order c x a = execorder x (\g -> runorder x g a) (runorder x c ())

algcomp :: (a .-> Computation b) -> a .-> b
algcomp f = withorder (algcomp_order f)

algcomp_order :: ExecOrder t => (a .-> Computation b) -> t -> a -> EnumProc b
algcomp_order f x a = execorder x (\g -> runorder x g ()) (runorder x f a)

(.+.) :: Algorithm a b -> Algorithm a b -> Algorithm a b
f .+. g = compalg (ecomp (f --> g --> Empty))

class ExecOrder t where
	execorder :: t -> (a -> EnumProc b) -> EnumProc a -> EnumProc b

runorder :: ExecOrder t => t -> (a .-> 	b) -> a -> EnumProc b
runorder x (AlgDir f) y = single_enum (f y)
runorder x (AlgFork f) y = f y
runorder x (AlgStep f g) y = execorder x (runorder x f) (runorder x g y)
runorder x (AlgFilter f) y = fromJust <$> (efilter isJust (single_enum (f y)))
runorder x (AlgEval f) y = f x y

runcomp :: ExecOrder t => t -> (() .-> a) -> EnumProc a
runcomp x alg = runorder x alg ()


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
-- Note that the reason this is not simply done by compressing the first n is that the result of this is an EnumProc that will have Continues corresponding to any Continues that the source EnumProcs may have, meaning that the result will be safe (each step will be finite) even when the EnumProc given does not have n elements. It may, however, not be complete (fair).
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

default_diag :: Diagonalize
default_diag = Diagonalize False False 1 1 False

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

-- This instances purposely DO NOT use the Applicative and/or Monad instances for EnumProc, as those assume a search order.

instance Functor (Algorithm a) where
	fmap f x = (alg f) ... x

instance Applicative (Algorithm a) where
	pure x = alg_produce (\_ -> x) alg_empty
	f <*> x = withorder (applicative_order f x)

applicative_order :: ExecOrder t => (a .-> (b -> c)) -> (a .-> b) -> t -> a -> EnumProc c
applicative_order f x t a = execorder t (\g -> g <$> (runorder t x a)) (runorder t f a)

instance Monad (Algorithm a) where
	return = pure
	b >>= f = withorder (monad_order b f)

monad_order :: ExecOrder t => (a .-> b) -> (b -> (a .-> c)) -> t -> a -> EnumProc c
monad_order b f x a = execorder x (\b2 -> runorder x (f b2) a) (runorder x b a)

anymap_alg :: Mappable a (EnumProc b) ta (EnumProc tb) => (a .-> b) -> (ta .-> tb)
anymap_alg f = withorder (anymap_alg_order f)

anymap_alg_order :: (Mappable a (EnumProc b) ta (EnumProc tb), ExecOrder t) => (a .-> b) -> t -> ta -> EnumProc tb
anymap_alg_order f x ta = anymap (runorder x f) ta

alg_traverse :: Traversable t => (a .-> b) -> t a .-> (t b)
alg_traverse = alg_traversal traverse

alg_traversal :: Control.Lens.Traversal s t a b -> (a .-> b) -> s .-> t
alg_traversal t = cunfactor . t . cfactor


-- Some utilities
-- Note that here the "Computation" on the arguments and the result is different in the sense of how many results it returns, but NOT in the sense of in what order the checks are done.
-- In some sense, these are "folds in an arbitrary order".
compor :: Computation Bool -> Computation Bool
compor = withenumcomp eor

compand :: Computation Bool -> Computation Bool
compand = withenumcomp eand

company :: (a .-> Bool) -> Computation a -> Computation Bool
company f a = compor (f ... a)

compall :: (a .-> Bool) -> Computation a -> Computation Bool
compall f a = compand (f ... a)


-- W/Provenance operators

type ProvAlgorithm p a = ProvenanceT p (Algorithm (a :- p))
type ProvComputation p = ProvAlgorithm p ()

idalgprov :: Monoid p => p -> ProvAlgorithm p a a
idalgprov p = algprov p id

algprov :: Monoid p => p -> (a -> b) -> ProvAlgorithm p a b
algprov p f = ProvenanceT (alg ((f >: p) <*>))

algprov_prov :: Monoid p => (a -> (b :- p)) -> ProvAlgorithm p a b
algprov_prov f = ProvenanceT (alg (\(Provenance a p1) -> p1 >:> (f a)))

algfilterprov :: Monoid p => p -> (a -> Maybe b) -> ProvAlgorithm p a b
algfilterprov p f = ProvenanceT (algfilter (sequence . ((f >: p) <*>)))

algfilterprov_prov :: Monoid p => (a -> Maybe (b :- p)) -> ProvAlgorithm p a b
algfilterprov_prov f = ProvenanceT (algfilter (\(Provenance a p1) -> (p1 >:>) <$> (f a)))

-- Important note: If you want to filter but keep the provenance indicating "I removed something here because of reason X", you should use your Maybe or equivalent optional type in the ProvAlgorithm itself. Otherwise, it would imply changing the whole way in which Algorithm works, or introducing a new variation of Provenance which does not contain an element but merely a Provenance. Either would complicate things unnecessarily. If you want to keep unsatisfactory solutions, do it yourself!

forkprov :: Monoid p => p -> (a -> EnumProc b) -> ProvAlgorithm p a b
forkprov p f = ProvenanceT (fork (sequence . ((f >: p) <*>)))

forkprov_prov :: Monoid p => (a -> EnumProc (b :- p)) -> ProvAlgorithm p a b
forkprov_prov f = ProvenanceT (fork (\(Provenance a p1) -> (p1 >:>) <$> (f a)))

compprov :: Monoid p => p -> a -> ProvComputation p a
compprov p x = algprov p (\_ -> x)

ecompprov :: Monoid p => p -> EnumProc a -> ProvComputation p a
ecompprov p x = forkprov p (\_ -> x)

(.:.) :: Monoid p => ProvAlgorithm p b c -> ProvAlgorithm p a b -> ProvAlgorithm p a c
x .:. y = ProvenanceT (xx ... yy) where xx = fromProvenanceT x; yy = fromProvenanceT y
infixr 0 .:.

withorderprov :: Monoid p => p -> (forall t. ExecOrder t => t -> a -> EnumProc b) -> ProvAlgorithm p a b
withorderprov p f = ProvenanceT (withorder (\t -> (sequence . (((f t) >: p) <*>))))

withorderprov_prov :: Monoid p => p -> (forall t. ExecOrder t => t -> a -> EnumProc (b :- p)) -> ProvAlgorithm p a b
withorderprov_prov p f = ProvenanceT (withorder (\t -> \(Provenance a p2) -> fmap ((p <> p2) >:>) (f t a)))

algprov_empty :: Monoid p => p -> ProvAlgorithm p a b
algprov_empty p = withorderprov p (\_ -> \_ -> Empty)

algprov_halt :: Monoid p => p -> ProvAlgorithm p a b
algprov_halt p = withorderprov p (\_ -> \_ -> Halt)

algprov_error :: Monoid p => p -> String -> ProvAlgorithm p a b
algprov_error p str = withorderprov p (\_ -> \_ -> Error str)

algprov_continue :: Monoid p => p -> ProvAlgorithm p a b -> ProvAlgorithm p a b
algprov_continue p alg = withorderprov_prov p (\x -> \a -> Continue (runorderprov x alg a))

algprov_produce :: Monoid p => p -> (a -> b) -> ProvAlgorithm p a b -> ProvAlgorithm p a b
algprov_produce p b alg = withorderprov_prov p (\x -> \a -> Produce ((b a) >: p) (runorderprov x alg a))

runorderprov :: (ExecOrder t, Monoid p) => t -> ProvAlgorithm p a b -> a -> EnumProc (b :- p)
runorderprov x f y = runorderprov_prov x f (pure y)

runorderprov_prov :: (ExecOrder t, Monoid p) => t -> ProvAlgorithm p a b -> (a :- p) -> EnumProc (b :- p)
runorderprov_prov x (ProvenanceT f) y = runorder x f y

runcompprov :: (ExecOrder t, Monoid p) => t -> ProvComputation p a -> EnumProc (a :- p)
runcompprov x f = runorderprov x f ()

algprov_uncurry :: Monoid p => ProvAlgorithm p a (ProvAlgorithm p b c) -> ProvAlgorithm p (a,b) c
algprov_uncurry f = withorderprov_prov mempty (algprov_uncurry_order f)

algprov_uncurry_order :: (ExecOrder t, Monoid p) => ProvAlgorithm p a (ProvAlgorithm p b c) -> t -> (a,b) -> EnumProc (c :- p)
algprov_uncurry_order f x (a,b) = execorder x (\(Provenance g p) -> (p >:>) <$> (runorderprov x g b)) (runorderprov x f a)

algprov_curry :: Monoid p => ProvAlgorithm p (a,b) c -> ProvAlgorithm p a (ProvAlgorithm p b c)
algprov_curry f = algprov mempty (\a -> f .:. (algprov mempty (a,)))

cfactorprov :: Monoid p => ProvAlgorithm p a b -> (a -> ProvAlgorithm p () b)
cfactorprov f a = f .:. (compprov mempty a)

cunfactorprov :: Monoid p => (a -> ProvAlgorithm p () b) -> ProvAlgorithm p a b
cunfactorprov f = withorderprov_prov mempty (cunfactorprov_order f)

cunfactorprov_order :: (ExecOrder t, Monoid p) => (a -> ProvAlgorithm p () b) -> t -> a -> EnumProc (b :- p)
cunfactorprov_order f x a = runorderprov x (f a) ()

-- Weak versions of curry/uncurry, where only one Algorithm layer exists.
cuncurryprov :: Monoid p => (a -> ProvAlgorithm p b c) -> ProvAlgorithm p (a,b) c
cuncurryprov = cunfactorprov . uncurry . (cfactorprov <$>)

ccurryprov :: Monoid p => (ProvAlgorithm p (a,b) c) -> (a -> ProvAlgorithm p b c)
ccurryprov = (cunfactorprov <$>) . curry . cfactorprov

compalgprov :: Monoid p => ProvComputation p (ProvAlgorithm p a b) -> ProvAlgorithm p a b
compalgprov c = withorderprov_prov mempty (compalgprov_order c)

compalgprov_order :: (Monoid p, ExecOrder t) => ProvComputation p (ProvAlgorithm p a b) -> t -> a -> EnumProc (b :- p)
compalgprov_order c x a = execorder x (\(Provenance g p) -> (p >:>) <$> (runorderprov x g a)) (runorderprov x c ())

algcompprov :: Monoid p => (ProvAlgorithm p a (ProvComputation p b)) -> ProvAlgorithm p a b
algcompprov f = withorderprov_prov mempty (algcompprov_order f)

algcompprov_order :: (Monoid p, ExecOrder t) => (ProvAlgorithm p a (ProvComputation p b)) -> t -> a -> EnumProc (b :- p)
algcompprov_order f x a = execorder x (\(Provenance g p) -> (p >:>) <$> (runorderprov x g ())) (runorderprov x f a)

(.+:.) :: Monoid p => ProvAlgorithm p a b -> ProvAlgorithm p a b -> ProvAlgorithm p a b
f .+:. g = compalgprov (ecompprov mempty (f --> g --> Empty))

-- Unfortunately, we need to lose previously existing provenance here. Avoiding it seems highly unlikely with the current setup.
anymap_algprov :: (Mappable a (EnumProc b) ta (EnumProc tb), Monoid p) => p -> ProvAlgorithm p a b -> ProvAlgorithm p ta tb
anymap_algprov p f = withorderprov_prov mempty (anymap_algprov_order p f)

anymap_algprov_order :: (Mappable a (EnumProc b) ta (EnumProc tb), ExecOrder t, Monoid p) => p -> ProvAlgorithm p a b -> t -> ta -> EnumProc (tb :- p)
anymap_algprov_order p f x ta = (anymap (\a -> raw <$> (runorderprov x f a)) ta) $>: p

algprov_traverse :: (Traversable t, Monoid p) => ProvAlgorithm p a b -> ProvAlgorithm p (t a) (t b)
algprov_traverse = algprov_traversal traverse

algprov_traversal :: Monoid p => Control.Lens.Traversal s t a b -> ProvAlgorithm p a b -> ProvAlgorithm p s t
algprov_traversal t = cunfactorprov . t . cfactorprov


-- Unfortunately, we're left with solving binary operators under monads manually on each case. I'll see this as a limitation of Haskell to be honest.
(.:&.) :: Monoid p => StateT s (ProvAlgorithm p b) c -> StateT s (ProvAlgorithm p a) b -> StateT s (ProvAlgorithm p a) c
x .:&. y = StateT rz
	where
		-- ax :: s -> ProvAlgorithm p b (c,s)
		ax = runStateT x;
		-- rax :: ProvAlgorithm p s (ProvAlgorithm p b (c,s))		
		rax = algprov mempty ax;
		-- rrax :: ProvAlgorithm p (s,b) (c,s)
		rrax = algprov_uncurry rax;
		-- fswap :: ProvAlgorithm p (b,s) (s,b)
		algswap = algprov mempty swap
		-- rrrax :: ProvAlgorithm p (b,s) (c,s)
		rrrax = rrax .:. algswap
		-- ay :: s -> ProvAlgorithm p a (b,s)
		ay = runStateT y;
		-- rz :: s -> ProvAlgorithm p a (c,s)
		rz = (\s -> rrrax .:. (ay s))

st_cfactorprov :: Monoid p => StateT s (ProvAlgorithm p a) b -> (a -> StateT s (ProvAlgorithm p ()) b)
st_cfactorprov st a = StateT (\s -> (cfactorprov (runStateT st s)) a)

st_cunfactorprov :: Monoid p => (a -> StateT s (ProvAlgorithm p ()) b) -> StateT s (ProvAlgorithm p a) b
st_cunfactorprov f = StateT (\s -> cunfactorprov (\a -> runStateT (f a) s))

-- Similarly for things with relevant contravariant values like traverse
st_algprov_traverse :: (Traversable t, Monoid p) => StateT s (ProvAlgorithm p a) b -> StateT s (ProvAlgorithm p (t a)) (t b)
st_algprov_traverse st = st_algprov_traversal traverse st
		
st_algprov_traversal :: Monoid p => Control.Lens.Traversal s t a b -> StateT st (ProvAlgorithm p a) b -> StateT st (ProvAlgorithm p s) t
st_algprov_traversal t st = unfactrav
	where
		facst = st_cfactorprov st
		traversed = t facst
		unfactrav = st_cunfactorprov traversed









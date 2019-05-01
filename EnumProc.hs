{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module EnumProc where

import Data.Time
import System.CPUTime
import Control.Exception
import Control.DeepSeq
import Data.Time.Clock
import Data.Time.Calendar
import System.Timeout
import Data.Semigroup

-- There are two fundamental assumptions for any instance of the type EnumProc:
--
-- 1. One step evaluation always terminates. That means that if it is continue, then the computation of the head of the continuation terminates. Same if it is produce (and so does the computation of the produced value).
-- In other words, any function producing an EnumProc type should always provide its head. Recursion needs to be after a "Continue".
--
-- 2. The enumeration may be infinite, but, conceptually, the number of steps before any given element is always finite.
-- In other words, you cannot "append" two infinite enumerations in the traditional sense. Instead, interleaving is produced.
-- Of course, this is not a property of the data itself, but of how it is computed. What this means is that safe functions returning EnumProcs will always make sure that the search is complete in this sense.
--
-- Some functions provided may produce results that violate one or both of these assumptions. These functions are considered unsafe and are prepended with the "uns_" prefix on their name to indicate this.
-- They should only be used for utility purposes, when the specific effects of the unsafety are known, but not for standard usage of the class.
--
-- The difference between Halt and Empty is that Halt forces halting the computation, whereas Empty simply means there's not more for now.
-- For instance, Halt ..+ x = Halt, whereas Empty ..+ x =  x
-- In general, Empty is the standard one. Halt is to be used when explicit termination is wanted.
-- Error is a way to avoid using Maybe's and exceptions. Instead, we incorporate computation errors into the type itself (since it is designed for developing computations/enumerations anyway).
data EnumProc t = Continue (EnumProc t) | Produce t (EnumProc t) | Halt | Empty | Error String

instance Show t => Show (EnumProc t) where
	show x = show_enumproc_run (run_enumproc x)

instance Functor EnumProc where
	fmap f (Continue x) = Continue (fmap f x)
	fmap f (Produce v x) = Produce (f v) (fmap f x)
	fmap f (Error str) = Error str
	fmap f Halt = Halt
	fmap f Empty = Empty

instance Foldable EnumProc where
	foldMap f = (foldMap f) . list_from_enum
	foldr f b = (foldr f b) . list_from_enum
	foldl f b = (foldl f b) . list_from_enum

instance Applicative EnumProc where
	pure x = single_enum x
	fs <*> en = diagonalize_apply (($ en) . fmap) fs
	en1 *> en2 = diagonalize_apply (\x -> en2) en1
	en1 <* en2 = diagonalize_apply (\x -> fmap (\y -> x) en2) en1

instance Monoid (EnumProc t) where
	mempty = Empty
	mappend = (..+)

instance Monad EnumProc where
	en >>= f = diagonalize_apply f en
	en1 >> en2 = diagonalize_apply (\_ -> en2) en1
	return x = single_enum x
	fail str = Error str

-- Halt is the equivalent of []

-- (-->) is the equivalent of (:), it is just an infix alias for Produce
(-->) :: t -> EnumProc t -> EnumProc t
v --> x = Produce v x
infixr 7 -->

-- (.>) is just an alias for Continue
(..>) :: () -> EnumProc t -> EnumProc t
_ ..> x = Continue x
infixr 7 ..>

-- E.g.: Write: 4 --> 5 --> () ..> () ..> 6 --> () ..> 7 --> Empty

-- An enumeration procedure that returns the first element and nothing else.
ehead :: EnumProc t -> EnumProc t
ehead Halt = Error "No head for halting enumeration"
ehead Empty = Error "No head for empty enumeration"
ehead (Error str) = Error str
ehead (Continue x) = Continue (ehead x)
ehead (Produce v x) = Produce v Empty

-- In the particular case of nested enumeration procedures, we can flatten at no cost
take_ehead :: EnumProc (EnumProc t) -> EnumProc t
take_ehead = take_next . ehead

etail :: EnumProc t -> EnumProc t
etail Halt = Error "No tail for halting enumeration"
etail Empty = Error "No tail for empty enumeration"
etail (Error str) = Error str
etail (Continue x) = Continue (etail x)
etail (Produce v x) = x

elength :: EnumProc t -> EnumProc Int
elength Halt = (0 --> Empty)
elength Empty = (0 --> Empty)
elength (Error str) = Error str
elength (Continue x) = Continue (elength x)
elength (Produce v x) = Continue (fmap (1 + ) (elength x))

-- I can't find anywhere a list of type classes that list implements and related functions, so I just add to them as I find them necessary.
efilter :: (t -> Bool) -> EnumProc t -> EnumProc t
efilter f Halt = Halt
efilter f Empty = Empty
efilter f (Error x) = Error x
efilter f (Continue x) = Continue (efilter f x)
efilter f (Produce v x) = if f v then (v --> (efilter f x)) else (efilter f x)

-- This is INTERLEAVING appending, NOT the same as list appending. List appending-kind of computation is provided as an unsafe function uns_append
(..+) :: EnumProc t -> EnumProc t -> EnumProc t
Halt ..+ x = Halt
Empty ..+ x = x
(Error x) ..+ y = Error x
(Continue x) ..+ y = Continue (y ..+ x)
(Produce v x) ..+ y = v --> (y ..+ x)
infixl 6 ..+

-- UNSAFE: It may produce incomplete searches (ass 2).
uns_append :: EnumProc t -> EnumProc t -> EnumProc t
uns_append Halt x = Halt
uns_append Empty x = x
uns_append (Error x) y = Error x
uns_append (Continue x) y = Continue (uns_append x y)
uns_append (Produce v x) y = v --> (uns_append x y)

econcat :: Foldable t => t (EnumProc a) -> EnumProc a
econcat procs = foldl (..+) Empty procs

-- !!! is a SAFE operation, unlike !!. It returns an enumeration procedure itself, so if there are not enough elements or they cannot be computed in finite time, the result behaves like so.
-- The element itself can always be (unsafely) extracted using uns_produce_next
(!!!) :: EnumProc t -> Int -> EnumProc t
Halt !!! _ = Error "Halting enumeration has no elements"
Empty !!! _ = Error "Empty enumeration has no elements"
(Error x) !!! _ = Error x
(Continue x) !!! i = Continue (x !!! i)
(Produce v x) !!! 0 = Produce v x
(Produce v x) !!! i = Continue (x !!! (i - 1))

-- In the particular case of nested enumeration procedures, we can flatten safely.
(!!!!) :: EnumProc (EnumProc t) -> Int -> EnumProc t
x !!!! i = take_next (x !!! i)

-- Interesting property: ereverse will always push all the results to the end of the computation.
-- So interesting, we do a function that does just that for normal enums. Essentially, only start returning results once we know the computation has terminated.
-- UNSAFE: ereverse may produce incomplete searches (ass 2).
uns_ereverse :: EnumProc t -> EnumProc t
uns_ereverse Halt = Halt
uns_ereverse Empty = Empty
uns_ereverse (Error x) = Error x
uns_ereverse (Continue x) = Continue (uns_ereverse x)
uns_ereverse (Produce v x) = Continue (uns_append (uns_ereverse x) (v --> Empty))

-- Push all the results to the end of the enumeration. Return everything in the end.
-- UNSAFE: May produce incomplete searches (ass 2).
uns_ewait :: EnumProc t -> EnumProc t
uns_ewait = uns_ewait_rec Empty

uns_ewait_rec :: EnumProc t -> EnumProc t -> EnumProc t
uns_ewait_rec r Halt = uns_append r Halt
uns_ewait_rec r Empty = uns_append r Empty
uns_ewait_rec r (Error x) = uns_append r (Error x)
uns_ewait_rec r (Continue x) = Continue (uns_ewait_rec r x)
uns_ewait_rec r (Produce v x) = Continue (uns_ewait_rec (uns_append r (v --> Empty)) x)

-- Runs the first enumeration, but without returning any results, and then runs the second one (and if the first one Halts, it halts there.)
-- UNSAFE: May produce incomplete searches (ass 2).
uns_ewaitfor :: EnumProc a -> EnumProc b -> EnumProc b
uns_ewaitfor Halt _ = Halt
uns_ewaitfor Empty x = x
uns_ewaitfor (Error x) _ = Error x
uns_ewaitfor (Continue x) y = Continue (uns_ewaitfor x y)
uns_ewaitfor (Produce _ x) y = Continue (uns_ewaitfor x y)

-- Note: ereverse, ewait and ewaitfor do respect assumption 1. It just happens that if the enumeration is infinite, then the result will be an infinite list of steps without producing any result, but each step will still be terminating.

-- Remove continues.
-- UNSAFE: May produce non-terminating steps (ass 1).
uns_ecollapse :: EnumProc t -> EnumProc t
uns_ecollapse Halt = Halt
uns_ecollapse Empty = Empty
uns_ecollapse (Error x) = Error x
uns_ecollapse (Continue x) = uns_ecollapse x
uns_ecollapse (Produce v x) = v --> (uns_ecollapse x)

eintersperse :: t -> EnumProc t -> EnumProc t
eintersperse a Halt = Halt
eintersperse a Empty = Empty
eintersperse a (Error x) = Error x
eintersperse a (Continue x) = () ..> (eintersperse a x)
eintersperse a (Produce v x) = v --> (eintersperse2 a x)

eintersperse2 :: t -> EnumProc t -> EnumProc t
eintersperse2 a Halt = Halt
eintersperse2 a Empty = Empty
eintersperse2 a (Error x) = Error x
eintersperse2 a (Continue x) = () ..> (eintersperse2 a x)
eintersperse2 a (Produce v x) = a --> v --> (eintersperse2 a x)

eintercalate :: (Foldable t, Monoid (t a)) => t a -> EnumProc (t a) -> t a
eintercalate xs xss = foldMap id (eintersperse xs xss)

etranspose :: EnumProc (EnumProc t) -> EnumProc (EnumProc t)
etranspose x = (take_each x) --> (etranspose (fmap etail x))

esubsequences :: EnumProc t -> EnumProc (EnumProc t)
esubsequences Halt = Produce Halt Empty
esubsequences Empty = Produce Empty Empty
esubsequences (Error str) = Error str
esubsequences (Continue x) = Continue (esubsequences x)
esubsequences (Produce v x) = (Empty --> (fmap (v -->) rec1)) ..+ rec2 where rec1 = esubsequences x; rec2 = esubsequences2 x

-- All but Empty/Halt
esubsequences2 :: EnumProc t -> EnumProc (EnumProc t)
esubsequences2 Halt = Empty
esubsequences2 Empty = Empty
esubsequences2 (Error str) = Error str
esubsequences2 (Continue x) = Continue (esubsequences2 x)
esubsequences2 (Produce v x) = fmap (v -->) rec where rec = esubsequences x

epermutations :: EnumProc t -> EnumProc (EnumProc t)
epermutations Halt = Produce Halt Empty
epermutations Empty = Produce Empty Empty
epermutations (Error str) = Produce (Error str) Empty
epermutations (Continue x) = Continue (epermutations x)
epermutations (Produce v x) = (v --> x) --> (epermutations2 (v --> x))

-- All except leaving everything the same way
epermutations2 :: EnumProc t -> EnumProc (EnumProc t)
epermutations2 Halt = Empty
epermutations2 Empty = Empty
epermutations2 (Error str) = Error str
epermutations2 (Continue x) = Continue (epermutations2 x)
epermutations2 (Produce v x) = (diagonalize_apply (epermutations_insert2 v) (epermutations x)) ..+ (fmap (v -->) (epermutations2 x))

epermutations_insert :: t -> EnumProc t -> EnumProc (EnumProc t)
epermutations_insert v Halt = Produce (v --> Halt) Empty
epermutations_insert v Empty = Produce (v --> Empty) Empty
epermutations_insert v (Error str) = Produce (v --> (Error str)) Empty
epermutations_insert v (Continue x) = Continue (epermutations_insert v x)
epermutations_insert v (Produce w y) = (v --> w --> y) --> (fmap (w -->) (epermutations_insert v y))

-- Not in the beginning
epermutations_insert2 :: t -> EnumProc t -> EnumProc (EnumProc t)
epermutations_insert2 v Halt = Empty
epermutations_insert2 v Empty = Empty
epermutations_insert2 v (Error str) = Error str
epermutations_insert2 v (Continue x) = Continue (epermutations_insert2 v x)
epermutations_insert2 v (Produce w y) = fmap (w -->) (epermutations_insert v y)

single_enum :: t -> EnumProc t
single_enum x = Produce x Empty

-- Surprisingly, bottom is safe. It respects assumption 1 because each step is terminating. It respects assumption 2 because, since it does not produce any results, there is a finite set of steps before each of them.
bottom :: EnumProc t
bottom = Continue bottom

-- UNSAFE: It may produce non-terminating steps, since lists themselves cannot be checked for safety (ass 1). It may also violate assumption 2, but the semantics of what this means here is unclear.
uns_enum_from_list :: [t] -> EnumProc t
uns_enum_from_list [] = Empty
uns_enum_from_list (x:xs) = Produce x (uns_enum_from_list xs)

-- This function may make it seem like [t] and EnumProc t are the same type, but the fundamental difference is the Continue construct that ensures one-step termination. In this function, we lose this head into recursion, potentially making the computation of the list hang up when there is no next value.
list_from_enum :: EnumProc t -> [t]
list_from_enum Empty = []
list_from_enum Halt = []
list_from_enum (Error x) = error x
list_from_enum (Continue x) = list_from_enum x
list_from_enum (Produce v x) = v:(list_from_enum x)

step :: EnumProc t -> EnumProc t
step (Continue next) = next
step (Produce v next) = next
step Halt = Halt
step Empty = Empty
step (Error x) = Error x

nstep :: Int -> EnumProc t -> EnumProc t
nstep n x = (iterate step x) !! n

-- UNSAFE: This function may produce steps that do not terminate (ass 1).
uns_next_result :: EnumProc t -> EnumProc t
uns_next_result x = case (step x) of {Continue y -> uns_next_result y; Produce v y -> Produce v y; Halt -> Halt; Empty -> Empty; Error x -> Error x}

-- UNSAFE: This may produce steps that do not terminate (ass 1).
uns_produce_next :: EnumProc t -> t
uns_produce_next Halt = error "No next element for halting enumeration"
uns_produce_next Empty = error "No next element for empty enumeration"
uns_produce_next (Error x) = error x
uns_produce_next (Continue x) = uns_produce_next x
uns_produce_next (Produce v x) = v

run_enumproc :: EnumProc t -> [EnumProc t]
run_enumproc (Continue x) = (Continue x):(run_enumproc x)
run_enumproc (Produce v x) = (Produce v x):(run_enumproc x)
run_enumproc Halt = [Halt]
run_enumproc Empty = []
run_enumproc (Error x) = [Error x]

run_enumproc_next :: EnumProc t -> [EnumProc t]
run_enumproc_next (Continue x) = (Continue x):(run_enumproc_next x)
run_enumproc_next (Produce v x) = [Produce v x]
run_enumproc_next Halt = [Halt]
run_enumproc_next Empty = []
run_enumproc_next (Error x) = [Error x]

show_enumproc_run :: Show t => [EnumProc t] -> String
show_enumproc_run [] = ""
show_enumproc_run ((Continue x):xs) = "() ..> " ++ (show_enumproc_run xs)
show_enumproc_run ((Produce v x):xs) = "(" ++ (show v) ++ ") --> " ++ (show_enumproc_run xs)
show_enumproc_run (Halt:xs) = " Halt."
-- This should not happen really.
show_enumproc_run (Empty:xs) = ""
show_enumproc_run ((Error x):xs) = "\n\nError: " ++ x ++ "\n"

-- Just use this if you just want to see an EnumProc run.
do_run_enumproc :: Show t => EnumProc t -> IO ()
do_run_enumproc x = putStr (show_enumproc_run (run_enumproc x))

show_collapsed_enumproc :: Show t => EnumProc t -> IO ()
show_collapsed_enumproc x = putStr (show (uns_ecollapse x))

diagonalize_enumproc :: EnumProc (EnumProc t) -> EnumProc t
diagonalize_enumproc x = diagonalize_enumproc_rec [] [] x

diagonalize_apply :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
diagonalize_apply f x = diagonalize_enumproc (fmap f x)

-- Note: We reverse so that the order is predicted, but it would be more efficient without doing this.
diagonalize_enumproc_rec :: [EnumProc t] -> [EnumProc t] -> EnumProc (EnumProc t) -> EnumProc t
diagonalize_enumproc_rec [] [] (Continue x) = Continue (diagonalize_enumproc_rec [] [] x)
diagonalize_enumproc_rec [] [] (Produce en x) = Continue (diagonalize_enumproc_rec [] [en] x)
diagonalize_enumproc_rec [] [] Halt = Halt
diagonalize_enumproc_rec [] [] Empty = Empty
diagonalize_enumproc_rec [] [] (Error x) = Error x
diagonalize_enumproc_rec done [] (Continue x) = Continue (diagonalize_enumproc_rec [] (reverse done) x)
diagonalize_enumproc_rec done [] (Produce en x) = Continue (diagonalize_enumproc_rec [] (reverse (en:done)) x)
diagonalize_enumproc_rec done [] Halt = Continue (diagonalize_enumproc_rec [] done Halt)
diagonalize_enumproc_rec done [] Empty = Continue (diagonalize_enumproc_rec [] done Empty)
diagonalize_enumproc_rec done [] (Error x) = Error x
diagonalize_enumproc_rec done ((Continue nx):nxs) x = Continue (diagonalize_enumproc_rec (nx:done) nxs x)
diagonalize_enumproc_rec done ((Produce v nx):nxs) x = Produce v (diagonalize_enumproc_rec (nx:done) nxs x)
diagonalize_enumproc_rec done (Halt:nxs) x = Continue (diagonalize_enumproc_rec done nxs x)
diagonalize_enumproc_rec done (Empty:nxs) x = Continue (diagonalize_enumproc_rec done nxs x)
diagonalize_enumproc_rec done ((Error x):nxs) _ = Error x

-- The important aspect of this function is that it "bends" the type. It goes "horizontally" to find the next element, and then applies something to that element, "vertically". But all of this with step-wise termination safety, so that even if there's no next element, the resulting EnumProc is still safe (which differs from simply obtaining next and THEN applying something to it).
-- It is very related to diagonalize in that they are both "enumeration flattening" functions. But, while diagonalize keeps completion by diagonalizing the running (and therefore incurring in space performance overheads and overall irregular ordering of results), take next maintains these by only computing the first one. It is, of course, impossible to have both.
take_next :: EnumProc (EnumProc t) -> EnumProc t
take_next Halt = Halt
take_next Empty = Empty
take_next (Error x) = Error x
take_next (Continue x) = Continue (take_next x)
take_next (Produce v _) = v

apply_next :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
apply_next f x = take_next (fmap f x)

-- And the dual, which instead of taking the first element of the enumeration, takes the enumeration of first elements.
take_each :: EnumProc (EnumProc t) -> EnumProc t
take_each Halt = Halt
take_each Empty = Empty
take_each (Error x) = Error x
take_each (Continue x) = Continue (take_each x)
take_each (Produce Halt x) = Continue (take_each x)
take_each (Produce Empty x) = Continue (take_each x)
take_each (Produce (Error str) x) = Error str
take_each (Produce (Continue x) y) = Continue (take_each (Produce x y))
take_each (Produce (Produce v _) y) = v --> (take_each y)

apply_each :: (a -> EnumProc b) -> EnumProc a -> EnumProc b
apply_each f x = take_each (fmap f x)


-- Provenance information for enumeration procedures
-- It is implemented as a wrapper to offer useful functions for seamless use without having to worry too much about the provenance and its handling.
data Provenance p t = Provenance t p

instance (Show t, Show p) => Show (Provenance p t) where
	show (Provenance x p) = (show x) ++ " (" ++ (show p) ++ ")"

instance Eq t => Eq (Provenance p t) where
	(Provenance x1 _) == (Provenance x2 _) = x1 == x2

instance Functor (Provenance p) where
	fmap f (Provenance x p) = Provenance (f x) p

raw :: Provenance p t -> t
raw (Provenance x _) = x

(>:) :: t -> p -> Provenance p t
x >: p = Provenance x p
infixl 9 >:

(>>:) :: Semigroup p => Provenance p t -> p -> Provenance p t
(Provenance x p1) >>: p2 = Provenance x (p1 <> p2)
infixl 8 >>:

(>:>) :: Semigroup p => p -> Provenance p t -> Provenance p t
p1 >:> (Provenance x p2) = Provenance x (p1 <> p2)
infixr 8 >:>

type ProvEnumProc p t = EnumProc (Provenance p t)

flatten_provenance :: (Semigroup p,Functor f) => Provenance p (f (Provenance p t)) -> f (Provenance p t)
flatten_provenance (Provenance c p) = fmap ((>:>) p) c

diagonalize_with_prov :: Semigroup p => ProvEnumProc p (ProvEnumProc p t) -> ProvEnumProc p t
diagonalize_with_prov = diagonalize_enumproc . (fmap flatten_provenance)


-- Apply a function and append to the provenance indicating something
apply_with_prov :: Semigroup p => (a -> b) -> (a -> p) -> Provenance p a -> Provenance p b
apply_with_prov f prov (Provenance ax px) = (f ax) >: px >>: (prov ax)

-- The standard way to use the above is on functors
map_with_prov :: (Functor f, Semigroup p) => (a -> b) -> (a -> p) -> f (Provenance p a) -> f (Provenance p b)
map_with_prov f prov = fmap (apply_with_prov f prov)

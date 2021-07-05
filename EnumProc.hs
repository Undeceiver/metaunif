{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module EnumProc where

import Data.Time
import System.CPUTime
import Control.Exception
import Control.DeepSeq
import Data.Time.Clock
import Data.Time.Calendar
import System.Timeout
import Data.Semigroup
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Monad.Trans.Class
import HaskellPlus
import Data.Maybe
import Control.Monad.ST
import Control.Applicative
import System.IO.Silently
import SimplePerformance
import System.IO


-- There are two fundamental assumptions for any instance of the type EnumProc:
--
-- 1. One step evaluation always terminates. That means that if it is continue, then the computation of the head of the continuation terminates. Same if it is produce (and so does the computation of the produced value).
-- In other words, any function producing an EnumProc type should always provide its head. Recursion needs to be after a "Continue".
-- More precisely, any safe element of type EnumProc t is always in Head Normal Form.
--
-- 2. The enumeration may be infinite, but, conceptually, the number of steps before any given element is always finite.
-- In other words, you cannot "append" two infinite enumerations in the traditional sense. Instead, interleaving is produced.
-- Of course, this is not a property of the data itself, but of how it is computed. What this means is that safe functions returning EnumProcs will always make sure that the search is complete in this sense.
-- Note that this is not really a fully achievable assumption semantically speaking. For example, for any enumeration, en \\\ bottom will always produce an infinite succession of void steps, even though conceptually, en \\\ bottom == en. There is no way around this, there is no computation that will subtract a non-terminating enumeration from any enumeration and produce any result (we can never be sure that an element in the enumeration will not suddenly appear. We know in bottom it will not, but that is because we are reasoning at a higher level).
-- More precisely this happens when negation of enumerations essentially happens. Since enumerations are semi-decidable, negating them is co-semi-decidable.
-- All in all, only (\\\) and similar functions should produce this behaviour. If avoiding their usage, assumption 2 should be fulfilled.
--
-- Some functions provided may produce results that violate one or both of these assumptions. These functions are considered unsafe and are prepended with the "uns_" prefix on their name to indicate this.
-- They should only be used for utility purposes, when the specific effects of the unsafety are known, but not for standard usage of the class.
--
-- In general, even safe functions may return unsafe results if functions passed as arguments to them are unsafe conceptually.
-- For example, fmap, if given a non-terminating function, will violate both assumptions, because the application of fmap to the first element will not terminate (nor produce infinite Continues).
-- For this purpose, we provide extra-safe functions, which are versions of these functions such that whenever they take a function as argument, the return type of the function must be wrapped in an EnumProc. These guarantee safety in all cases. We preffix these with "es_"
--
-- The difference between Halt and Empty is that Halt forces halting the computation, whereas Empty simply means there's not more for now.
-- For instance, Halt ..+ x = Halt, whereas Empty ..+ x = x
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

-- NOTE that foldl on an EnumProc (EnumProc t) is unsafe, as it will need to find the last element of the enumeration in order to produce any result at all.
-- foldr, on the other hand, is still safe.
instance Foldable EnumProc where
	foldr f b = (foldr f b) . list_from_enum	

es_foldr :: (a -> EnumProc b -> EnumProc b) -> EnumProc b -> EnumProc a -> EnumProc b
es_foldr f b Empty = b
es_foldr f b Halt = Halt
es_foldr f b (Error str) = Error str
es_foldr f b (Continue x) = Continue (es_foldr f b x)
es_foldr f b (Produce v x) = f v (Continue (es_foldr f b x))

-- Coinductive fold
-- Thanks to Olaf Klinke for providing this idea.
class CoFoldable (f :: * -> *) where
	cofoldr :: (a -> b -> b) -> f a -> b

instance CoFoldable EnumProc where	
	cofoldr f Empty = undefined
	cofoldr f Halt = undefined
	cofoldr f (Error str) = error str
	cofoldr f (Continue x) = cofoldr f x
	cofoldr f (Produce v x) = f v (cofoldr f x)

es_cofoldr :: (a -> EnumProc b -> EnumProc b) -> EnumProc a -> EnumProc b
es_cofoldr f Empty = bottom
es_cofoldr f Halt = bottom
es_cofoldr f (Error str) = Error str
es_cofoldr f (Continue x) = Continue (es_cofoldr f x)
es_cofoldr f (Produce v x) = f v (es_cofoldr f x)

-- Note that this can cause unsafe non-termination depending on the behaviour of the applicative's fmap!
instance Traversable EnumProc where
	traverse f Empty = pure Empty
	traverse f Halt = pure Halt
	traverse f (Error str) = pure (Error str)
	traverse f (Continue x) = Continue <$> (traverse f x)
	traverse f (Produce v x) = liftA2 Produce (f v) (traverse f x)

instance Applicative EnumProc where
	pure x = single_enum x
	--fs <*> en = diagonalize_apply (($ en) . fmap) fs
	fs <*> en = es_econcat (fmap (($ en) . fmap) fs)
	--en1 *> en2 = diagonalize_apply (\x -> en2) en1
	en1 *> en2 = es_econcat (fmap (\x -> en2) en1)
	--en1 <* en2 = diagonalize_apply (\x -> fmap (\y -> x) en2) en1
	en1 <* en2 = es_econcat (fmap (\x -> fmap (\y -> x) en2) en1)

-- Extra safe version
(<**>) :: EnumProc (a -> EnumProc b) -> EnumProc a -> EnumProc b
fs <**> en = es_econcat (fmap (take_each . ($ en) . fmap) fs)
infixl 7 <**>

instance Semigroup (EnumProc t) where
	(<>) = (..+)
	stimes 0 x = Empty
	-- The continue here is actually for the case that some instance of integral has n-1 not terminate. If this does not happen this continue is unnecessary.
	stimes n x = x ..+ (Continue (stimes (n-1) x))

instance Monoid (EnumProc t) where
	mempty = Empty
	mappend = (..+)

-- WARNING: Be very careful with using the do syntax for this Monad: Not everything you do inside is guaranteed safe (as per the assumptions above). Make sure that you know what you are doing if you use the do syntax. If you're not sure, use only the safe functions provided and use the Monad operators explicitly.
instance Monad EnumProc where
	en >>= f = diagonalize_apply f en
	--en >>= f = es_econcat (fmap f en)
	en1 >> en2 = diagonalize_apply (\_ -> en2) en1
	--en1 >> en2 = es_econcat (fmap (\_ -> en2) en1)
	return x = single_enum x
	fail str = Error str

-- We may wish to produce monad actions over EnumProcs. This is not the same as a monad transformer, the types do not match. This could be implemented from a monad transformer, but a generic monad transformer cannot be implemented from this.
(..>>=) :: Monad m => EnumProc (m a) -> (a -> m b) -> EnumProc (m b)
(..>>=) = (>$>=)
infixl 7 ..>>=


-- (-->) is the equivalent of (:), it is just an infix alias for Produce
(-->) :: t -> EnumProc t -> EnumProc t
v --> x = Produce v x
infixr 5 -->

-- () ..> is just an alias for Continue
(..>) :: () -> EnumProc t -> EnumProc t
_ ..> x = Continue x
infixr 5 ..>

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
efilter f (Produce v x) = if f v then (v --> (efilter f x)) else (Continue (efilter f x))

es_efilter :: (t -> EnumProc Bool) -> EnumProc t -> EnumProc t
es_efilter f en = en >>= (\x -> (f x) >>= (\y -> if y then (return x) else Empty))

--es_efilter f Halt = Halt
--es_efilter f Empty = Empty
--es_efilter f (Error x) = Error x
--es_efilter f (Continue x) = Continue (es_efilter f x)
--es_efilter f (Produce v x) = do {r <- f v; if r then (v --> (es_efilter f x)) else (Continue (es_efilter f x))}

m_efilter :: Monad m => (a -> m Bool) -> EnumProc a -> m (EnumProc a)
m_efilter f l = traverse_collect ((fmap fromJust) . (efilter isJust)) (\a -> do {b <- f a; if b then (return (Just a)) else (return Nothing)}) l


-- A useful case of efilter with Maybe types.
efilter_mb :: EnumProc (Maybe t) -> EnumProc t
efilter_mb = (fromJust <$>) . (efilter isJust)

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
econcat procs = foldr (..+) Empty procs

es_econcat :: EnumProc (EnumProc a) -> EnumProc a
--es_econcat procs = es_foldr (..+) Empty procs
es_econcat = diagonalize_enumproc

(&&?) :: Bool -> Bool ->? Bool
(&&?) True = varf id
(&&?) False = constf False

eifelse :: EnumProc Bool -> EnumProc t -> EnumProc t -> EnumProc t
eifelse cond true false = cond >>= (\r -> if r then true else false)

eand :: EnumProc Bool -> EnumProc Bool
eand = es_foldr (\x -> ((apply_next_constf ((varf return) .? ((&&?) x))) $?)) (return True)

(||?) :: Bool -> Bool ->? Bool
(||?) True = constf True
(||?) False = varf id

eor :: EnumProc Bool -> EnumProc Bool
eor = es_foldr (\x -> ((apply_next_constf ((varf return) .? ((||?) x))) $?)) (return False)

eany :: (a -> EnumProc Bool) -> EnumProc a -> EnumProc Bool
eany p en = eor (take_each (fmap p en))

eall :: (a -> EnumProc Bool) -> EnumProc a -> EnumProc Bool
eall p en = eand (take_each (fmap p en))

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

-- Note that the following functions (intersperse and intercalate) are unlikely to be useful, given the semantics of (..+), but we can implement them... (I did before I properly defined the semantics of (..+))
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

es_eintercalate :: EnumProc a -> EnumProc (EnumProc a) -> EnumProc a
es_eintercalate xs xss = es_econcat (eintersperse xs xss)

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
--epermutations2 (Produce v x) = (diagonalize_apply (epermutations_insert2 v) (epermutations x)) ..+ (fmap (v -->) (epermutations2 x))
epermutations2 (Produce v x) = (es_econcat (fmap (epermutations_insert2 v) (epermutations x))) ..+ (fmap (v -->) (epermutations2 x))

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

escanl :: (b -> a -> b) -> b -> EnumProc a -> EnumProc b
escanl f cur Halt = (cur --> Halt)
escanl f cur Empty = (cur --> Empty)
escanl f cur (Error str) = (cur --> Error str)
escanl f cur (Continue x) = Continue (escanl f cur x)
escanl f cur (Produce v x) = cur --> (escanl f (f cur v) x)

es_escanl :: (b -> a -> EnumProc b) -> b -> EnumProc a -> EnumProc b
es_escanl f cur Halt = (cur --> Halt)
es_escanl f cur Empty = (cur --> Empty)
es_escanl f cur (Error str) = (cur --> Error str)
es_escanl f cur (Continue x) = Continue (es_escanl f cur x)
es_escanl f cur (Produce v x) = cur --> do {r <- f cur v; es_escanl f r x}

-- UNSAFE: escanr may have steps that do not terminate when the enumeration is infinite
uns_escanr :: (a -> b -> b) -> b -> EnumProc a -> EnumProc b
uns_escanr f cur Halt = (cur --> Halt)
uns_escanr f cur Empty = (cur --> Empty)
uns_escanr f cur (Error str) = (cur --> Error str)
uns_escanr f cur (Continue x) = Continue (uns_escanr f cur x)
uns_escanr f cur (Produce v x) = (f v (uns_produce_next (ehead prev))) --> prev where prev = (uns_escanr f cur x)

eiterate :: (a -> a) -> a -> EnumProc a
eiterate f x = x --> (fmap f (eiterate f x))

es_eiterate :: (a -> EnumProc a) -> a -> EnumProc a
es_eiterate f x = x --> ((es_eiterate f x) >>= f)

erepeat :: a -> EnumProc a
erepeat x = x --> (erepeat x)

ereplicate :: Int -> a -> EnumProc a
ereplicate 0 _ = Empty
ereplicate n x = x --> (ereplicate (n - 1) x)

-- Note that, to ensure safety, our functions generally do not allow concatenating each other, and so this function is essentially against the usual things that you would like to do with enumerations. Therefore, we consider it unsafe. Indeed, cycling an infinite list creates an infinite set of infinite lists, but only the first instance is visited. This is all semantics, really, and the behaviour is clear, but we consider this function unsafe because it technically is and it does not provide a funtionality that one would usually want with enumeration procedures
uns_ecycle :: EnumProc a -> EnumProc a
uns_ecycle x = uns_ecycle_rec Empty x

uns_ecycle_rec :: EnumProc a -> EnumProc a -> EnumProc a
uns_ecycle_rec prev Empty = uns_ecycle prev
uns_ecycle_rec prev Halt = Halt
uns_ecycle_rec prev (Error str) = Error str
uns_ecycle_rec prev (Continue x) = Continue (uns_ecycle_rec prev x)
uns_ecycle_rec prev (Produce v x) = v --> (uns_ecycle_rec prev x)

-- A semantically more adequate version of cycle is to econcat erepeat, same as cycle == concat . repeat. The ordering will be strange, it won't be exactly a "cycle", but it will be an infinite concatenation of an enumeration with itself, diagonalized!
-- In other words: It is an enumeration that produces an infinite amount of each element in the enumeration provided, all safely.
ecycle :: EnumProc a -> EnumProc a
ecycle = es_econcat . erepeat

etake :: Int -> EnumProc t -> EnumProc t
etake 0 _ = Empty
etake n Empty = Empty
etake n Halt = Halt
etake n (Error str) = Error str
etake n (Continue x) = Continue (etake n x)
etake n (Produce v x) = v --> (etake (n-1) x)

-- Counts continues
etakeSteps :: Int -> EnumProc t -> EnumProc t
etakeSteps 0 _ = Empty
etakeSteps n Empty = Empty
etakeSteps n Halt = Halt
etakeSteps n (Error str) = Error str
etakeSteps n (Continue x) = Continue (etakeSteps (n-1) x)
etakeSteps n (Produce v x) = v --> (etakeSteps (n-1) x)

etakeWhile :: (a -> Bool) -> EnumProc a -> EnumProc a
etakeWhile _ Empty = Empty
etakeWhile _ Halt = Halt
etakeWhile _ (Error str) = Error str
etakeWhile p (Continue x) = Continue (etakeWhile p x)
etakeWhile p (Produce v x) | p v = v --> (etakeWhile p x)
etakeWhile p (Produce v x) = Empty

es_etakeWhile :: (a -> EnumProc Bool) -> EnumProc a -> EnumProc a
es_etakeWhile _ Empty = Empty
es_etakeWhile _ Halt = Halt
es_etakeWhile _ (Error str) = Error str
es_etakeWhile p (Continue x) = Continue (es_etakeWhile p x)
es_etakeWhile p (Produce v x) = do {r <- p v; if r then (v --> es_etakeWhile p x) else Empty}

edrop :: Int -> EnumProc t -> EnumProc t
edrop 0 x = x
edrop n Empty = Empty
edrop n Halt = Halt
edrop n (Error str) = Error str
edrop n (Continue x) = Continue (edrop n x)
edrop n (Produce v x) = Continue (edrop (n-1) x)

edropWhile :: (a -> Bool) -> EnumProc a -> EnumProc a
edropWhile _ Empty = Empty
edropWhile _ Halt = Halt
edropWhile _ (Error str) = Error str
edropWhile p (Continue x) = Continue (edropWhile p x)
edropWhile p (Produce v x) | p v = Continue (edropWhile p x)
edropWhile p (Produce v x) = v --> x

es_edropWhile :: (a -> EnumProc Bool) -> EnumProc a -> EnumProc a
es_edropWhile _ Empty = Empty
es_edropWhile _ Halt = Halt
es_edropWhile _ (Error str) = Error str
es_edropWhile p (Continue x) = Continue (es_edropWhile p x)
es_edropWhile p (Produce v x) = do {r <- p v; if r then (Continue (es_edropWhile p x)) else (v --> x)}

egroupBy :: (a -> a -> Bool) -> EnumProc a -> EnumProc (EnumProc a)
egroupBy _ Empty = Empty
egroupBy _ Halt = Halt
egroupBy _ (Error str) = Error str
egroupBy eq (Continue x) = Continue (egroupBy eq x)
egroupBy eq (Produce v x) = case (egroupBy_rec eq v x) of {(cur,next) -> (v --> cur) --> (egroupBy eq next)} 

egroupBy_rec :: (a -> a -> Bool) -> a -> EnumProc a -> (EnumProc a, EnumProc a)
egroupBy_rec _ _ Empty = (Empty, Empty)
egroupBy_rec _ _ Halt = (Empty, Halt)
egroupBy_rec _ _ (Error str) = (Empty, Error str)
egroupBy_rec eq e (Continue x) = case (egroupBy_rec eq e x) of {(cur,next) -> (() ..> cur, () ..> next)}
egroupBy_rec eq e (Produce v x) | eq e v = case (egroupBy_rec eq e x) of {(cur,next) -> (v --> cur, () ..> next)}
egroupBy_rec eq e (Produce v x) = (Empty,v --> x)

es_egroupBy :: (a -> a -> EnumProc Bool) -> EnumProc a -> EnumProc (EnumProc a)
es_egroupBy _ Empty = Empty
es_egroupBy _ Halt = Halt
es_egroupBy _ (Error str) = Error str
es_egroupBy eq (Continue x) = Continue (es_egroupBy eq x)
es_egroupBy eq (Produce v x) = case (es_egroupBy_rec eq v x) of {(cur,next) -> (v --> cur) --> (es_egroupBy eq next)}

es_egroupBy_rec :: (a -> a -> EnumProc Bool) -> a -> EnumProc a -> (EnumProc a, EnumProc a)
es_egroupBy_rec _ _ Empty = (Empty,Empty)
es_egroupBy_rec _ _ Halt = (Empty,Halt)
es_egroupBy_rec _ _ (Error str) = (Empty, Error str)
es_egroupBy_rec eq e (Continue x) = case (es_egroupBy_rec eq e x) of {(cur,next) -> (() ..> cur, () ..> next)}
es_egroupBy_rec eq e (Produce v x) = (rcur,rnext) where r = eq e v; (curtrue,nexttrue) = case (es_egroupBy_rec eq e x) of {(cur,next) -> (v --> cur, () ..> next)}; (curfalse,nextfalse) = (Empty, v --> x); rcur = r >>= (\rr -> if rr then curtrue else curfalse); rnext = r >>= (\rr -> if rr then nexttrue else nextfalse)

-- To make egroup truly safe we'd have to implement equality as a function returning an EnumProc satisfying our assumptions.
egroup :: Eq a => EnumProc a -> EnumProc (EnumProc a)
egroup = egroupBy (==)

einits :: EnumProc a -> EnumProc (EnumProc a)
einits Empty = (Empty --> Empty)
einits Halt = (Empty --> Halt)
einits (Error str) = (Empty --> Error str)
einits (Continue x) = (Empty --> (fmap Continue (einits x)))
einits (Produce v x) = (Empty --> (fmap (v -->) (einits x)))

etails :: EnumProc a -> EnumProc (EnumProc a)
etails Empty = (Empty --> Empty)
etails Halt = (Empty --> Halt)
etails (Error str) = (Empty --> Error str)
etails (Continue x) = (() ..> x) --> (etails x)
etails (Produce v x) = (v --> x) --> (etails x)

eelem :: Eq t => t -> EnumProc t -> EnumProc Bool
eelem x Empty = (False --> Empty)
eelem x Halt = (False --> Halt)
eelem x (Error str) = Error str
eelem x (Continue y) = Continue (eelem x y)
eelem x (Produce v y) | x == v = (True --> Empty)
eelem x (Produce v y) = Continue (eelem x y)

efind :: (t -> Bool) -> EnumProc t -> EnumProc (Maybe t)
efind p Empty = (Nothing --> Empty)
efind p Halt = (Nothing --> Halt)
efind p (Error str) = Error str
efind p (Continue x) = Continue (efind p x)
efind p (Produce v x) | p v = (Just v --> Empty)
efind p (Produce v x) = Continue (efind p x)

es_efind :: (t -> EnumProc Bool) -> EnumProc t -> EnumProc (Maybe t)
es_efind p Empty = (Nothing --> Empty)
es_efind p Halt = (Nothing --> Halt)
es_efind p (Error str) = Error str
es_efind p (Continue x) = Continue (es_efind p x)
es_efind p (Produce v x) = do {r <- p v; if r then (Just v --> Empty) else (Continue (es_efind p x))}

epartition :: (t -> Bool) -> EnumProc t -> (EnumProc t, EnumProc t)
epartition p Empty = (Empty,Empty)
epartition p Halt = (Halt,Halt)
epartition p (Error str) = (Error str, Error str)
epartition p (Continue x) = (Continue ryes, Continue rno) where (ryes,rno) = epartition p x
epartition p (Produce v x) | p v = (v --> ryes, Continue rno) where (ryes,rno) = epartition p x
epartition p (Produce v x) = (Continue ryes, v --> rno) where (ryes,rno) = epartition p x

es_epartition :: (t -> EnumProc Bool) -> EnumProc t -> (EnumProc t, EnumProc t)
es_epartition p Empty = (Empty,Empty)
es_epartition p Halt = (Halt,Halt)
es_epartition p (Error str) = (Error str, Error str)
es_epartition p (Continue x) = (Continue ryes, Continue rno) where (ryes,rno) = es_epartition p x
es_epartition p (Produce v x) = (rryes, rrno) where (ryes,rno) = es_epartition p x; r = p v; rryes = r >>= (\rr -> if rr then (v --> ryes) else (Continue ryes)); rrno = r >>= (\rr -> if rr then (Continue rno) else (v --> rno))

-- To be honest, given that ordering in enumeration procedures may not be fully controllable, zipping seems like not the right solution for whatever you're trying to do in most cases, but we provide it anyway.
ezip :: EnumProc a -> EnumProc b -> EnumProc (a,b)
ezip Empty _ = Empty
ezip Halt _ = Halt
ezip (Error str) _ = Error str
ezip (Continue x) y = Continue (ezip x y)
ezip (Produce v x) y = Continue (ezip2 v y x)

ezip2 :: a -> EnumProc b -> EnumProc a -> EnumProc (a,b)
ezip2 v Empty _ = Empty
ezip2 v Halt _ = Halt
ezip2 v (Error str) _ = Error str
ezip2 v (Continue y) x = Continue (ezip2 v y x)
ezip2 v (Produce w y) x = ((v,w) --> ezip x y)

-- Unzip, on the other hand, seems a lot more useful
-- Worth saying: eunzip really is a very very particular case of <*>
eunzip :: EnumProc (a,b) -> (EnumProc a, EnumProc b)
eunzip Empty = (Empty,Empty)
eunzip Halt = (Halt,Halt)
eunzip (Error str) = (Error str,Error str)
eunzip (Continue x) = (Continue ras, Continue rbs) where (ras,rbs) = eunzip x
eunzip (Produce (va,vb) x) = (va --> ras, vb --> rbs) where (ras,rbs) = eunzip x

enubBy :: (a -> a -> Bool) -> EnumProc a -> EnumProc a
enubBy p Empty = Empty
enubBy p Halt = Halt
enubBy p (Error str) = Error str
enubBy p (Continue x) = Continue (enubBy p x)
enubBy p (Produce v x) = v --> (enubBy p (efilter (not . (p v)) x))

es_enubBy :: (a -> a -> EnumProc Bool) -> EnumProc a -> EnumProc a
es_enubBy p Empty = Empty
es_enubBy p Halt = Halt
es_enubBy p (Error str) = Error str
es_enubBy p (Continue x) = Continue (es_enubBy p x)
es_enubBy p (Produce v x) = v --> (es_enubBy p (es_efilter (\y -> (p v y) >>= (return . not)) x))

-- To produce a truly safe enub we'd have to reimplement equality ensuring it fulfills our assumptions.
enub :: Eq t => EnumProc t -> EnumProc t
enub = enubBy (==)

edeleteBy :: (a -> a -> Bool) -> a -> EnumProc a -> EnumProc a
edeleteBy p x Empty = Empty
edeleteBy p x Halt = Halt
edeleteBy p x (Error str) = Error str
edeleteBy p x (Continue y) = Continue (edeleteBy p x y)
edeleteBy p x (Produce v y) | p x v = y
edeleteBy p x (Produce v y) = v --> (edeleteBy p x y)

es_edeleteBy :: (a -> a -> EnumProc Bool) -> a -> EnumProc a -> EnumProc a
es_edeleteBy p x en = en >>= (\v -> p x v >>= (\r -> if r then Empty else (return v)))

-- Same comment again about safe equality
edelete :: Eq t => t -> EnumProc t -> EnumProc t
edelete = edeleteBy (==)

-- Subtracting infinite enumerations is guaranteed to produce bottom.
-- So don't do it.
(\\\) :: Eq t => EnumProc t -> EnumProc t -> EnumProc t
en1 \\\ en2 = es_foldr edelete en1 en2

eunionBy :: (a -> a -> Bool) -> EnumProc a -> EnumProc a -> EnumProc a
eunionBy p e1 e2 = enubBy p (e1 ..+ e2)

es_eunionBy :: (a -> a -> EnumProc Bool) -> EnumProc a -> EnumProc a -> EnumProc a
es_eunionBy p e1 e2 = es_enubBy p (e1 ..+ e2)

-- Again, true safety only if reimplementing equality
eunion :: Eq a => EnumProc a -> EnumProc a -> EnumProc a
eunion = eunionBy (==)

eunionAll :: Eq a => EnumProc (EnumProc a) -> EnumProc a
eunionAll = enub . diagonalize_enumproc

eintersectBy :: (a -> a -> Bool) -> EnumProc a -> EnumProc a -> EnumProc a
eintersectBy p e1 e2 = es_efilter (\x -> eany (return . (p x)) e1) e2

es_eintersectBy :: (a -> a -> EnumProc Bool) -> EnumProc a -> EnumProc a -> EnumProc a
es_eintersectBy p e1 e2 = es_efilter (\x -> eany (p x) e1) e2

-- True safety only if reimplementing equality.
eintersect :: Eq a => EnumProc a -> EnumProc a -> EnumProc a
eintersect = eintersectBy (==)

eintersectAll :: Eq a => EnumProc (EnumProc a) -> EnumProc a
-- Because there's no (computable) neutral element with intersection, we need to pick apart the empty case, and take the first enumeration as the base case for the foldr.
-- We produce an error when attempting to perform the intersection of no enumerations.
eintersectAll Empty = Error "Attempting to intersect zero enumerations."
eintersectAll Halt = Halt
eintersectAll (Error str) = Error str
eintersectAll (Continue x) = Continue (eintersectAll x)
eintersectAll (Produce en x) = en >>= (\el -> eifelse (eall (\en2 -> eelem el en2) x) (return el) Empty)

-- Make tuples (lists of known length, to be precise, since the length is a parameter and so we cannot use tuple types easily) of elements in an enum.
-- Picking the same element more than once is allowed.
-- E.g. (epick 2 (1 --> 2 --> 3 --> Empty)) == ([1,1] --> [1,2] --> [1,3] --> [2,1] --> [2,2] --> [2,3] --> [3,1] --> [3,2] --> [3,3] --> Empty)
epick :: Int -> EnumProc a -> EnumProc [a]
epick 0 en = ([] --> Empty)
epick n en = en >>= (\f -> (f:) <$> (epick (n-1) en))

single_enum :: t -> EnumProc t
single_enum x = Produce x Empty

mb_single_enum :: Maybe t -> EnumProc t
mb_single_enum Nothing = Empty
mb_single_enum (Just x) = single_enum x

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

-- Version of the above that, if everything goes fine, returns an enum with just one element, the list containing the first n elements of the enumeration.
-- If Empty is found, it returns the list with all elements in the enum
-- Similarly if Halt is found, except the Enum is appended with Halt.
-- If an error occurs, the same and we append with Error
-- Of course, if a non-terminating enumeration with not enough elements is given, the result is a non-terminating enumeration with no results.

list_n_from_enum :: Int -> EnumProc t -> EnumProc [t]
list_n_from_enum n x = fst (list_n_from_enum_full n x)

list_n_from_enum_strict :: Int -> EnumProc t -> EnumProc [t]
list_n_from_enum_strict n x = fst (list_n_from_enum_strict_full n x)

-- And now the versions that return the remaining enumeration too (safely).
list_n_from_enum_full :: Int -> EnumProc t -> (EnumProc [t],EnumProc t)
list_n_from_enum_full 0 x = ([] --> Empty,x)
list_n_from_enum_full n Empty = ([] --> Empty,Empty)
list_n_from_enum_full n Halt = ([] --> Halt,Halt)
list_n_from_enum_full n (Error str) = ([] --> (Error str),Error str)
list_n_from_enum_full n (Continue x) = (Continue r1,Continue r2) where (r1,r2) = list_n_from_enum_full n x
list_n_from_enum_full n (Produce v x) = (fmap (v:) r1,Continue r2) where (r1,r2) = list_n_from_enum_full (n-1) x

-- Version of the above that returns Empty/Halt/Error if no elements were found.
list_n_from_enum_strict_full :: Int -> EnumProc t -> (EnumProc [t],EnumProc t)
list_n_from_enum_strict_full n x = (list_n_from_enum_strict_rec r1,r2) where (r1,r2) = list_n_from_enum_full n x

list_n_from_enum_strict_rec :: EnumProc [t] -> EnumProc [t]
list_n_from_enum_strict_rec Empty = Empty
list_n_from_enum_strict_rec Halt = Halt
list_n_from_enum_strict_rec (Error str) = Error str
list_n_from_enum_strict_rec (Continue x) = Continue (list_n_from_enum_strict_rec x)
list_n_from_enum_strict_rec (Produce [] x) = x
list_n_from_enum_strict_rec (Produce l x) = Produce l x




step :: EnumProc t -> EnumProc t
step (Continue next) = next
step (Produce v next) = next
step Halt = Halt
step Empty = Empty
step (Error x) = Error x

nstep :: Int -> EnumProc t -> EnumProc t
nstep n x = (iterate step x) !! n

get_nstep :: Int -> EnumProc t -> [t]
get_nstep 0 x = []
get_nstep n Empty = []
get_nstep n Halt = []
get_nstep n (Error str) = error str
-- A cool thing about get_nstep is that we can safely compress Continues while applying it, because it will only be a finite number of them.
--get_nstep n (Continue x) = Continue (get_nstep (n-1) x)
get_nstep n (Continue x) = get_nstep (n-1) x
get_nstep n (Produce v x) = v:(get_nstep (n-1) x)

get_nstep_full :: Int -> EnumProc t -> ([t], EnumProc t)
get_nstep_full 0 x = ([],x)
get_nstep_full n Empty = ([],Empty)
get_nstep_full n Halt = ([],Halt)
get_nstep_full n (Error str) = (error str,Error str)
-- A cool thing about get_nstep is that we can safely compress Continues while applying it, because it will only be a finite number of them.
--get_nstep n (Continue x) = Continue (get_nstep (n-1) x)
get_nstep_full n (Continue x) = get_nstep_full (n-1) x
get_nstep_full n (Produce v x) = (v:rf,rr) where (rf,rr) = get_nstep_full (n-1) x

get_nstep_en :: Int -> EnumProc t -> EnumProc t
-- This is not really unsafe, because we know the list will be finite by construction.
get_nstep_en n en = uns_enum_from_list (get_nstep n en)

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

-- I leave this for honor purposes, but I realized that a way more elegant way of implementing diagonalize is... econcat!!! It is just a folding of interleaving. It does not output things in the same order as this implementation of diagonalize (in a sense, foldr (..+) is "recursive" whereas this implementation of diagonalize is "iterative", so foldr (..+) will output exponentially as many elements from earlier enumerations than from latter ones, whereas diagonalize will output a constant number as many), but that is not relevant for the semantics of diagonalize.
-- Update: This implementation is HUGELY more efficient, so I use it instead whenever I can. In fact, econcat will be an alias to this. The recursive implementation is simply too slow.
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

apply_next_constf :: ConstF a (EnumProc b) -> ConstF (EnumProc a) (EnumProc b)
apply_next_constf f = (Right take_next) .? (constfmap f)

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

apply_each_constf :: ConstF a (EnumProc b) -> ConstF (EnumProc a) (EnumProc b)
apply_each_constf f = (Right take_each) .? (constfmap f)


-- Wrapper for function type designed to enable lifting constant functions to functors without needing to have the structure of the functor.
-- Not all instances of ConstF are constant, it just explicitly distinguishes between constant and non-constant behaviour in the type, so that it can be pattern matched against.
type ConstF a b = Either b (a -> b)
type a ->? b = ConstF a b
infixr 7 ->?

constf :: b -> (a ->? b)
constf x = Left x

varf :: (a -> b) -> (a ->? b)
varf f = Right f

(.?) :: ConstF b c -> ConstF a b -> ConstF a c
(Left x) .? _ = Left x
(Right f) .? (Left y) = Left (f y)
(Right f) .? (Right g) = Right (f . g)
infixr 9 .?

($?) :: ConstF a b -> a -> b
(Left x) $? _ = x
(Right f) $? x = f x
infixr 0 $?

-- A type being an instance of ConstFFunctor means that **it can have constant behaviour**, it is not necessarily the case (and it is most interesting when) constfmap \== fmap.
-- In the case of EnumProc, for example, constant behaviour can happen only when we are applying to a single element in the enumeration.
-- So constfmap should be read as: "fmap in a way that preserves constants".
-- It is true that another way to look at this is to have two different types which are related and instantiate Functor, one of which instantiates ConstFFunctor and constfmap == fmap and the other does not. We forget about that for now.
class Functor f => ConstFFunctor f where
	constfmap :: ConstF a b -> ConstF (f a) (f b)

instance (Functor f, Applicative f) => ConstFFunctor f where
	constfmap (Left x) = Left (pure x)
	constfmap (Right f) = Right (fmap f)

data STEnumProcCommute = EmptyCom | HaltCom | ErrorCom | ContinueCom | ProduceCom

st_en_commute :: (forall s. ST s (EnumProc t)) -> (forall s2. EnumProc (ST s2 t))
st_en_commute sten = case comtype of
	{
		EmptyCom -> Empty;
		HaltCom -> Halt;
		ErrorCom -> Error (runST (do {(Error str) <- sten; return str}));
		ContinueCom -> Continue (st_en_commute (do {(Continue x) <- sten; return x}));
		ProduceCom -> Produce (do {(Produce v x) <- sten; return v}) (st_en_commute (do {(Produce v x) <- sten; return x}))
	}
	where
		comtype = runST (do
		{
			en <- sten;
			case en of
			{
				Empty -> return EmptyCom;
				Halt -> return HaltCom;
				Error str -> return ErrorCom;
				Continue x -> return ContinueCom;
				Produce v x -> return ProduceCom
			}
		})







type EnumProcPerformanceOutput a = Integer -> Integer -> Integer -> a -> IO ()

-- Measuring times for infinite enumerations.
-- The first function is what to do on Produce.
	-- First Integer argument is this step's time
	-- Second Integer argument is time since last produce
	-- Third Integer argument is total time
-- The second function is what to do on Continue. Same arguments (but without the element, of course)
-- The third function is what to do on Empty.
-- The fourth function is what to do on Halt.
-- Errors get output as errors regardless.
t_measure_enum_by :: Show a => EnumProcPerformanceOutput a -> EnumProcPerformanceOutput () -> EnumProcPerformanceOutput () -> EnumProcPerformanceOutput () -> EnumProc a -> IO ()
t_measure_enum_by fprod fcont fempty fhalt en = do
	{
		cur <- getCPUTime;

		t_measure_enum_by_rec fprod fcont fempty fhalt cur cur cur en
	}

t_measure_enum_by_rec :: Show a => EnumProcPerformanceOutput a -> EnumProcPerformanceOutput () -> EnumProcPerformanceOutput () -> EnumProcPerformanceOutput () -> Integer -> Integer -> Integer -> EnumProc a -> IO ()
t_measure_enum_by_rec fprod fcont fempty fhalt lstep lprod base EnumProc.Empty = do
	{
		cur <- getCPUTime;
		let {tstep = cur - lstep; tprod = cur - lprod; ttot = cur - base};
		fempty tstep tprod ttot ()
	}
t_measure_enum_by_rec fprod fcont fempty fhalt lstep lprod base EnumProc.Halt = do
	{
		cur <- getCPUTime;
		let {tstep = cur - lstep; tprod = cur - lprod; ttot = cur - base};
		fhalt tstep tprod ttot ()
	}
t_measure_enum_by_rec fprod fcont fempty fhalt lstep lprod base (Error estr) = error estr
t_measure_enum_by_rec fprod fcont fempty fhalt lstep lprod base (Produce v x) = do
	{
		silence (putStr (show v));

		cur <- getCPUTime;
		let {tstep = cur - lstep; tprod = cur - lprod; ttot = cur - base};
		fprod tstep tprod ttot v;
		
		let {nstep = cur; nprod = cur};

		t_measure_enum_by_rec fprod fcont fempty fhalt nstep nprod base x;	
	}
t_measure_enum_by_rec fprod fcont fempty fhalt lstep lprod base (Continue x) = do
	{
		cur <- getCPUTime;
		let {tstep = cur - lstep; tprod = cur - lprod; ttot = cur - base};
		fcont tstep tprod ttot ();
		
		let {nstep = cur; nprod = lprod};

		t_measure_enum_by_rec fprod fcont fempty fhalt nstep nprod base x;	
	}

t_measure_enum_default_fprod :: Show a => EnumProcPerformanceOutput a
t_measure_enum_default_fprod tstep tprod ttot a = do
	{
		putStrLn "Found an element";
		putStrLn "";
		putStrLn (show a);
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show tstep));
		putStrLn ("Time since last element: " ++ (show tprod));
		putStrLn ("Time since start: " ++ (show ttot));
		putStrLn ""
	}

t_measure_enum_default_fcont :: EnumProcPerformanceOutput ()
t_measure_enum_default_fcont tstep tprod ttot _ = do
	{
		putStrLn "Improductive step";
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show tstep));
		putStrLn ("Time since last element: " ++ (show tprod));
		putStrLn ("Time since start: " ++ (show ttot));
		putStrLn ""
	}

t_measure_enum_default_fempty :: EnumProcPerformanceOutput ()
t_measure_enum_default_fempty tstep tprod ttot _ = do
	{
		putStrLn "Enumeration finished";
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show tstep));
		putStrLn ("Time since last element: " ++ (show tprod));
		putStrLn ("Time since start: " ++ (show ttot));
		putStrLn ""
	}

t_measure_enum_default_fhalt :: EnumProcPerformanceOutput ()
t_measure_enum_default_fhalt tstep tprod ttot _ = do
	{
		putStrLn "Enumeration halted";
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show tstep));
		putStrLn ("Time since last element: " ++ (show tprod));
		putStrLn ("Time since start: " ++ (show ttot));
		putStrLn ""
	}

t_measure_enum :: Show a => EnumProc a -> IO ()
t_measure_enum = t_measure_enum_by t_measure_enum_default_fprod t_measure_enum_default_fcont t_measure_enum_default_fempty t_measure_enum_default_fhalt

t_measure_enum_default_fprod_secs :: Show a => EnumProcPerformanceOutput a
t_measure_enum_default_fprod_secs tstep tprod ttot a = do
	{
		putStrLn "Found an element";
		putStrLn "";
		putStrLn (show a);
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show (t_seconds tstep)) ++ "s");
		putStrLn ("Time since last element: " ++ (show (t_seconds tprod)) ++ "s");
		putStrLn ("Time since start: " ++ (show (t_seconds ttot)) ++ "s");
		putStrLn ""
	}

t_measure_enum_default_fcont_secs :: EnumProcPerformanceOutput ()
t_measure_enum_default_fcont_secs tstep tprod ttot _ = do
	{
		putStrLn "Improductive step";
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show (t_seconds tstep)) ++ "s");
		putStrLn ("Time since last element: " ++ (show (t_seconds tprod)) ++ "s");
		putStrLn ("Time since start: " ++ (show (t_seconds ttot)) ++ "s");
		putStrLn ""
	}

t_measure_enum_default_fempty_secs :: EnumProcPerformanceOutput ()
t_measure_enum_default_fempty_secs tstep tprod ttot _ = do
	{
		putStrLn "Enumeration finished";
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show (t_seconds tstep)) ++ "s");
		putStrLn ("Time since last element: " ++ (show (t_seconds tprod)) ++ "s");
		putStrLn ("Time since start: " ++ (show (t_seconds ttot)) ++ "s");
		putStrLn ""
	}

t_measure_enum_default_fhalt_secs :: EnumProcPerformanceOutput ()
t_measure_enum_default_fhalt_secs tstep tprod ttot _ = do
	{
		putStrLn "Enumeration halted";
		putStrLn "";
		putStrLn ("Time since last step: " ++ (show (t_seconds tstep)) ++ "s");
		putStrLn ("Time since last element: " ++ (show (t_seconds tprod)) ++ "s");
		putStrLn ("Time since start: " ++ (show (t_seconds ttot)) ++ "s");
		putStrLn ""
	}

t_measure_enum_secs :: Show a => EnumProc a -> IO ()
t_measure_enum_secs = t_measure_enum_by t_measure_enum_default_fprod_secs t_measure_enum_default_fcont_secs t_measure_enum_default_fempty_secs t_measure_enum_default_fhalt_secs

t_measure_enum_csv_fprod :: Show a => String -> EnumProcPerformanceOutput a
t_measure_enum_csv_fprod sep tstep tprod ttot a = do
	{
		let {
			stype = "PROD";
			sstep = show (t_seconds tstep);
			sprod = show (t_seconds tprod);
			stot = show (t_seconds ttot);
			sa = show a;
		};

		putStrLn (stype ++ sep ++ sstep ++ sep ++ sprod ++ sep ++ stot ++ sep ++ sa);
		hFlush stdout
	}

t_measure_enum_csv_fcont :: String -> EnumProcPerformanceOutput ()
t_measure_enum_csv_fcont sep tstep tprod ttot _ = do
	{
		let {
			stype = "CONT";
			sstep = show (t_seconds tstep);
			sprod = show (t_seconds tprod);
			stot = show (t_seconds ttot);
			sa = "";
		};

		putStrLn (stype ++ sep ++ sstep ++ sep ++ sprod ++ sep ++ stot ++ sep ++ sa);
		hFlush stdout
	}

t_measure_enum_csv_fempty :: String -> EnumProcPerformanceOutput ()
t_measure_enum_csv_fempty sep tstep tprod ttot _ = do
	{
		let {
			stype = "EMPTY";
			sstep = show (t_seconds tstep);
			sprod = show (t_seconds tprod);
			stot = show (t_seconds ttot);
			sa = "";
		};

		putStrLn (stype ++ sep ++ sstep ++ sep ++ sprod ++ sep ++ stot ++ sep ++ sa);
		hFlush stdout
	}

t_measure_enum_csv_fhalt :: String -> EnumProcPerformanceOutput ()
t_measure_enum_csv_fhalt sep tstep tprod ttot _ = do
	{
		let {
			stype = "HALT";
			sstep = show (t_seconds tstep);
			sprod = show (t_seconds tprod);
			stot = show (t_seconds ttot);
			sa = "";
		};

		putStrLn (stype ++ sep ++ sstep ++ sep ++ sprod ++ sep ++ stot ++ sep ++ sa);
		hFlush stdout
	}

t_measure_enum_csv :: Show a => String -> EnumProc a -> IO ()
t_measure_enum_csv sep = t_measure_enum_by (t_measure_enum_csv_fprod sep) (t_measure_enum_csv_fcont sep) (t_measure_enum_csv_fempty sep) (t_measure_enum_csv_fhalt sep)


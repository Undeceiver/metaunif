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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
module HaskellPlus where

import Data.Bifunctor
import Data.Maybe
import Data.Functor.Fixedpoint
import Data.Functor.Identity
import Control.Unification
import Control.Monad.Except
import Data.Map.Strict
import Data.Graph
import Control.Lens
import Control.Applicative
import Control.Monad.State
import Control.Monad.ST
import Data.Functor.Compose

-- Here I put functions/types that I feel should be part of Haskell but aren't. It is likely that at least half of them ACTUALLY are part of Haskell, but I wasn't smart enough to find them.

collapse_mb :: Maybe (Maybe t) -> Maybe t
collapse_mb Nothing = Nothing
collapse_mb (Just Nothing) = Nothing
collapse_mb (Just (Just x)) = (Just x)

type Preshow = () -> String

preshow :: Show t => t -> Preshow
preshow x = unshow (show x)

unshow :: String -> Preshow
unshow str = (\_ -> str)

instance Show Preshow where
	show f = f ()

-- Amazingly, some list utilities.
-- I've seen this implemented in similar libraries to this one.
(!!?) :: [a] -> Int -> Maybe a
[] !!? _ = Nothing
(x:xs) !!? 0 = Just x
(x:xs) !!? n = xs !!? (n-1)

-- Why is this not a thing?
insertAt :: Int -> a -> [a] -> [a]
insertAt 0 x xs = x:xs
insertAt n x [] = error "No such position in the list"
insertAt n x (y:ys) = y:(insertAt (n-1) x ys)

replaceAt :: Int -> a -> [a] -> [a]
replaceAt 0 x (y:ys) = x:ys
replaceAt n x [] = error "No such position in the list"
replaceAt n x (y:ys) = y:(replaceAt (n-1) x ys)

applyBy :: Functor f => (a -> Bool) -> (a -> a) -> f a -> f a
applyBy p f = fmap (\a -> if (p a) then (f a) else a)

applyAll :: (Eq a, Functor f) => a -> (a -> a) -> f a -> f a
applyAll a = applyBy (== a)

replaceAll :: (Eq a, Functor f) => a -> a -> f a -> f a
replaceAll a1 a2 = applyAll a1 (\_ -> a2)

replaceIf :: Eq a => a -> a -> a -> a
replaceIf a1 a2 = runIdentity . (replaceAll a1 a2) . Identity

deleteAllBy :: (a -> Bool) -> [a] -> [a]
deleteAllBy p [] = []
deleteAllBy p (x:xs) | p x = deleteAllBy p xs
deleteAllBy p (x:xs) = x:(deleteAllBy p xs)

deleteAll :: Eq a => a -> [a] -> [a]
deleteAll a = deleteAllBy (== a)

append_to_mblist :: Maybe [a] -> [a] -> [a]
append_to_mblist Nothing x = x
append_to_mblist (Just x) y = x ++ y

-- foldMap with semigroups, with an initial element
foldMapSG :: (Foldable f, Functor f, Semigroup m) => (a -> m) -> m -> f a -> m
foldMapSG f i ts = Prelude.foldr (<>) i (f <$> ts)

newtype FlippedFunctor (t :: k) (f :: k -> *) = FlippedFunctor (f t)
fromFlippedFunctor :: FlippedFunctor t f -> f t
fromFlippedFunctor (FlippedFunctor x) = x

newtype FlippedBifunctor (b :: k1 -> k2 -> *) (t :: k2) (f :: k1) = FlippedBifunctor (b f t)
fromFlippedBifunctor :: FlippedBifunctor b t f -> b f t
fromFlippedBifunctor (FlippedBifunctor x) = x

instance Bifunctor b => Bifunctor (FlippedBifunctor b) where
	bimap f g (FlippedBifunctor x) = FlippedBifunctor (bimap g f x)

instance Bifunctor b => Functor (FlippedBifunctor b a) where
	fmap = bimap id

--instance Bifunctor f => Functor (f t) where
--	fmap = bimap id

show_as_args :: [String] -> String
show_as_args [] = ""
show_as_args [x] = x
show_as_args (x:xs) = x ++ ", " ++ (show_as_args xs)

class Fixpoint (fx :: (* -> *) -> *) where
	fixp :: Functor t => t (fx t) -> fx t
	-- We cannot in general extract the element because some fixedpoint instances may not have such elements, but we can always "map" into those elements of the fixpoint that are, in fact, fixedpoints; plus indicate what to do with the added base cases the fixpoint may have.
	unfixp :: Functor t => (t (fx t) -> fx a) -> fx t -> fx a

instance Fixpoint Fix where
	fixp = Fix
	unfixp f (Fix x) = f x

instance Fixpoint (FlippedBifunctor UTerm v) where
	fixp = FlippedBifunctor . UTerm . (fmap fromFlippedBifunctor)
	unfixp f (FlippedBifunctor (UVar v)) = FlippedBifunctor (UVar v)
	unfixp f (FlippedBifunctor (UTerm t)) = (f (fmap FlippedBifunctor t))

-- Take some initial information (e.g. a head) and an already built functor (such as a list) that is used on the constructor of another functor, and map it to its fixed point.
build_functor_fix :: (Fixpoint fx, Functor t) => (forall f. h -> l f -> t f) -> h -> l (fx t) -> fx t
build_functor_fix b h s = fixp (b h s)

-- Just to avoid flipping and unflipping excessively when using the above function with UTerms.
build_functor_fix_uterm :: (Functor t, Functor l) => (forall f. h -> l f -> t f) -> h -> l (UTerm t v) -> UTerm t v
build_functor_fix_uterm b h s = fromFlippedBifunctor (build_functor_fix b h (fmap FlippedBifunctor s))

instance (Eq v, Eq (t (UTerm t v))) => Eq (UTerm t v) where
	(UVar x) == (UVar y) = x == y
	(UTerm x) == (UTerm y) = x == y
	_ == _ = False



-- Monad utilities
pass :: Monad m => m ()
pass = return ()

floatExceptT :: (Show e, Monad m) => (ExceptT e m) a -> m a
floatExceptT exc = (runExceptT exc) >>= (\x -> case x of {Left e -> error (show e); Right y -> return y})

mb_from_exceptT :: Monad m => (ExceptT e m) a -> m (Maybe a)
mb_from_exceptT exc = (runExceptT exc) >>= (\x -> case x of {Left e -> return Nothing; Right y -> return (Just y)})

clear_value :: Monad m => m a -> m ()
clear_value = (>> (return ()))

(>$>=) :: (Functor f, Monad m) => f (m a) -> (a -> m b) -> f (m b)
x >$>= f = (>>= f) <$> x
infixl 7 >$>=

(>*>=) :: (Applicative m1, Monad m2) => m1 (m2 a) -> m1 (a -> m2 b) -> m1 (m2 b)
x >*>= fs = ((\f -> (>>= f)) <$> fs) <*> x
infixl 7 >*>=

-- Warning: This is not general, when the inner function should modify the external monad itself, this won't work. It's only for running monadic computations inside a monad.
(>>>=) :: (Monad m1, Monad m2) => m1 (m2 a) -> (a -> m2 b) -> m1 (m2 b)
x >>>= f = x >>= (\st -> return (st >>= f))

type JState s = State s ()
jstate :: (s -> s) -> JState s
jstate f = state (\s -> ((),f s))

runJState :: JState s -> s -> s
runJState st s = snd (runState st s)


-- Type lists
type a :* b = (a,b)
infixr 7 :*

totlist :: a -> a :* ()
totlist x = x *: ()

(*:) :: a -> b -> (a :* b)
a *: b = (a,b)
infixr 7 *:

(*::) :: a -> b -> (a :* b :* ())
a *:: b = a *: b *: ()
infixr 7 *::

-- Provide functions to use them nicely. Unfortunately we cannot do one function to obtain any given of them, but we can do the first ten.
thead :: a :* b -> a
thead (a,b) = a

ttail :: a :* b -> b
ttail (a,b) = b

tget0 :: a :* _ -> a
tget0 = thead

tget1 :: _ :* a :* _ -> a
tget1 = thead . ttail

tget2 :: _ :* _ :* a :* _ -> a
tget2 = thead . ttail . ttail

tget3 :: _ :* _ :* _ :* a :* _ -> a
tget3 = thead . ttail . ttail . ttail

tget4 :: _ :* _ :* _ :* _ :* a :* _ -> a
tget4 = thead . ttail . ttail . ttail . ttail

tget5 :: _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget5 = thead . ttail . ttail . ttail . ttail . ttail

tget6 :: _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget6 = thead . ttail . ttail . ttail . ttail . ttail . ttail

tget7 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget7 = thead . ttail . ttail . ttail . ttail . ttail . ttail . ttail

tget8 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget8 = thead . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

tget9 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget9 = thead . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail0 :: _ :* r -> r
ttail0 = ttail

ttail1 :: _ :* _ :* r -> r
ttail1 = ttail . ttail

ttail2 :: _ :* _ :* _ :* r -> r
ttail2 = ttail . ttail . ttail

ttail3 :: _ :* _ :* _ :* _ :* r -> r
ttail3 = ttail . ttail . ttail . ttail

ttail4 :: _ :* _ :* _ :* _ :* _ :* r -> r
ttail4 = ttail . ttail . ttail . ttail . ttail

ttail5 :: _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail5 = ttail . ttail . ttail . ttail . ttail . ttail

ttail6 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail6 = ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail7 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail7 = ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail8 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail8 = ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail9 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail9 = ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail


-- Utility to normalize to a certain list length for compatibility with other functions
tinsert0 :: v0 -> r -> v0 :* r
tinsert0 v0 r = v0 *: r

tfill0 :: r -> () :* r
tfill0 = tinsert0 ()

tinsert1 :: v1 -> v0 :* r -> v0 :* v1 :* r
tinsert1 v1 r = (thead r) *: (tinsert0 v1 (ttail r))

tfill1 :: v0 :* r -> v0 :* () :* r
tfill1 = tinsert1 ()

tinsert2 :: v2 -> v0 :* v1 :* r -> v0 :* v1 :* v2 :* r
tinsert2 v2 r = (thead r) *: (tinsert1 v2 (ttail r))

tfill2 :: v0 :* v1 :* r -> v0 :* v1 :* () :* r
tfill2 = tinsert2 ()

tinsert3 :: v3 -> v0 :* v1 :* v2 :* r -> v0 :* v1 :* v2 :* v3 :* r
tinsert3 v3 r = (thead r) *: (tinsert2 v3 (ttail r))

tfill3 :: v0 :* v1 :* v2 :* r -> v0 :* v1 :* v2 :* () :* r
tfill3 = tinsert3 ()

tinsert4 :: v4 -> v0 :* v1 :* v2 :* v3 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* r
tinsert4 v4 r = (thead r) *: (tinsert3 v4 (ttail r))

tfill4 :: v0 :* v1 :* v2 :* v3 :* r -> v0 :* v1 :* v2 :* v3 :* () :* r
tfill4 = tinsert4 ()

tinsert5 :: v5 -> v0 :* v1 :* v2 :* v3 :* v4 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* r
tinsert5 v5 r = (thead r) *: (tinsert4 v5 (ttail r))

tfill5 :: v0 :* v1 :* v2 :* v3 :* v4 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* () :* r
tfill5 = tinsert5 ()

tinsert6 :: v6 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* r
tinsert6 v6 r = (thead r) *: (tinsert5 v6 (ttail r))

tfill6 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* () :* r
tfill6 = tinsert6 ()

tinsert7 :: v7 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* r
tinsert7 v7 r = (thead r) *: (tinsert6 v7 (ttail r))

tfill7 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* () :* r
tfill7 = tinsert7 ()

tinsert8 :: v8 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* r
tinsert8 v8 r = (thead r) *: (tinsert7 v8 (ttail r))

tfill8 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* () :* r
tfill8 = tinsert8 ()

tinsert9 :: v9 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* v9 :* r
tinsert9 v9 r = (thead r) *: (tinsert8 v9 (ttail r))

tfill9 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* () :* r
tfill9 = tinsert9 ()




-- Types that are essentially functions with added functionality.
class Functional t a b where
	tofun :: t -> a -> b

instance Functional (a -> b) a b where
	tofun = id

-- The idea when you use a Normalizable type is that you define all your functions on the a type, and simply use the type n to indicate when an element needs to be normalized, and only define functions on n that are necessarily to be performed on normalized types. The rest can be performed on normalized types by simply injecting them into a. If at some point it is important to keep normality while performing an operation, we can implement a different version for n.
class Normalizable a n | a -> n, n -> a where
	normalize :: a -> n
	inject_normal :: n -> a
	-- If every element of the type n is normal, it should obey: normalize . inject_normal = id.
	-- However, we can relax this constraint to say that n contains normal elements but not all are normal, and then it must be normalize . inject_normal . normalize = normalize
	-- normalize itself should not produce non-termination.

(~~) :: (Normalizable a n, Eq n) => a -> a -> Bool
x1 ~~ x2 = (normalize x1) == (normalize x2)

newtype NormalizedFunctor (f :: * -> *) (t :: *) = NormalizedFunctor {fromNormalizedFunctor :: f t}
instance (Functor f, Normalizable a b) => Normalizable (NormalizedFunctor f a) (NormalizedFunctor f b) where
	inject_normal = NormalizedFunctor . (fmap inject_normal) . fromNormalizedFunctor
	normalize = NormalizedFunctor. (fmap normalize) . fromNormalizedFunctor

-- Mapping a set of results to a set of arguments in something that is similar to a functional.
type (v := r) = Map v r


-- Variations of Functor for different arguments and types.
-- We use the following nomenclature: A "Non" syllable means an argument that does not behave functorially. A "Func" syllable means an argument that behaves functorially, in order.
-- So, for example, Functor ~ FuncFunctor, Bifunctor ~ FuncFuncFunctor, a type which has two arguments but is only functorial on the first one would be FuncNonFunctor, etc.
-- We define them as necessary
-- (VOID)




-- Careful with this class, it is extremely prone to overlapping instances. Define the ones you specifically want each time, maybe using reusable functions but not instances.
class Mappable a b ta tb where
	anymap :: (a -> b) -> ta -> tb
	-- Known instances:
	-- Functor f => anymap = fmap	

(<$$>) :: Mappable a b ta tb => (a -> b) -> ta -> tb
(<$$>) = anymap





-- Some graph utilities

-- Check if a graph is directedly acyclic
acyclic :: Graph -> Bool
acyclic g = length (scc g) == length (vertices g)


monadop :: Monad m => (a -> b -> c) -> m a -> m b -> m c
monadop f m1 m2 = do {r1 <- m1; r2 <- m2; return (f r1 r2)}


-- Interprets the bool result inside a monad as a fail state (when False), so that if False is returned, then the monadic composition does not happen and instead we simply return False
mcompose_with_bool :: Monad m => m Bool -> m Bool -> m Bool
mcompose_with_bool r1 r2 = r1 >>= (\v -> if v then r2 else (return False))

(>>=&) :: Monad m => m Bool -> m Bool -> m Bool
(>>=&) = mcompose_with_bool
infixl 1 >>=&

-- An lazy or version (only runs the monadic elements until it finds a True).
(>>=|) :: Monad m => m Bool -> m Bool -> m Bool
m1 >>=| m2 = m1 >>= (\v -> if v then (return True) else m2)
infixl 1 >>=|

-- An or version, and also one which always runs monadic elements (strict). It composes monadically, and returns the or of both bools.
(|>>=) :: Monad m => m Bool -> m Bool -> m Bool
m1 |>>= m2 = do {r1 <- m1; r2 <- m2; return (r1 || r2)}
infixl 1 |>>=



-- Concatenate within a monad.
(>>=++) :: Monad m => m [a] -> m [a] -> m [a]
(>>=++) = monadop (++)
infixl 1 >>=++

monadconcat :: (Monad m, Foldable t) => m (t (m [a])) -> m [a]
monadconcat m = join (Prelude.foldr (>>=++) (return []) <$> m)

monadfilter :: Monad m => (a -> m Bool) -> [a] -> m [a]
monadfilter f [] = return []
monadfilter f (x:xs) = (f x) >>= (\r -> if r then ((x:) <$> rest) else rest) where rest = monadfilter f xs





-- Lens extensions
overTraversal :: LensLike (WrappedMonad Identity) s t a b -> (a -> b) -> s -> t
overTraversal = (\t -> \f -> \s -> runIdentity (mapMOf t (Identity . f) s))

(..~) :: LensLike (WrappedMonad Identity) s t a b -> (a -> b) -> s -> t
(..~) = overTraversal
infixr 4 ..~

foldMapBool :: Monad m => Traversal' s a -> (a -> m Bool) -> s -> m Bool
foldMapBool tr f s = foldMapByOf tr (\s1 -> \s2 -> do {r1 <- s1; r2 <- s2; return (r1 && r2)}) (return True) f s

-- In theory we can use the provided map optics instead of this, but they seem harder to use, at least to me. I prefer to just compose stuff.
-- This may, however, be inefficient in large maps. I'd have to think about it slowly.
lens_assocs :: Ord k => Lens' (Map k v) [(k,v)]
lens_assocs = lens assocs (\prev -> \new -> fromList new)

traversal_assocs :: Ord k => Traversal' (Map k v) (k,v)
traversal_assocs = lens_assocs . traverse

lens_idx :: Int -> Lens' [a] a
lens_idx _ f [] = error "No such index in the list"
lens_idx 0 f (x:xs) = fmap (\rx -> rx:xs) (f x)
lens_idx n f (x:xs) = fmap (\rxs -> x:rxs) (lens_idx (n-1) f xs)

-- Monadic traversals: Traversals that only work with monads, but they allow other things that rely on the fact they only need to work with monads, like sum.
type MTraversal s t a b = forall m. Monad m => (a -> m b) -> s -> m t
type MTraversal' s a = MTraversal s s a a

newtype ReifiedMTraversal s t a b = MTraversal {runMTraversal :: MTraversal s t a b}
type ReifiedMTraversal' s a = ReifiedMTraversal s s a a

-- Adding mtraversals
add_mtraversals :: Semigroup t => MTraversal r t a b -> MTraversal s r a b -> MTraversal s t a b
add_mtraversals t1 t2 f s = (t2 f s) >>= (t1 f)

instance Semigroup s => Semigroup (ReifiedMTraversal' s a) where
	a1 <> a2 = MTraversal (add_mtraversals (runMTraversal a1) (runMTraversal a2))

instance Semigroup s => Monoid (ReifiedMTraversal' s a) where
	mempty = MTraversal (\_ -> return . id)

newtype MZooming m c a = MZooming { munZooming :: m (c, a) }

instance Monad m => Functor (MZooming m c) where
  fmap f (MZooming m) = MZooming (liftM (fmap f) m)

instance (Monoid c, Monad m) => Applicative (MZooming m c) where
  pure a = MZooming (return (mempty, a))
  MZooming f <*> MZooming x = MZooming $ do
    (a, f') <- f
    (b, x') <- x
    return (a <> b, f' x')

instance (Monoid c, Monad m) => Monad (MZooming m c) where
	return = pure
	(MZooming x) >>= f = MZooming $ do
		(c, a) <- x
		(d, a') <- munZooming (f a)
		return (c <> d, a')
	
mzoom :: Monad m => LensLike' (MZooming m c) s a -> StateT a m c -> StateT s m c
mzoom l m = StateT $ munZooming . l (MZooming . (runStateT m))



-- An order based on creation order.
-- A pretty naive implementation, that relies on being provided the previous element. In some sense it is a stateful monad, but we do not go as far as treating it that way.
data CreationOrder t = CO t Int
fromCO :: CreationOrder t -> t
fromCO (CO x _) = x

firstCO :: t -> CreationOrder t
firstCO x = CO x 0

nextCO :: CreationOrder t -> t -> CreationOrder t
nextCO (CO _ i) x = CO x (i+1)

instance Eq t => Eq (CreationOrder t) where
	(CO _ x) == (CO _ y) = (x == y)

-- The purpose of this type.
instance Eq t => Ord (CreationOrder t) where
	(CO _ i) <= (CO _ j) = (i <= j)




-- My version of ListT, pivoting around traverse
data TravListT m a = TravListT {runTravListT :: m [a]}

instance Functor m => Functor (TravListT m) where
	fmap f (TravListT m) = TravListT (fmap (fmap f) m)

instance Applicative m => Applicative (TravListT m) where
	pure x = TravListT (pure (pure x))
	(TravListT fs) <*> (TravListT xs) = TravListT (getCompose ((Compose fs) <*> Compose xs))

instance Monad m => Monad (TravListT m) where
	return = pure
	(TravListT ma) >>= f = TravListT (ma >>= (\l -> (concat <$> (traverse (runTravListT . f) l))))

instance MonadTrans TravListT where
	lift m = TravListT (return <$> m)


-- Proof of lawfulness of the transformation.
--lift (m >>= f) = TravListT (return <$> (m >>= f)) = TravListT (fmap (\a -> [a]) (m >>= f)) = TravListT (onsingleton (m >>= f))

--lift m >>= (lift . f) = (TravListT (return <$> m)) >>= (\m2 -> TravListT (return <$> (f m2))) = TravListT ((return <$> m) >>= (\l -> (concat <$> (traverse (runTravListT . (\m2 -> TravListT (return <$> (f m2)))) l)))) = TravListT ((return <$> m) >>= (\l -> (concat <$> (traverse (\m2 -> return <$> (f m2)) l)))) = TravListT ((onsingleton m) >>= (\l -> (concat <$> (traverse (\m2 -> onsingleton (f m2)) l)))) = TravListT ((onsingleton m) >>= (\[a] -> (concat <$> (traverse (\m2 -> onsingleton (f m2)) [a])))) = TravListT ((onsingleton m) >>= (\[a] -> (concat <$> (onsingleton (onsingleton (f a)))))) = TravListT ((onsingleton m) >>= (\[a] -> onsingleton (f a))) = TravListT (onsingleton (m >>= f))




-- May be a bit too precise, but here are some utilities to extract values from a StateT _ (ST s)
-- The dependency of the state type with s (on the value case) is not super generic, but it is enough for our purposes. If need be, you can always wrap it with newtypes.
getStateTSTState :: (forall s. StateT a (ST s) b) -> a -> a
getStateTSTState stst x = snd (runST (runStateT stst x))

getStateTSTValue :: (forall s. StateT (a s) (ST s) b) -> (forall s. a s) -> b
getStateTSTValue stst x = runST (fst <$> (runStateT stst x))





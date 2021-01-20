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
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
module SOResolution where

import Control.Exception
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Unification
import Control.Unification.IntVar
import Control.Unification.Types
import Control.Monad.Trans
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Error.Class
import HaskellPlus
import Syntax
import Data.Functor.Fixedpoint
import Data.List
import Data.Map.Strict
import AnswerSet
import EnumProc
import Data.Maybe
import Data.Graph
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import Control.Monad.Morph
import Algorithm
import Provenance
import CESQResolutionProvenance
import DependencyGraph
import Identifier
import Control.Monad.ST
import Operable
import Data.Tuple
import Debug.Trace
import Safe (maximumMay, minimumMay)
import GlobalTrace
import ESUnification

data AUnifSysSolution pd fn pmv fmv = AUnifSysSolution {f_syssol :: UnifSysSolution fn fmv, p_syssol :: pmv := GroundSOA pd fn}

lens_f_syssol :: Lens' (AUnifSysSolution pd fn pmv fmv) (UnifSysSolution fn fmv)
lens_f_syssol = lens f_syssol (\prev -> \new -> AUnifSysSolution new (p_syssol prev))

lens_p_syssol :: Lens' (AUnifSysSolution pd fn pmv fmv) (pmv := GroundSOA pd fn)
lens_p_syssol = lens p_syssol (\prev -> \new -> AUnifSysSolution (f_syssol prev) new)

-- In a partial function variable instantiation, occurs check issues may occur. We avoid these (which are dealt with in graphs, and thus we do not need them).
-- We can, however, and require, a partial predicate variable instantiation. Thus, we explicitly avoid this partial predicate variable instantiation having any sort of function instantiation in it, precisely because of the occurs check issue mentioned above.
-- For the same reason, we also assume that there are no predicate variable instantiations to other predicate variables. This stuff is dealt with BELOW.
type ParcAUnifSysSolution pd fn pmv fmv = pmv := SOAtom pd fn pmv fmv

composeParcAUnifSysSolution :: Eq fmv => ParcAUnifSysSolution pd fn pmv fmv -> UnifSysSolution fn fmv -> AUnifSysSolution pd fn pmv fmv
composeParcAUnifSysSolution puss uss = AUnifSysSolution uss ((to_groundsoa . subst_all uss) <$> puss)

data ParcInstAUnifSystem t mpd pd fn v pmv fmv uv = PIAUS {piaus_parcsol :: ParcAUnifSysSolution pd fn pmv fmv, piaus_usys :: FullUnifSystem t mpd pd fn v pmv fmv uv}

lens_piaus_parcsol :: Lens' (ParcInstAUnifSystem t mpd pd fn v pmv fmv uv) (ParcAUnifSysSolution pd fn pmv fmv)
lens_piaus_parcsol = lens piaus_parcsol (\prev -> \new -> PIAUS new (piaus_usys prev))

lens_piaus_usys :: Lens' (ParcInstAUnifSystem t mpd pd fn v pmv fmv uv) (FullUnifSystem t mpd pd fn v pmv fmv uv)
lens_piaus_usys = lens piaus_usys (\prev -> \new -> PIAUS (piaus_parcsol prev) new)

instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Implicit (ParcInstAUnifSystem t mpd pd fn v pmv fmv uv) (AUnifSysSolution pd fn pmv fmv) where
	-- checkImplicit :: ParcInstAUnifSystem t mpd pd fn v pmv fmv uv -> AUnifSysSolution pd fn pmv fmv -> Computation Bool
	-- I have not spent the time checking that this function is necessarily correct, but for sure it is most of the time. If it is not, it is probably due to alpha-equivalence.
	-- We are checking, first, that the function unification system associated to the partially instantiated overall unification system has the function part of the solution as a solution.
	-- Then, we also check that the partial instantiation applied to the function part of the unification solution returns a predicate instantiation that equals the predicate instantiation of the given solution.
	-- We actually check these in the opposite order.
	checkImplicit piaus ausys = if prev then (checkImplicit (piaus_usys piaus) (f_syssol ausys)) else (return False) where prev = ((p_syssol (composeParcAUnifSysSolution (piaus_parcsol piaus) (f_syssol ausys))) == (p_syssol ausys))
	-- This one, on the other hand, should be 100% correct.
	-- enumImplicit :: ParcInstAUnifSystem t mpd pd fn v pmv fmv uv -> Computation (AUnifSysSolution pd fn pmv fmv)
	enumImplicit piaus = composeParcAUnifSysSolution (piaus_parcsol piaus) <$> (enumAS (ImplicitAS (piaus_usys piaus)))



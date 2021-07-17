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
module GlobalTrace where

import HaskellPlus
import Debug.Trace

-- This module involves "global variables", so it kind of goes against Haskell principles. But they are global variables set at compile time, simply as a way to disable debug traces on code without having to permanently remove them.
-- Change this variable to change the behaviour.
gtrace_switch :: Bool
--gtrace_switch = True
gtrace_switch = False

gtrace :: Bool -> String -> a -> a
gtrace True str x = if gtrace_switch then (trace str x) else x
gtrace False _ x = x

gtraceM :: Applicative f => Bool -> String -> f ()
gtraceM True str = if gtrace_switch then (traceM str) else (pure ())
gtraceM False _ = pure ()

gmytrace :: Bool -> String -> a -> a
gmytrace True str x = trace str x
gmytrace False _ x = x

gmytraceM :: Applicative f => Bool -> String -> f ()
gmytraceM True str = traceM str
gmytraceM False _ = pure ()


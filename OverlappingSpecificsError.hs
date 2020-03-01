{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module OverlappingSpecificsError where

class EqM a b where
	(===) :: a -> b -> Bool

instance {-# INCOHERENT #-} Eq a => EqM a a where
	a === b = a == b

instance {-# INCOHERENT #-} EqM a b where
	a === b = False

aretheyeq :: (Eq a, Eq b) => Either a b -> Either a b -> Bool
aretheyeq (Left a1) (Right b2) = a1 === b2

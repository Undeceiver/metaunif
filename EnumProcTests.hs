{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module EnumProcTests where

import EnumProc

multiples_enum :: Int -> EnumProc Int
multiples_enum n = multiples_enum_rec n 0

multiples_enum_rec :: Int -> Int -> EnumProc Int
multiples_enum_rec b x = Produce x (multiples_enum_rec b (x+b))

multiples_alt :: Int -> EnumProc Int
multiples_alt n = multiples_alt_rec n 0

multiples_alt_rec :: Int -> Int -> EnumProc Int
multiples_alt_rec b x | (mod x b) == 0 = Produce x (multiples_alt_rec b (x+1))
multiples_alt_rec b x = Continue (multiples_alt_rec b (x+1))

multiples_enum_prov :: Int -> ProvEnumProc String Int
multiples_enum_prov n = multiples_enum_prov_rec n 0

multiples_enum_prov_rec :: Int -> Int -> ProvEnumProc String Int
multiples_enum_prov_rec b x = x >: ((show x) ++ " is a multiple of " ++ (show b) ++ "; ") --> (multiples_enum_prov_rec b (x+b))






-- PERDITA: Look here.
naturals :: EnumProc Int
naturals = naturals_rec 1

naturals_rec :: Int -> EnumProc Int
naturals_rec n = n --> (naturals_rec (n+1))



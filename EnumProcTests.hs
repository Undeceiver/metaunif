{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module EnumProcTests where

import EnumProc

multiples_enum :: Int -> EnumProc Int
multiples_enum n = multiples_enum_rec n n

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






-- PERDITA, Look here.
-- 
-- I put the list equivalent next to every part.
naturals :: ProvEnumProc String Int
naturals = naturals_rec 1

naturals_rec :: Int -> ProvEnumProc String Int
naturals_rec n = (n >: ((show n) ++ " is a natural number; ")) --> (naturals_rec (n+1))

l_naturals :: [Int]
l_naturals = [1..]

-- Find those numbers such that their triple is equal to n*(n+7) for some n.
filter_1 :: Int -> EnumProc Bool
filter_1 x = eany (\y -> return (y * (y + 7) == (3*x))) (fmap raw naturals)

l_filter_1 :: Int -> Bool
l_filter_1 x = any (\y -> (y * (y + 7)) == (3*x)) l_naturals

-- Find those numbers such that their square plus 5 is a multiple of 3.
filter_2 :: Int -> Bool
filter_2 x = (mod ((x * x) + 5) 3) == 0

l_filter_2 :: Int -> Bool
l_filter_2 = filter_2

-- Now do the whole thing:
--	1. Take all naturals.
-- 	2. For each of them, calculate their multiples.
--	3. Filter them with filter_1.
--	4. For each of the resulting numbers, calculate their multiples.
--	5. Filter them with filter_2.
each_multiples :: ProvEnumProc String Int
each_multiples = naturals >>=: (multiples_enum_prov ->: (\x -> ("Calculate multiples of " ++ (show x) ++ "; ")))

each_multiples_filtered :: ProvEnumProc String Int
each_multiples_filtered = map_with_prov id (\x -> ("There is a natural n such that n*(n+7) is 3*" ++ (show x) ++ "; ")) (es_efilter (filter_1 . raw) each_multiples)

each_multiples_2 :: ProvEnumProc String Int
each_multiples_2 = each_multiples_filtered >>=: (multiples_enum_prov ->: (\x -> ("Calculate multiples of " ++ (show x) ++ "; ")))

result :: ProvEnumProc String Int
result = map_with_prov id (\x -> ((show x) ++ " squared plus 5 is a multiple of 3; ")) (efilter (filter_2 . raw) each_multiples_2)


-- Normal lists die.
l_each_multiples :: [Int]
l_each_multiples = concat (map (\x -> iterate (+x) 0) l_naturals)
-- Of course, here we could use a diagonalization over lists instead of concatenation, but it still is not good enough, I explain why later.

l_each_multiples_filtered :: [Int]
l_each_multiples_filtered = filter l_filter_1 l_each_multiples

l_each_multiples_2 :: [Int]
l_each_multiples_2 = concat (map (\x -> iterate (+x) 0) l_each_multiples_filtered)

l_result :: [Int]
l_result = filter filter_2 l_each_multiples_2


-- Even if we diagonalized instead of concatenating the lists (which I did not do because I don't have an implemented function diagonalize :: [[t]] -> [t] right now, even if I know how to do it), this would still not work.
-- The reason is that the filter 1 will return no values at all for some of the multiples, and a regular diagonalization would, in that case, end up dying when trying to produce a next element for one of the lists, because it is filtering an infinite list returning no values.
-- That's why I tried to provide a "complicated" filter 1 which isn't easily replaced by a generative function. Of course, this one can actually be replaced by a generative function, but it is already tedious. In my application, there is not that possibility: sometimes I just need to verify conditions instead of generating only those solutions that I need.
-- My implementation EnumProc, when filtering the infinite list and finding no values, generates an enumeration that, while producing no values, produces an infinite number of steps. Because diagonalization on EnumProc happens over steps rather than over values, this doesn't prevent the other lists which do return some results from outputting them.

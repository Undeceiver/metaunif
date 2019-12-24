{-# LANGUAGE ScopedTypeVariables #-}

module CouldNotDeduce where


class Class1 t where
	foo :: t -> Int

instance Class1 Int where
	foo = (+1)

fun2 :: a -> a
fun2 = id

fun1 :: forall a b. (Class1 a, Class1 b) => [a] -> [b] -> Int
fun1 [] [] = 0
fun1 [] (b:bs) = (foo b) + (fun1 ([] :: [a]) bs)


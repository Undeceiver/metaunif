{-# LANGUAGE PartialTypeSignatures #-}
import Metaresolution_tests
import Metaresolution

main = do_batch_unsat_f_tests [0..10] [5,10,15,20] [1,5,10,20,50] "Home Undeceiver" 3

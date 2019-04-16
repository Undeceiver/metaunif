{-# LANGUAGE PartialTypeSignatures #-}
import Metaresolution_tests
import Metaresolution

main = show_all_unsat_instantiations pepper_sig pepper_mvs pepper_sols
--main = show_all_unsat_instantiations pepper_nmv_sig pepper_nmv_mvs pepper_nmv_sols


{-# LANGUAGE PartialTypeSignatures #-}
module AutoTests where

import Data.Time
import System.CPUTime
import Control.Exception
import Control.DeepSeq
import Data.Time.Clock
import Data.Time.Calendar


-- Automated testing

-- Correct/incorrect and message.
data AutomatedTestResult = ATR Bool String

instance Show AutomatedTestResult where
	show (ATR True str) = "OK: " ++ str
	show (ATR False str) = "ERROR: " ++ str

data AutomatedTest = AT String AutomatedTestResult

instance Show AutomatedTest where
	show (AT desc result) = "Test \"" ++ desc ++ "\":\n" ++ (show result) ++ "\n\n"

atr_is_error :: AutomatedTestResult -> Bool
atr_is_error (ATR x _) = not x

at_is_error :: AutomatedTest -> Bool
at_is_error (AT _ x) = atr_is_error x

-- Custom properties
-- List of elements, property, message if all correct, message if found some exceptions (function of the exceptions)
atr_all_p :: [t] -> (t -> Bool) -> String -> ([t] -> String) -> AutomatedTestResult
atr_all_p ts p correct incorrect = if (all p ts) then (ATR True correct) else (ATR False (incorrect (filter (p_not p) ts)))

atr_any_p :: [t] -> (t -> Bool) -> String -> String -> AutomatedTestResult
atr_any_p ts p correct incorrect = if (any p ts) then (ATR True correct) else (ATR False incorrect)

atr_none_p :: [t] -> (t -> Bool) -> String -> ([t] -> String) -> AutomatedTestResult
atr_none_p ts p correct incorrect = if (any p ts) then (ATR False (incorrect (filter p ts))) else (ATR True correct)

-- Utility functions

combine_test_results :: [AutomatedTest] -> String
combine_test_results ts = if (any at_is_error ts) then (concat (map show (filter at_is_error ts))) else (concat (map show ts))

p_2_op :: (Bool -> Bool -> Bool) -> (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p_2_op op p1 p2 x = op (p1 x) (p2 x)

p_and = p_2_op (&&)
p_or = p_2_op (||)

p_not :: (a -> Bool) -> (a -> Bool)
p_not p x = not (p x)


-- Measuring running time

old_measure_time :: NFData t => t -> IO Integer
old_measure_time op = (do
	start <- getCPUTime	
	end <- op `deepseq` getCPUTime
	return (end - start))
	
measure_time_and_run :: Fractional t => IO x -> IO t
measure_time_and_run op = (do
	start <- getCPUTime
	op
	end <- getCPUTime
	op >> (return ((fromInteger (end - start))/1000000000000)))

measure_time :: (Fractional t, NFData x) => x -> IO t
measure_time op = (do
	start <- getCPUTime
	end <- deepseq op getCPUTime
	return ((fromInteger (end - start))/1000000000000))

--instance NFData t => NFData (IO t) where
--	rnf op = seq op ()

--measure_time :: (Fractional t, NFData x) => x -> IO t
--measure_time exp = ((\start -> do end <- getCPUTime; start >>= (\start2 -> return ((fromInteger (end - start2)/1000000000000)))) $!!
--	((\start -> deepseq exp start) $!!
--	(getCPUTime)
--	))


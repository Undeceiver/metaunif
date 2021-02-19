{-# LANGUAGE PartialTypeSignatures #-}
module AutoTests where

import Data.Time
import System.CPUTime
import Control.Exception
import Control.DeepSeq
import Data.Time.Clock
import Data.Time.Calendar
import System.Timeout
import AnswerSet
import Algorithm
import EnumProc


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

monadize_list :: Monad m => [m t] -> m [t]
monadize_list [] = return []
monadize_list (x:xs) = do {rx <- x; rxs <- monadize_list xs; return (rx:rxs)}

combine_test_results :: [AutomatedTest] -> String
combine_test_results ts = if (any at_is_error ts) then (concat (map show (filter at_is_error ts))) else (concat (map show ts))

p_2_op :: (Bool -> Bool -> Bool) -> (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p_2_op op p1 p2 x = op (p1 x) (p2 x)

p_and = p_2_op (&&)
p_or = p_2_op (||)

p_not :: (a -> Bool) -> (a -> Bool)
p_not p x = not (p x)

onesec :: Int
onesec = 1000000

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


-- First parameter is the test to compute. Second is the result if timeout. 
timeout_test :: Int -> AutomatedTestResult -> AutomatedTestResult -> IO AutomatedTestResult
timeout_test time actual_comp ifto = do {mb_timeout <- timeout time (deepseq (show actual_comp) (return actual_comp)); case mb_timeout of {Nothing -> return ifto; Just x -> return x}}

-- When there is an integer parameter that should be increased iteratively, to avoid deadlocks that fail to output errors that could be caught.
timeout_test_failfast :: Int -> Int -> (Int -> AutomatedTestResult) -> AutomatedTestResult -> IO AutomatedTestResult
timeout_test_failfast time n actual_comp ifto = do {mb_timeout <- timeout time (deepseq (show todo) (return todo)); case mb_timeout of {Nothing -> return ifto; Just x -> return x}} where todo = timeout_test_failfast_rec n actual_comp

timeout_test_failfast_rec :: Int -> (Int -> AutomatedTestResult) -> AutomatedTestResult
timeout_test_failfast_rec 0 actual_comp = ATR True "Base case for iterative testing. No tests were performed"
timeout_test_failfast_rec n actual_comp = case (timeout_test_failfast_rec (n-1) actual_comp) of {ATR True str -> (actual_comp n); ATR False str -> ATR False str}



doprint :: IO String -> IO ()
doprint op = do {r <- op; putStr r}



-- For answer sets
check_min_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_min_as title n as = if l < n then (AT title (ATR False ("Expected at least " ++ (show n) ++ " results, but could only find " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found at least " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake n ((implicitOnly as) \$ ())))

check_max_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_max_as title n as = if l > n then (AT title (ATR False ("Expected at most " ++ (show n) ++ " results, but found " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found less than " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((implicitOnly as) \$ ())))

check_exactly_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_exactly_as title n as = if l /= n then (AT title (ATR False ("Expected exactly " ++ (show n) ++ " results, but found " ++ (show l) ++ " instead."))) else (AT title (ATR True ("Correctly found exactly " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((implicitOnly as) \$ ())))

check_min_exp_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_min_exp_as title n as = if l < n then (AT title (ATR False ("Expected at least " ++ (show n) ++ " results, but could only find " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found at least " ++ (show n)  ++ " results."))) where l = uns_produce_next (elength (etake n ((enumAS as) \$ ())))

check_max_exp_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_max_exp_as title n as = if l > n then (AT title (ATR False ("Expected at most " ++ (show n) ++ " results, but found " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found less than " ++ (show n)  ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((enumAS as) \$ ())))

check_exactly_exp_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_exactly_exp_as title n as = if l /= n then (AT title (ATR False ("Expected exactly " ++ (show n) ++ " results, but found " ++ (show l) ++ " instead."))) else (AT title (ATR True ("Correctly found exactly " ++ (show n)  ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((enumAS as) \$ ())))


-- For enum procs
check_min_enum :: String -> Int -> EnumProc a -> AutomatedTest
check_min_enum title n en = if l < n then (AT title (ATR False ("Expected at least " ++ (show n) ++ " results, but could only find " ++  (show l) ++ "."))) else (AT title (ATR True ("Correctly found at least " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake n en))

check_max_enum :: String -> Int -> EnumProc a -> AutomatedTest
check_max_enum title n en = if l > n then (AT title (ATR False ("Expected at most " ++ (show n) ++ " results, but found " ++  (show l) ++ "."))) else (AT title (ATR True ("Correctly found less than " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n + 1) en))

check_exactly_enum :: String -> Int -> EnumProc a -> AutomatedTest
check_exactly_enum title n en = if l /= n then (AT title (ATR False ("Expected exactly " ++ (show n) ++ " results, but found " ++  (show l) ++ " instead."))) else (AT title (ATR True ("Correctly found exactly " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n+1) en))

check_any_enum :: Int -> String -> (String -> a -> AutomatedTest) -> EnumProc a -> AutomatedTest
check_any_enum maxen title ftest en = case filtered of {EnumProc.Empty -> AT title (ATR False ("None of the first " ++ (show maxen) ++ " results produced passed the check.")); Produce at _ -> at} where tk = etake maxen en; tkat = ftest title <$> tk; filtered = uns_ecollapse (efilter (\(AT title (ATR res str)) -> res) tkat)

check_all_enum :: Int -> String -> (String -> a -> AutomatedTest) -> EnumProc a -> AutomatedTest
check_all_enum maxen title ftest en = case filtered of {EnumProc.Empty -> AT title (ATR True ("All of the first " ++ (show maxen) ++ " results produced passed the check.")); Produce at _ -> AT title (ATR False ("Found a result amongst the first " ++ (show maxen) ++ " produced that did not pass the check."))} where tk = etake maxen en; tkat = ftest title <$> tk; filtered = uns_ecollapse (efilter (\(AT title (ATR res str)) -> not res) tkat)


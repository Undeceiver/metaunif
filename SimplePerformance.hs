{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module SimplePerformance where

import System.CPUTime
import HaskellPlus
import Control.Lens
import System.IO.Silently
import Control.DeepSeq
import System.Timeout
import Debug.Trace
import GlobalTrace
import System.IO.Unsafe

t_measure_io :: IO a -> IO (Integer, a)
t_measure_io io = do
	{
		before <- getCPUTime;
		a <- io;
		after <- getCPUTime;

		return (after - before, a)
	}

t_measure_io_jt :: IO a -> IO Integer
t_measure_io_jt io = fst <$> t_measure_io io

t_seconds :: Integer -> Double
t_seconds d = fromIntegral d / 10^12

t_measure_io_secs :: IO a -> IO (Double, a)
t_measure_io_secs io = (_1 ..~ t_seconds) <$> (t_measure_io io)

t_measure_io_secs_jt :: IO a -> IO Double
t_measure_io_secs_jt io = fst <$> t_measure_io_secs io

-- Measures how long it takes to calculate a enough to show it, but does not actually show it.
t_measure :: Show a => a -> IO (Integer, a)
t_measure a = t_measure_io (silence (putStr (show a)) >> return a)

t_measure_jt :: Show a => a -> IO Integer
t_measure_jt a = fst <$> t_measure a

t_measure_secs :: Show a => a -> IO (Double, a)
t_measure_secs a = t_measure_io_secs (silence (putStr (show a)) >> return a)

t_measure_secs_jt :: Show a => a -> IO Double
t_measure_secs_jt a = fst <$> t_measure_secs a

t_measure_deepseq :: NFData a => a -> IO (Integer, a)
t_measure_deepseq a = t_measure_io (deepseq a (return a))

t_measure_deepseq_jt :: NFData a => a -> IO Integer
t_measure_deepseq_jt a = fst <$> t_measure_deepseq a

t_measure_deepseq_secs :: NFData a => a -> IO (Double, a)
t_measure_deepseq_secs a = t_measure_io_secs (deepseq a (return a))

t_measure_deepseq_secs_jt :: NFData a => a -> IO Double
t_measure_deepseq_secs_jt a = fst <$> t_measure_deepseq_secs a

n_timeout :: Int -> IO () -> IO ()
n_timeout t io = timeout t io >> return ()

timeout_secs :: Double -> IO a -> IO (Maybe a)
timeout_secs secs io = timeout (floor (secs * 10^6)) io

n_timeout_secs :: Double -> IO () -> IO ()
n_timeout_secs secs io = timeout_secs secs io >> return ()


trace_measure :: NFData a => Bool -> (Integer -> String) -> a -> a
trace_measure False _ x = x
trace_measure True str a = unsafePerformIO printed_io
	where
		measured_io = t_measure_deepseq a;
		printed_io = measured_io >>= (\(time,aa) -> do {putStr (str time); return aa});

trace_measure_secs :: NFData a => Bool -> (Double -> String) -> a -> a
trace_measure_secs False _ x = x
trace_measure_secs True str a = unsafePerformIO printed_io
	where
		measured_io = t_measure_deepseq_secs a;
		printed_io = measured_io >>= (\(time,aa) -> do {putStr (str time); return aa});

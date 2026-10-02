-- Generated fixed-ambient registry format: 1
import Benchmark.Example4001.Input
import Whiel.Synthesis.Tests.BenchmarkPreprocRoundTrip

/- The printed preprocessed loop re-reads as the computed one. -/

open Whiel.Synthesis.Tests.BenchmarkNotationRoundTrip

set_option linter.hashCommand false
set_option linter.style.setOption false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

#roundTripPreproc Whiel.Benchmark.Example4001
-- End generated fixed-ambient registry format: 1

# Run `gpt-5.5-20260917-sample-5-3`

model: `gpt-5.5` (codex, effort medium, isolation bwrap)
limits: search 600.0 s, certification 1800.0 s, iterations 6, workers 32
started 2026-09-17T18:00:35-04:00, finished 2026-09-17T19:01:01-04:00, exit code 3
revision: `e9dc09926895304e1b52bdb17d8fa74564ee318b`
notes: 5-input sample: 3 valid (0001, 4001, 4041), 1 unknown (0134), 1 invalid (5040).
verifier summary: all_certified=False, interrupted=False, unrun=[]

| input | status | rounds | proposed | dropped | Core | pending | dead | time | detail |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| [Example0001](examples/Example0001/summary.md) | valid | 1 | 6 | 0 | 6 | 0 | 0 | 4 min 38 s |  |
| [Example0134](examples/Example0134/summary.md) | search_timeout | 3 | 30 | 0 | 30* | 0 | ? | 12 min 57 s | overall limit expired after 600s |
| [Example4001](examples/Example4001/summary.md) | valid | 1 | 3 | 0 | 4 | 0 | 0 | 5 min 16 s |  |
| [Example4041](examples/Example4041/summary.md) | valid | 3 | 17 | 0 | 17 | 0 | 0 | 34 min 49 s |  |
| [Example5040](examples/Example5040/summary.md) | invalid | 1 | 0 | 0 | 0 | 0 | 0 | 48 s |  |

Core/pending/dead come from the verifier's final state; a `*` marks a count read from the last prompt instead, because the run has not settled or was not recorded.

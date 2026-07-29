# Physlib alignment policy

RankR is Mathlib-only. Keep the core development that way while maintaining
deliberate compatibility with Physlib wherever both libraries represent the
same mathematics.

This is an alignment policy, not a porting plan. RankR owns its finite-level
positivity, Schmidt-rank, low-rank Choi, and amplification APIs; adding an
interoperability dependency must not obscure those mathematical interfaces.

## Compatibility boundary

The interfaces worth keeping aligned are:

| RankR | Physlib analogue | Required check |
| --- | --- | --- |
| `ptraceU`, `ptraceV` | matrix partial traces | traced factor and product-index order |
| `mapChoi`, `mapOfChoiLinear` | Choi matrix and inverse map | output/input register order |
| `krausSum`, `choiOf` | Kraus maps and their Choi matrices | conjugation and vectorization conventions |
| `mapAmplification` | tensoring a map with an identity | system/ancilla order and reindexing |
| `IsDensityMatrix` | bundled mixed states | positivity and trace normalization |
| `IsMapRPositive 1` | positive maps | the `Fin 1` ampliation bridge |
| `∀ r, IsMapRPositive r` | completely positive maps | all-level ampliation equivalence |
| `SchmidtNumberLE 1` | separable states | conversion between the two decomposition conventions |

Similarity of notation is not evidence of equality. In particular, any bridge
must expose register permutations and the difference between RankR's complex
Hilbert--Schmidt pairing and real inner products on Hermitian matrices.

## How alignment should be checked

If executable interoperability becomes useful, build it as a separate optional
adapter depending on pinned revisions of both projects. It should:

- prove narrow bridge theorems rather than replace RankR's paper-facing names;
- keep every product-index equivalence explicit;
- distinguish definitional equalities from theorem-level equivalences;
- remain outside `RankR`, `RankR.Core`, and the axiom-audit import graph; and
- fail visibly when either project changes a convention.

This adapter would be a semantic audit of the formal--informal boundary as much
as an interoperability layer.

## When to reconsider the dependency

Revisit a direct Physlib dependency only if one of the following changes:

1. Physlib gains public Schmidt-number, finite-level positivity,
   block-positivity, and low-rank Choi APIs that replace a substantial part of
   `RankR/Library`; or
2. several RankR applications begin using Physlib's bundled channels, states,
   entropy, or functional-calculus infrastructure.

Until then, prefer compatible conventions and explicit bridges over a core
dependency.

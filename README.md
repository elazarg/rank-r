# Rank-two Choi lifting, formalized in Lean

This repository studies a reusable way to turn a rank-two bound for the Choi
operator of a completely positive map into an $r$-positivity theorem at every
finite level $r$. The lift is the main construction; a sharp inequality for
the two partial traces of a low-rank matrix is its principal application.

[Read the paper](paper/rank-r.pdf) ·
[inspect the TeX source](paper/rank-r.tex) ·
[audit the formalization claim by claim](docs/FORMALIZATION.md)

## The construction

Let $\Phi$ be a completely positive map and let

$$
\beta _2(\Phi)
=\frac12\sup_{\mathrm{SR}(z)\le 2,\ \lVert z\rVert=1}
  \langle z,J(\Phi)z\rangle .
$$

Here $J(\Phi)$ is the Choi operator and $\mathrm{SR}$ denotes
Schmidt rank. Equivalently, $\beta _2(\Phi)$ measures the largest total
action of a normalized linear combination of Kraus operators on an
orthonormal pair. The main theorem proves, for every integer $r\ge1$, that

$$
\Phi\circ\tau
+(r-1)\beta _2(\Phi)
  \left(\Delta-\frac1r\mathrm{id}\right)
$$

is $r$-positive whenever the Kraus space of $\Phi$ is fixed by transpose.
Here $\tau$ is transpose and $\Delta(X)=\mathrm{Tr}(X)I$. Without the
transpose symmetry, the unprotected correction

$$
\Phi\circ\tau+(r-1)\beta _2(\Phi)\Delta
$$

is still $r$-positive. A map is $r$-positive when its ampliation by the
identity on $r\times r$ matrices is positive. The corrected map depends on
$r$; the theorem does not assert that one map is positive at every level.

The proof decomposes the negative Choi sector into the edges of a complete
graph. Each edge is controlled by the rank-two input, while the vertex degree
$r-1$ determines the amplification coefficient. Transpose symmetry removes
one scalar direction and produces the protected
$-\mathrm{id}/r$ term. Graph examples show that the universal
coefficient cannot be improved.

For the concrete double-skew Kraus family, the local constant is at most one
in every dimension and exactly one when both local dimensions are at least
two. After a map identity and four elementary Choi contractions, the lift
gives the flagship inequality

$$
\lVert\mathrm{Tr}_U C\rVert_2^2
+\lVert\mathrm{Tr}_V C\rVert_2^2
\le
r\lVert C\rVert_2^2+\frac1r|\mathrm{Tr}C|^2,
\qquad \mathrm{rank}(C)\le r .
$$

Both coefficients are dimension-uniform and sharp in the ranges stated in the
paper.

## Is this machinery useful for your problem?

It is a promising fit when:

- the target statement is a block-positivity, $r$-positivity, or low-rank
  matrix inequality;
- its difficult part can be represented as $\Phi\circ\tau$ for a completely
  positive map $\Phi$;
- the rank-two Choi constant $\beta _2(\Phi)$, or the equivalent two-vector
  Kraus action, is substantially easier to bound than the original
  rank-$r$ problem; and
- there is an application-specific identity that translates positivity of the
  corrected map back into the quantity of interest.

Transpose-even Kraus spaces are especially useful because they protect the
scalar direction. If that symmetry is absent, the unprotected theorem may
still apply, but usually with a weaker conclusion.

The construction is unlikely to help when the problem has no meaningful
rank/Schmidt-rank restriction, when computing $\beta _2$ is already as hard
as the original problem, or when no map or contraction identity decodes the
result. Sharpness is also a separate question: the lift supplies a universal
upper coefficient, while optimality for a particular family requires a
rank-$r$ witness.

The paper develops this diagnostic in more detail, including failure tests and
a comparison with the balanced-polarization proof of the partial-trace
inequality.

## What is formalized

The central chain is unconditional in finite coordinates:

- the generic protected and unprotected rank-two-to-$r$ lifts;
- the Autonne--Takagi and double-skew input;
- the map identity and partial-trace inequality;
- sharp witnesses and graph thresholds; and
- the complementary balanced-polarization proof and its stability estimate.

The repository also contains optional applications and companion
constructions: positive-map and Schmidt-number certificates, Ky Fan bounds,
graph inclusions, higher-arity exterior lifting, higher Choi constants, and a
Schmidt-number staircase. Some companion endpoints remain conditional or open;
the exact boundary is maintained in the
[formalization ledger](docs/FORMALIZATION.md).

Lean statements use matrices indexed by finite types. The transport from
abstract finite-dimensional Hilbert spaces to chosen coordinates is not
packaged as a theorem. Within those coordinates, the headline development
contains no `sorry`, custom `axiom`, `native_decide`, or local `set_option`
escape. The executable [axiom audit](RankR/Verification/Axioms/All.lean)
guards the expected surface:
`propext`, `Classical.choice`, and `Quot.sound`.

Lean checks deduction from the formal definitions. It does not by itself check
that those definitions faithfully express the informal mathematics; the
ledger records that correspondence explicitly.

## Where to start

| Goal | Starting point |
| --- | --- |
| Understand the mathematics and motivation | [paper/rank-r.pdf](paper/rank-r.pdf) |
| Check whether a paper claim is machine-verified | [docs/FORMALIZATION.md](docs/FORMALIZATION.md) |
| Reuse only the generic lift | `import RankR.Core.Amplification` |
| Use the headline partial-trace theorem | `import RankR` |
| Reuse matrix, Choi, Kraus, or Schmidt-rank infrastructure | `import RankR.Library` |
| Explore optional clients | `import RankR.Applications` or `import RankR.Companions` |
| Build the entire mathematical development | `import RankR.All` |
| Inspect notation and vectorization conventions | [RankR/Library/Conventions.lean](RankR/Library/Conventions.lean) |
| Inspect the trust boundary | [RankR/Verification/Axioms/All.lean](RankR/Verification/Axioms/All.lean) |
| Understand the intended Physlib alignment | [docs/PHYSLIB_ALIGNMENT.md](docs/PHYSLIB_ALIGNMENT.md) |

The source tree follows the same boundary:

- `RankR/Library/` contains reusable finite-coordinate infrastructure;
- `RankR/Core/Amplification/` contains the generic lift;
- `RankR/Core/DoubleSkew/` and `RankR/Core/PartialTrace/` contain the principal
  seed and application;
- `RankR/Applications/` contains downstream clients; and
- `RankR/Companions/` contains broader constructions and research directions.

## Build

The project uses Lean 4.32.0 and the Mathlib revision pinned in
`lake-manifest.json`.

```bash
lake exe cache get
lake build RankR
```

Useful broader targets are:

```bash
lake build RankR.All
lake build RankR.Verification.Axioms
```

## Attribution and provenance

The appendix presents the double-skew proof as an adaptation of
Fu--Gao--Park, reorganized around an explicit Autonne--Takagi factorization.
The partial-trace inequality was also obtained independently in concurrent
work by Fraser--Huber--Pozsgay--Vona, whose balanced-decomposition route is
compared with the Choi lift in the paper. The paper gives the full attribution
and literature context without making a priority claim.

The manuscript and formalization were developed with extensive AI assistance,
including mathematical exploration, exposition, and Lean proof generation.
The author directed the project, selected the claims and interfaces, and
checked the resulting development, but did not independently derive every
generated proof. The paper contains the complete disclosure.

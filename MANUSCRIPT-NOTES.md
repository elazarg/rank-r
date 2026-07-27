# Notes on `rank-r.tex` from formalizing it

Everything here survived both the numerical pre-flight (`preflight.py`, 19/19)
and, where formalized, Lean. **Nothing below is a claim that the manuscript is
wrong.** These are places where the write-up asserts something a reader cannot
check at the stated level of detail, uses a convention that defeats
self-checking, or takes a harder route than necessary.

Ordered by how much I think each matters.

---

## 1. Lemma 2.1's derivation from Fu–Gao–Park is not checkable as written

**`lem:double-skew`, the proof.** The chain is: zero-extend $U,V$ into a common
$\mathbb C^d$; identify $\operatorname{vec} K \in (\wedge^2U)\otimes(\wedge^2V)$;
apply the best-Schmidt-rank-2 approximation identity; apply FGP Thm 2.4 "with
antisymmetric pairs $(U_{\rm out},U_{\rm in})$ and $(V_{\rm out},V_{\rm in})$ and
Schmidt cut $(U_{\rm out}V_{\rm out}):(U_{\rm in}V_{\rm in})$"; apply Ky Fan.

FGP states its bound for antisymmetric pairs $(1,3)$ and $(2,4)$ on
$(\mathbb C^d)^{\otimes2}_{12}\otimes(\mathbb C^d)^{\otimes2}_{34}$ with the cut
$12{:}34$. That these are the same statement under relabeling is asserted, not
exhibited. **This is the single place where I would most expect an error, and it
is the only major step no amount of computation can check** — I verified the
*conclusion* of Lemma 2.1 numerically (tight at exactly $0.5$ for
$\dim U,\dim V \in \{2,3\}$), but a true statement can have a broken derivation.

*Suggested change:* display the relabeling explicitly — write down the
permutation of the four tensor factors carrying FGP's labeling to this one, and
state which of FGP's indices is which of yours. Three lines.

Also: the zero-extension step claims the extension "belongs to
$\mathfrak{so}(\mathbb C^d)\otimes\mathfrak{so}(\mathbb C^d)$ and has the same
nonzero singular values and Hilbert–Schmidt norm". True, but the first clause
needs one word — extending a skew matrix by zero stays skew *because the
embedding is a coordinate subspace inclusion*, which is where the choice of
orthonormal bases in the lemma statement is actually used.

## 2. "Placed on their labeled tensor factors" is a placeholder, not a convention

**After `eq:H_r`:** *"Here and below, operators are placed on their labeled
tensor factors, regardless of whether those factors are adjacent in the
displayed tensor ordering."*

This sentence is doing real work in `eq:Phi-expansion`, `eq:Phi-rhoT`, `eq:H_r`
and throughout §7, and it is the only specification of what those displays mean.
Formalizing it required defining the placements explicitly; there is no way to
verify a factor-ordering claim against a sentence.

*Suggested change:* fix the notation once. Either introduce
$\iota_{S}: \mathcal L(\mathcal H_S) \to \mathcal L(\mathcal H_{[n]})$ for
$S\subseteq[n]$ and write $\iota_{UQ}(\rho_{UQ})$, or state the permutation
unitary and write $\pi(\rho_{UQ}\otimes I_V)\pi^*$. Either makes §2 and §7
mechanically checkable.

## 3. The tightest inequality in the paper is the least explicit

**`eq:T-Cauchy` → `eq:T-operator-bound`.** The manuscript says "By Lemma 2.1,
each parenthesized expression is at most $\frac12\|K^{(ij)}_c\|_2^2$", then
displays the conclusion $(r-1)\|c\|_2^2$. Four constants must conspire: the
$1/\sqrt2$ from $\eta_{ij}$, the vertex degree $r-1$, the $1/2$ from Lemma 2.1,
and $\|K^{(ij)}\|_2^2 = 4\|c^{(ij)}\|_2^2$. The arithmetic
$\frac{r-1}{2}\cdot\frac12\cdot4 = r-1$ is never displayed.

I checked this numerically: the bound is **attained exactly**, ratio
$1.000000$. At $\dim U=\dim V=2$, $\mathfrak{so}(2)\otimes\mathfrak{so}(2)$ is
one-dimensional, so every orthonormal pair saturates Lemma 2.1. There is *zero*
slack. Any slip in those four constants and Proposition 2.2 fails, taking the
paper with it.

*Suggested change:* display the one-line arithmetic, and add a remark that the
bound is attained — a reader who knows there is no slack will check it, and a
reader who assumes there is margin will not.

## 4. `eq:Phi-Pminus-TTstar` asserts an index bijection

*"The last equality follows because the vectors in the first line are exactly
the columns of $\mathcal T$ indexed by $(i,j,\alpha,\beta)$."*

This is $\Phi(P_-) = \mathcal T\mathcal T^*$, and it is the step that converts
the Kraus expansion into a synthesis-map factorization. The justification is a
claim about how $\mathcal T$'s columns are indexed, but `eq:T-definition`
defines $\mathcal T$ as acting on coefficient arrays, without ever fixing a
column indexing.

*Suggested change:* state the column index set of $\mathcal T$ where
$\mathcal T$ is defined.

## 5. §3's trace–rank bound takes the long way round

The proof of Theorem 1.1 introduces the range projection $P$, notes $PC=C$ and
$\|P\|_2^2 = r_0$, and applies Hilbert–Schmidt Cauchy–Schwarz to get
$|\operatorname{Tr}C|^2 \le r_0\|C\|_2^2$.

But at that point in the proof the range factorization $C=\sum_i|e_i\rangle\langle d_i|$
is *already in hand*, and `eq:contraction-trace` already gives
$\operatorname{Tr}C = \sum_i\langle d_i,e_i\rangle$. So

$$|\operatorname{Tr}C|^2 \le \Big(\sum_i\|d_i\|\Big)^2 \le r_0\sum_i\|d_i\|^2 = r_0\|C\|_2^2$$

by Cauchy–Schwarz twice, with no projection. (This is how it is proved in
`RankR.normSq_trace_le`; introducing $P$ cost real infrastructure in Lean and
buys nothing on paper either.)

## 6. Carrying $1/\sqrt{s}$ through §3 is avoidable

$\psi$ is normalized, so every one of Lemma 3.1's four identities carries a
$1/s$, and $\psi$ itself a $1/\sqrt s$. Working with the unnormalized
$\delta_e := \sum_i e_i\otimes q_i$ instead makes them square-root-free — e.g.
$\langle\delta_e,\delta_d\rangle = \overline{\operatorname{Tr}C}$ exactly. The
normalization is needed only where $\rho$ must be a state, which in §3 it need
not be.

Purely cosmetic, but it removes a factor that has to be tracked correctly four
times.

## 7. Proposition 4.2 forward-references Proposition 4.3

`prop:sos-sector-gram` ends: *"The positivity of $B_E$ follows from the
complete-graph defect certificate below together with
$\operatorname{ran}\mathcal T_-\subseteq\psi^\perp$."* The certificate is
`prop:sos-complete-graph`, which comes after. Harmless, but §4 would read better
with the order reversed.

## 8. `so(U) ⊗ so(V)` should be said to be the span

Lemma 2.1 quantifies over $K\in\mathfrak{so}(U)\otimes\mathfrak{so}(V)$. Read as
the tensor product *space* this is what is meant and what the proof uses (via
$\operatorname{vec}K\in(\wedge^2U)\otimes(\wedge^2V)$). Read as the set of
elementary tensors $L\otimes M$ it would be a strictly weaker statement — and
`eq:T-definition` immediately applies the lemma to
$K^{(ij)}_c=\sum_{\alpha\beta}c_{\alpha\beta}L_\alpha\otimes M_\beta$, a general
element, not an elementary tensor.

One word ("the linear span of") removes the ambiguity. In Lean this had to be a
`Submodule.span`.

## 9. `eq:sos-complete-graph` is an identity — say so louder

The display is boxed and is an exact identity, not a bound (I verified it to
relative error $2\times10^{-15}$). The derivation — *"Adding and subtracting the
total edge action gives exactly"* — hides the one step where an identity could
degrade into an inequality. Since the exactness is the point of §4, the
intermediate is worth displaying.

## 10. The $\mathrm{Tr}_U$ convention cannot be self-checked until §5

$\mathrm{Tr}_U$ = trace *over* $U$ is stated once, in §1. Theorem 1.1 is
symmetric in $U$ and $V$, so a reader who silently adopts the opposite
convention will sail through §§1–4 and only go wrong at
`thm:exact-asymmetric-score`, where $a$ and $b$ attach to different factors.

*Suggested change:* one reminder at Theorem 5.9. (This is also why
`preflight.py` tests the asymmetric score specifically: it is the only check
that can detect the convention flip.)

## 11. Minor

- `SR` is used in the proof of Lemma 2.1 before `SN`/`SR` are given meanings;
  both are only `\DeclareMathOperator`'d. A one-line definition at first use.
- The proof of `eq:contraction-U` ends *"Expanding the right-hand side of
  (eq:contraction-U-expansion) gives the same sum"* — this is the bulkiest
  routine computation in the paper and is left entirely to the reader. Worth
  either displaying the common quadruple sum or noting explicitly that the
  expression is manifestly real because it is self-conjugate under $i\leftrightarrow j$
  together with $a\leftrightarrow a'$ (which is what makes the two natural ways of
  writing it agree).
- The sharpness paragraph after Theorem 1.1 gives four quantities and concludes
  equality. All four are correct, but it is worth saying that equality requires
  $\operatorname{rank}C = r$ exactly, not $\le r$ — which is why the example is
  built from a rank-$r$ projection.

# Changes to make in `rank-r.tex`

Every item below is a concrete edit: where, what is wrong or missing, and what
to put instead. No mathematical error was found — these are places where the
manuscript asserts something a reader cannot check at the stated level of
detail, uses a convention that defeats self-checking, or takes a longer route
than necessary.

Ordered by importance.

---

## 1. Display the Fu–Gao–Park relabeling — Lemma 2.1, proof

**Now:** "applying FGP Thm 2.4 with antisymmetric pairs
$(U_{\rm out},U_{\rm in})$ and $(V_{\rm out},V_{\rm in})$ and Schmidt cut
$(U_{\rm out}V_{\rm out}):(U_{\rm in}V_{\rm in})$".

FGP states its bound for antisymmetric pairs $(1,3)$, $(2,4)$ with cut
$12{:}34$. That these coincide is asserted, never exhibited — and it is the
step on which everything else rests.

**Add,** immediately before the application:

> Label the four factors $1=U_{\rm out}$, $2=V_{\rm out}$, $3=U_{\rm in}$,
> $4=V_{\rm in}$. Under this labeling the antisymmetric pairs
> $(U_{\rm out},U_{\rm in})$, $(V_{\rm out},V_{\rm in})$ are FGP's $(1,3)$,
> $(2,4)$, and the cut $(U_{\rm out}V_{\rm out}):(U_{\rm in}V_{\rm in})$ is
> FGP's $12{:}34$.

Two lines, and they turn the paper's least checkable step into its most
obvious one.

## 2. Fix the tensor-factor placement notation — after `eq:H_r`

**Now:** "operators are placed on their labeled tensor factors, regardless of
whether those factors are adjacent in the displayed tensor ordering."

This sentence is the only specification of what `eq:Phi-expansion`,
`eq:Phi-rhoT`, `eq:H_r` and all of §7 mean, and a factor-ordering claim cannot
be verified against prose.

**Replace** with fixed notation, either

- $\iota_S : \mathcal L(\mathcal H_S) \to \mathcal L(\mathcal H_{[n]})$ for
  $S \subseteq [n]$, writing $\iota_{UQ}(\rho_{UQ})$ in place of
  $\rho_{UQ}\otimes I_V$; or
- an explicit permutation unitary $\pi$, writing
  $\pi(\rho_{UQ}\otimes I_V)\pi^*$.

## 3. Display the constant arithmetic — `eq:T-Cauchy` → `eq:T-operator-bound`

**Now:** "By Lemma 2.1, each parenthesized expression is at most
$\frac12\|K^{(ij)}_c\|_2^2$", then the conclusion $(r-1)\|c\|_2^2$.

Four constants must conspire — the $1/\sqrt2$ from $\eta_{ij}$, the vertex
degree $r-1$, the $1/2$ from Lemma 2.1, and
$\|K^{(ij)}\|_2^2 = 4\|c^{(ij)}\|_2^2$ — and the arithmetic is never shown.

**Add** the displayed line $\frac{r-1}{2}\cdot\frac12\cdot 4 = r-1$, **and a
remark that the bound is attained**: at $\dim U = \dim V = 2$ the space
$\mathfrak{so}(2)\otimes\mathfrak{so}(2)$ is one-dimensional, so every
orthonormal pair saturates Lemma 2.1 and there is no slack anywhere in the
chain. A reader who knows that will check it; a reader who assumes margin
will not.

## 4. State the column indexing of $\mathcal T$ — `eq:T-definition`

`eq:Phi-Pminus-TTstar` is justified by "the vectors in the first line are
exactly the columns of $\mathcal T$ indexed by $(i,j,\alpha,\beta)$", but
`eq:T-definition` defines $\mathcal T$ as acting on coefficient arrays and
never fixes a column indexing.

**Add** the column index set where $\mathcal T$ is defined.

## 5. Say "linear span" — Lemma 2.1, statement

$K \in \mathfrak{so}(U)\otimes\mathfrak{so}(V)$, read as the set of elementary
tensors $L\otimes M$, would be strictly weaker than what the proof needs — and
`eq:T-definition` immediately applies the lemma to
$K^{(ij)}_c = \sum_{\alpha\beta}c_{\alpha\beta}L_\alpha\otimes M_\beta$, which
is not elementary.

**Change** to "the linear span of $\{L \otimes M\}$".

## 6. Replace the trace–rank argument — §3, proof of Theorem 1.1

**Now:** introduces the range projection $P$, notes $PC = C$ and
$\|P\|_2^2 = r_0$, and applies Hilbert–Schmidt Cauchy–Schwarz.

At that point the range factorization $C = \sum_i |e_i\rangle\langle d_i|$ is
already in hand, and `eq:contraction-trace` already gives
$\operatorname{Tr}C = \sum_i \langle d_i, e_i\rangle$.

**Replace** with two applications of Cauchy–Schwarz and no projection:

$$|\operatorname{Tr}C|^2 \le \Big(\sum_i\|d_i\|\Big)^2 \le r_0\sum_i\|d_i\|^2 = r_0\|C\|_2^2.$$

## 7. Drop the normalization through §2–§3

$\psi$ is normalized, so each of Lemma 3.1's four identities carries a $1/s$ and
$\psi$ itself a $1/\sqrt s$; `eq:rho-partial-transpose`, `eq:Phi-rhoT` and
`eq:H-decomposition` each carry a $1/r$; and $\eta_{ij}$ carries a $1/\sqrt2$.

**Use** the unnormalized $\delta_e := \sum_i e_i\otimes q_i$ and
$\rho_0 := |\delta_e\rangle\langle\delta_e| = r\rho$ instead. Then
$\langle\delta_e,\delta_d\rangle = \overline{\operatorname{Tr}C}$ exactly,
$\rho_0^{T_{UV}} = P_+ - P_-$, and

$$\Phi(\rho_0^{T_{UV}}) = I - \rho_{UQ}\otimes I_V - I_U\otimes\rho_{VQ} + \rho_0$$

with **no denominators at all**. $\rho$ must be a state only where a state is
required, which in §§2–3 it never is. This removes a factor that otherwise has
to be tracked correctly in six places.

## 8. Reorder §4 — Propositions 4.2 and 4.3

`prop:sos-sector-gram` ends "The positivity of $B_E$ follows from the
complete-graph defect certificate below", forward-referencing
`prop:sos-complete-graph`.

**Swap** the two propositions.

## 9. Display the intermediate in `eq:sos-complete-graph`

The boxed display is an exact identity, not a bound, and the derivation —
"Adding and subtracting the total edge action gives exactly" — hides the one
step at which an identity could degrade into an inequality. Since the exactness
is the point of §4,

**add** the intermediate step.

## 10. Restate the $\mathrm{Tr}_U$ convention at Theorem 5.9

$\mathrm{Tr}_U$ = trace *over* $U$ appears once, in §1. Theorem 1.1 is
symmetric in $U$ and $V$, so a reader who adopts the opposite convention passes
through §§1–4 undetected and goes wrong only at `thm:exact-asymmetric-score`,
where $a$ and $b$ attach to different factors.

**Add** a one-line reminder there.

## 11. Justify the zero-extension — Lemma 2.1, proof

"the resulting extension of $K$ belongs to
$\mathfrak{so}(\mathbb C^d)\otimes\mathfrak{so}(\mathbb C^d)$" is true, but

**add** the reason: the embedding is a coordinate-subspace inclusion, which is
where the choice of orthonormal bases in the lemma statement is actually used.

## 12. Smaller edits

- **`SR` and `SN`** are used from the proof of Lemma 2.1 onward but only
  `\DeclareMathOperator`'d. Add a one-line definition at first use.
- **Proof of `eq:contraction-U`** ends "Expanding the right-hand side of
  (eq:contraction-U-expansion) gives the same sum" — the bulkiest routine
  computation in the paper, left entirely to the reader. Either display the
  common quadruple sum, or note that the expression is self-conjugate under
  $i\leftrightarrow j$ together with $a\leftrightarrow a'$, which is what makes
  the two natural ways of writing it agree.
- **Sharpness paragraph after Theorem 1.1**: say that equality requires
  $\operatorname{rank}C = r$ exactly, not $\le r$ — which is why the example is
  built from a rank-$r$ projection.

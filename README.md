# terminal-contraction-lean

Lean 4 + Mathlib proofs about **certifying a terminal reading of a linear error recursion**.
The recursion is

$$E_j = F_j\,E_{j-1} + D_j,$$

with arbitrary transitions $F_j$ (singular or zero allowed) and local defects $D_j$.

Every statement is proved by the Lean kernel with no `sorry`, no warnings, and
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. All of them are in
[`TerminalContraction.lean`](TerminalContraction.lean).

**Classes.** `[L]`: new statement or construction, proved in Lean. `[L-known]`: Lean formalization of a known result. `refuted`: constructive counterexample in Lean. `example`: an instance that shows a phenomenon. All of them are kernel-checked: no `sorry`, no warnings, axioms within `propext`, `Classical.choice`, `Quot.sound`.

## Results

| Class | Statement | Lean name |
|-------|-----------|-----------|
| `[L-known]` | **Adjoint identity.** With $w_t=q$ and $w_{j-1}=F_j^\top w_j$: $q^\top E_t = w_b^\top E_b + \sum_{j=b+1}^{t} w_j^\top D_j$ for every cut $b\le t$ (matrix-valued errors, any commutative ring) | `adjoint_identity`, `adjoint_identityV` |
| `[L-known]` | **Independent-ball bound.** If $\lVert E_b\rVert\le e_b$ and $\lVert D_j\rVert\le\delta_j$, then $\lvert q^\top E_t\rvert\le\lVert w_b\rVert e_b+\sum_j\lVert w_j\rVert\delta_j$ | `terminal_bound` |
| `[L-known]` | **The bound is the exact supremum of that relaxed class** (aligned defects attain it) | `terminal_bound_attained` |
| `[L-known]` | **Common generators give an exact forward certificate.** If $D_j=G_jc$ with $\lVert c\rVert\le r$ and $E_0=M_0c$, then $E_t=M_tc$ with $M_j=F_jM_{j-1}+G_j$. So $\sup\lvert q^\top E_t\rvert=r\,\lVert M_t^\top q\rVert$ for **every** reader $q$ at once | `error_eq_genCert`, `genCert_bound`, `genCert_bound_attained` |
| `refuted` | **Refutation: the independent relaxation can be arbitrarily loose.** With cancelling generators the exact supremum is $0$, while the relaxation gives $2r$ | `cancellation_example` |
| `[L-known]` | **Sign constraints contract the certificate.** For nonnegative defects the exact supremum is $\delta\lVert w^+\rVert\le\delta\lVert w\rVert$, with strict inequality for $w=(1,-1)$ | `sign_constrained_bound`, `sign_constrained_attained`, `norm2_posPart_le`, `sign_constraint_strict` |
| `[L]` | **Size accounting.** A causal window of $L$ signed directions plus controls is smaller than a dense $128\times128$ binary64 state **iff** $L\le 63$; at $L=64$ it takes $132616$ B against $131072$ B. The forward generator certificate ($n\times m$) is smaller than an $n\times p$ state iff $m<p$, at every horizon | `window_breakeven`, `window_64_exceeds_dense`, `genCert_smaller` |

## Subspaces closed under the evolution ([`InvariantErrorSubspaces.lean`](InvariantErrorSubspaces.lean))

Same recursion with $E_0=D_0$ and arbitrary time-varying $F_j$. A family of subspaces $U_j$ is **closed** if
$F_{j+1}(U_j)\subseteq U_{j+1}$. These results describe when the error, or a compressed state, can be tracked exactly
by a certificate whose size **does not depend on the horizon**. That avoids the window break-even above.

| Class | Statement | Scope | Lean name |
|-------|-----------|-------|-----------|
| `[L]` | **Exact closure ⟺ invariance**: $E_t\in U_t$ for all $t$ and **all** defect sequences with $D_j\in U_j$ iff the family is closed | Any field, any vector space, arbitrary (also singular) $F_j$. Excludes nothing: it is an exact characterization | `closed_iff` |
| `[L]` | **Horizon-independent certificate**: if $F_{j+1}B_j=B_{j+1}T_{j+1}$ ($n\times m$ bases) and $D_j=B_jc_j$, then $E_t=B_tz_t$ with $z_{j+1}=T_{j+1}z_j+c_{j+1}$, and every reader $q$ is answered exactly by $(B_t^\top q)^\top z_t$ | Needs defects inside the moving subspace. The certificate has $n\,m+m$ numbers at every horizon | `error_eq_basis`, `reading_eq` |
| `[L]` | **Rank-one writes**: $x\mapsto x-\varphi(x)\,k$ preserves $U$ iff $k\in U$ or $U\subseteq\ker\varphi$ (also for nonzero gates $a\,(I-k\varphi)$) | Covers the delta rule $I-\beta kk^\top$ ($\varphi=\beta\langle k,\cdot\rangle$). Any other $U$ is broken by the write | `rankOne_invariant_iff`, `gated_invariant_iff` |
| `[L]` | Keys confined to $S$ make $S$ invariant under every write, and vectors annihilated by $\varphi$ are frozen | So only the $S$-component of the state evolves | `keys_in_span_invariant`, `frozen_of_annihilated` |
| `refuted` | **Layerwise amplification does not compose multiplicatively**: for every $M>0$, two layers each amplify some direction by $M$, yet their composition is the identity | The product of per-layer gains is only an upper bound for the terminal sensitivity, and it can be loose by any factor | `cancellation_of_gains` |
| `[L]` | **Size**: $n\,m+m<n^2$ iff $m\le n-1$, at every horizon | Compare with an independent-defect window, which is below an $n\times n$ binary64 state only for $L\le63$ when $n=128$ | `invariant_cert_smaller` |

## Active certificates ([`ActiveCertificates.lean`](ActiveCertificates.lean))

| Class | Statement | Lean name |
|-------|-----------|-----------|
| `[L-known]` | active correction `S̃ = Ŝ + E P`, `P = B(BᵀB)⁻¹Bᵀ`: exact error `E (1 - P)`, exact on `span B` | `correction_error`, `corrected_exact_on_basis` |
| `[L-known]` | `P² = P`, `P B = B` | `projector_mul_self`, `projector_mul_basis` |
| `[L-known]` | closure `(F S + u vᵀ) B = F (S B) + u (vᵀ B)`; basis-change split | `projected_closure`, `basis_change_split` |
| refuted | "a zero certificate on `B` implies zero error for every reader" (rank-one defect) | `discarded_dependency_returns` |

Details: [docs/active-certificates.md](docs/active-certificates.md).

## Open

- **Approximate closure.** If $F_{j+1}(U_j)$ leaves $U_{j+1}$ by at most $\eta_j$, is the drift bounded by
  $\sum_j\eta_j\prod_{i>j}\lVert F_i\rVert$ and is that sharp? Is there a smallest closed family containing a
  given reader-relevant subspace whose dimension stays bounded for structured key sequences?
- **Minimal closed families.** Characterize the smallest closed family that contains given subspaces. Which
  key sequences keep its dimension bounded uniformly in $t$?

## What it means

The adjoint identity turns a certificate for one reader into a sum of *transported* local
defects. Bounding each defect in its own ball is exact for that relaxed class, but the relaxed
class can be much larger than the true set of errors. Two structures make it contract:

- **defects through a shared low-dimensional generator.** Here the forward matrix $M_t$ is an
  inductive invariant, exact for all readers, and its size does not grow with the window;
- **sign information**, which replaces $\lVert w\rVert$ by $\lVert w^+\rVert$.

Without such structure, enlarging the window cannot beat the dense state past the exact
break-even computed above.

## Verify

```bash
lake exe cache get
scripts/audit.sh            # compiles each file and checks sorry, warnings and axioms
```

Pin: `leanprover/lean4:v4.33.1`, Mathlib `0df444a` (v4.33.1).

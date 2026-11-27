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

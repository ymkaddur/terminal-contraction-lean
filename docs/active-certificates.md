# Active certificates

Status labels: **[L-known]** formalized here, mathematically known or elementary;
**[L]** formalized here, statement new in this form; **refuted** the claim is false and the
counterexample is formalized; **open** not proved.

## Statement

A state `S` is approximated by `Ŝ`, with defect `E = S - Ŝ`. A protected basis `B` with `BᵀB`
invertible carries the projector `P = B (BᵀB)⁻¹ Bᵀ`. The active correction stores `Z = E B` and uses
`S̃ = Ŝ + Z (BᵀB)⁻¹ Bᵀ = Ŝ + E P`.

* `S - S̃ = E (1 - P)` exactly, and `(S - S̃) B = 0`: the corrected state is exact on every reader
  in the span of `B`.
* For an update `S' = F S + u vᵀ`, `S' B = F (S B) + u (vᵀ B)`: the projected representation
  evolves in closed form without the dense state.
* For an orthonormal `B` and any reader `C`, `E C = (E B)(Bᵀ C) + E (1 - P) C`.

## Motivation

Correct an approximation along a small protected subspace while storing only `k` columns, and know
exactly which error remains: the part of the defect outside the span of `B`.

## Proof

Direct matrix algebra: `P B = B` because `(BᵀB)⁻¹ (BᵀB) = 1`, which also gives `P² = P`.

## Counterexample

`discarded_dependency_returns`: `E = e₁ e₂ᵀ`, `B = e₁`, `C = e₂` in dimension 2. Then `BᵀB = 1`
and `E B = 0`, but `E C ≠ 0`. A zero certificate on the protected basis says nothing about readers
outside its span, so a change of basis or representation must carry the residual `E (1 - P)` and
cannot reset it to zero.

## Formalization

`ActiveCertificates.lean`

| Status | Statement | Lean name |
|--------|-----------|-----------|
| [L-known] | `S - (Ŝ + E P) = E (1 - P)` | `correction_error` |
| [L-known] | `P` is idempotent and `P B = B` | `projector_mul_self`, `projector_mul_basis` |
| [L-known] | the corrected state is exact on the protected basis | `corrected_exact_on_basis` |
| [L-known] | closure under `S' = F S + u vᵀ` | `projected_closure` |
| [L-known] | basis-change split for orthonormal `B` | `basis_change_split` |
| **refuted** | "a zero certificate on `B` implies zero error for every reader" | `discarded_dependency_returns` |

## Limitations

* Exact real arithmetic. No statement about floating point or rounding.
* Fixed basis. Moving bases, state-dependent projectors and the growth of the residual
  `E (1 - P)` under `F` are open: the residual obeys `Γ' = F Γ + u ((1 - P) v)ᵀ`, which mixes back
  into the protected span unless the span is invariant under `F`.

## Verification

`scripts/audit.sh` compiles every module with `#print axioms` of each theorem appended, and fails on
`sorry`, on warnings, or on axioms outside `propext`, `Classical.choice` and `Quot.sound`. Pinned
toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`.

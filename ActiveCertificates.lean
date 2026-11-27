import Mathlib

/-!
# Active certificates: projected correction, closure under rank-one updates, basis change

A state `S` is approximated by `Ŝ`, with defect `E = S - Ŝ`. A protected basis `B` (full column rank,
not necessarily orthonormal) carries the projector `P = B (BᵀB)⁻¹ Bᵀ`. The active correction stores
`Z = E B` and uses `S̃ = Ŝ + Z (BᵀB)⁻¹ Bᵀ = Ŝ + E P`.

* `correction_error`: `S - S̃ = E (1 - P)` exactly;
* `projector_mul_self`, `projector_mul_basis`: `P` is idempotent and fixes `B`, so the corrected
  state is exact on every reader in the span of `B` (`corrected_exact_on_basis`);
* `projected_closure`: for `S' = F S + u vᵀ`, `S' B = F (S B) + u (vᵀ B)`. The projected
  representation evolves in closed form, without the dense state;
* `basis_change_split`: for an orthonormal `B` (`BᵀB = 1`) and any reader `C`,
  `E C = Z (Bᵀ C) + E (1 - P) C`;
* `discarded_dependency_returns` (**refutation**): a zero certificate `Z = E B = 0` does not mean
  zero error for readers outside the span of `B`. A rank-one defect is invisible to `B` and fully
  visible to another reader, so debt cannot be reset by a change of basis or format.
-/

namespace ActiveCertificates

open Matrix

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]

/-- The projector onto the column span of `B`, for `BᵀB` invertible. -/
noncomputable def proj (B : Matrix n k ℝ) : Matrix n n ℝ := B * (Bᵀ * B)⁻¹ * Bᵀ

/-- Exact error of the active correction: `S - (Ŝ + E P) = E (1 - P)` with `E = S - Ŝ`. -/
theorem correction_error [DecidableEq n] (S Ŝ P : Matrix n n ℝ) : S - (Ŝ + (S - Ŝ) * P) = (S - Ŝ) * (1 - P) := by
  rw [mul_sub, mul_one]; abel

/-- The projector is idempotent. -/
theorem projector_mul_self (B : Matrix n k ℝ) (h : IsUnit (Bᵀ * B).det) :
    proj B * proj B = proj B := by
  unfold proj
  calc B * (Bᵀ * B)⁻¹ * Bᵀ * (B * (Bᵀ * B)⁻¹ * Bᵀ)
      = B * ((Bᵀ * B)⁻¹ * (Bᵀ * B)) * (Bᵀ * B)⁻¹ * Bᵀ := by simp only [Matrix.mul_assoc]
    _ = B * (Bᵀ * B)⁻¹ * Bᵀ := by rw [nonsing_inv_mul _ h, Matrix.mul_one]

/-- The projector fixes the protected basis. -/
theorem projector_mul_basis (B : Matrix n k ℝ) (h : IsUnit (Bᵀ * B).det) : proj B * B = B := by
  unfold proj
  rw [Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]

/-- The corrected state is exact on the protected basis: `(S - S̃) B = 0`. -/
theorem corrected_exact_on_basis [DecidableEq n] (S Ŝ : Matrix n n ℝ) (B : Matrix n k ℝ)
    (h : IsUnit (Bᵀ * B).det) : (S - (Ŝ + (S - Ŝ) * proj B)) * B = 0 := by
  rw [correction_error, Matrix.mul_assoc, Matrix.sub_mul 1 (proj B) B, Matrix.one_mul,
    projector_mul_basis B h, sub_self, Matrix.mul_zero]

omit [Fintype k] [DecidableEq k] in
/-- Closure of the projected representation under `S' = F S + u vᵀ`. -/
theorem projected_closure {r : Type*} [Fintype r] (F S : Matrix n n ℝ) (u : Matrix n r ℝ)
    (v : Matrix n r ℝ) (B : Matrix n k ℝ) :
    (F * S + u * vᵀ) * B = F * (S * B) + u * (vᵀ * B) := by
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]

omit [DecidableEq k] in
/-- Basis-change split for an orthonormal protected basis (`BᵀB = 1`, so `P = B Bᵀ`). -/
theorem basis_change_split [DecidableEq n] {c : Type*} [Fintype c] (E : Matrix n n ℝ) (B : Matrix n k ℝ)
    (C : Matrix n c ℝ) : E * C = (E * B) * (Bᵀ * C) + E * (1 - B * Bᵀ) * C := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- **Refutation**: zero certificate on the protected basis, nonzero error for another reader. -/
theorem discarded_dependency_returns :
    let E : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let B : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let C : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
    Bᵀ * B = 1 ∧ E * B = 0 ∧ E * C ≠ 0 := by
  intro E B C
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [B, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [E, B, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [E, C, Matrix.mul_apply, Fin.sum_univ_two] at this

end ActiveCertificates

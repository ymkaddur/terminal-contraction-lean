import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bilateral updates with moving readers

The state is observed on the columns of a reader matrix. The right factor pulls the next
readers back to the current input space. All products below allow rectangular factors.
-/

set_option autoImplicit false

namespace BilateralCertificates

open Matrix

section Step

variable {R o i p q k l : Type*} [Fintype i] [Fintype p] [Fintype q] [Fintype k]

/-- A factorization of the pulled-back readers gives an update using only the old readout. -/
theorem bilateral_step [Semiring R] (F : Matrix o i R) (S : Matrix i p R) (G : Matrix p q R)
    (U : Matrix o q R) (B : Matrix p k R) (Bnext : Matrix q l R) (M : Matrix k l R)
    (h : G * Bnext = B * M) :
    (F * S * G + U) * Bnext = F * (S * B) * M + U * Bnext := by
  simp only [Matrix.add_mul, Matrix.mul_assoc, h]

/-- The discrepancy for any proposed transfer, with the sign actual minus predicted. -/
theorem bilateral_residual [Ring R] (F : Matrix o i R) (S : Matrix i p R) (G : Matrix p q R)
    (U : Matrix o q R) (B : Matrix p k R) (Bnext : Matrix q l R) (M : Matrix k l R) :
    (F * S * G + U) * Bnext - (F * (S * B) * M + U * Bnext) =
      F * S * (G * Bnext - B * M) := by
  simp only [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_sub]
  abel

end Step

/-- Left multiplication preserves vanishing on fixed readers for every matrix fixing them. -/
theorem fixed_reader_residual {R o i p k : Type*} [Ring R] [Fintype i] [Fintype p]
    [DecidableEq p] (F : Matrix o i R) (E : Matrix i p R) (P : Matrix p p R) (B : Matrix p k R)
    (h : P * B = B) : F * (E * (1 - P)) * B = 0 := by
  simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, h, sub_self, Matrix.mul_zero]

/-- The reduced recurrence tracks the exact readout at every time, including changes of width. -/
theorem moving_readout {R n p : Type*} [Semiring R] [Fintype n] [Fintype p] (width : ℕ → ℕ)
    (F : ℕ → Matrix n n R) (G : ℕ → Matrix p p R) (U S : ℕ → Matrix n p R)
    (B : (t : ℕ) → Matrix p (Fin (width t)) R)
    (M : (t : ℕ) → Matrix (Fin (width t)) (Fin (width (t + 1))) R)
    (Z : (t : ℕ) → Matrix n (Fin (width t)) R) (h₀ : S 0 * B 0 = Z 0)
    (hS : ∀ t, S (t + 1) = F t * S t * G t + U t)
    (hZ : ∀ t, Z (t + 1) = F t * Z t * M t + U t * B (t + 1))
    (hB : ∀ t, G t * B (t + 1) = B t * M t) : ∀ t, S t * B t = Z t := by
  intro t
  induction t with
  | zero => exact h₀
  | succ t ih =>
    rw [hS, hZ, bilateral_step _ _ _ _ _ _ _ (hB t), ih]

section Necessity

variable {K o i p q k l : Type*} [Field K] [Fintype i] [Fintype p]

/-- A single-entry test state detects any pair of nonzero factors over a field. -/
theorem sandwich_zero_iff (F : Matrix o i K) (D : Matrix p l K) :
    (∀ S : Matrix i p K, F * S * D = 0) ↔ F = 0 ∨ D = 0 := by
  classical
  constructor
  · intro hall
    by_cases hF : F = 0
    · exact Or.inl hF
    right
    obtain ⟨r, a, ha⟩ : ∃ r a, F r a ≠ 0 := by
      by_contra! h
      exact hF (Matrix.ext h)
    ext j c
    have hz : (F * Matrix.single a j (1 : K) * D) r c = 0 :=
      congrArg (fun N : Matrix o l K => N r c) (hall (Matrix.single a j 1))
    have he : (F * Matrix.single a j (1 : K) * D) r c = F r a * D j c := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [Matrix.mul_single_apply_same, mul_one]
      · intro b _ hbj
        rw [Matrix.mul_single_apply_of_ne 1 a j r b hbj F, zero_mul]
      · simp
    exact (mul_eq_zero.mp (he.symm.trans hz)).resolve_left ha
  · rintro (rfl | rfl) S <;> simp

/-- Complete one-step classification for a prescribed transfer and every state. -/
theorem universal_step_iff [Fintype q] [Fintype k] (F : Matrix o i K) (G : Matrix p q K)
    (U : Matrix o q K) (B : Matrix p k K) (Bnext : Matrix q l K) (M : Matrix k l K) :
    (∀ S : Matrix i p K, (F * S * G + U) * Bnext = F * (S * B) * M + U * Bnext) ↔
      F = 0 ∨ G * Bnext = B * M := by
  calc
    _ ↔ ∀ S : Matrix i p K, F * S * (G * Bnext - B * M) = 0 := by
      apply forall_congr'
      intro S
      rw [← bilateral_residual F S G U B Bnext M, sub_eq_zero]
    _ ↔ _ := by rw [sandwich_zero_iff, sub_eq_zero]

end Necessity

section SideInformation

variable {K V W Y : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Y] [Module K Y]

/-- Observations on P determine the output on C precisely when P contains C, for nonzero F. -/
theorem observations_determine_iff (F : W →ₗ[K] Y) (hF : F ≠ 0) (P C : Submodule K V) :
    (∀ S T : V →ₗ[K] W, (∀ x ∈ P, S x = T x) → ∀ x ∈ C, F (S x) = F (T x)) ↔ C ≤ P := by
  constructor
  · intro hall x hx
    by_contra hmiss
    obtain ⟨f, hfx, hfP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hmiss inferInstance
    obtain ⟨y, hy⟩ : ∃ y, F y ≠ 0 := by
      by_contra! h
      exact hF (LinearMap.ext h)
    have hagree (z : V) (hz : z ∈ P) : (f.smulRight y) z = (0 : V →ₗ[K] W) z := by
      have hfz : f z ∈ P.map f := Submodule.mem_map_of_mem hz
      rw [hfP, Submodule.mem_bot] at hfz
      simp [hfz]
    have he := hall (f.smulRight y) 0 hagree x hx
    exact (smul_ne_zero hfx hy) (by simpa using he)
  · intro h S T hagree x hx
    rw [hagree x (h hx)]

/-- Extra reader directions span what is missing exactly when their quotient images do. -/
theorem side_readers_iff (P C D : Submodule K V) :
    C ≤ P ⊔ D ↔ C.map P.mkQ ≤ D.map P.mkQ := by
  rw [Submodule.map_le_iff_le_comap, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm]

variable [FiniteDimensional K V]

/-- A sufficient side-reader space has dimension at least that of the missing quotient image. -/
theorem side_dimension_le (P C D : Submodule K V) (h : C ≤ P ⊔ D) :
    Module.finrank K (C.map P.mkQ) ≤ Module.finrank K D :=
  (Submodule.finrank_mono ((side_readers_iff P C D).mp h)).trans (Submodule.finrank_map_le _ _)

/-- Lifting the missing quotient image attains the side-reader dimension bound. -/
theorem side_dimension_attained (P C : Submodule K V) :
    ∃ D : Submodule K V, C ≤ P ⊔ D ∧ Module.finrank K D = Module.finrank K (C.map P.mkQ) := by
  obtain ⟨s, hs⟩ := P.mkQ.exists_rightInverse_of_surjective P.range_mkQ
  let D := (C.map P.mkQ).map s
  have h : C ≤ P ⊔ D := (side_readers_iff P C D).mpr (by
    intro z hz
    exact ⟨s z, ⟨z, hz, rfl⟩, LinearMap.congr_fun hs z⟩)
  exact ⟨D, h, le_antisymm (Submodule.finrank_map_le s _) (side_dimension_le P C D h)⟩

end SideInformation

section RationalExamples

local notation "e₁" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℚ)
local notation "e₂" => (!![0; 1] : Matrix (Fin 2) (Fin 1) ℚ)

/-- Two different reader lines close with a nonidentity right transition and transfer. -/
theorem rational_moving_closed :
    let G : Matrix (Fin 2) (Fin 2) ℚ := !![0, 2; 1, 0]
    let M : Matrix (Fin 1) (Fin 1) ℚ := !![2]
    e₁ ≠ e₂ ∧ G * e₂ = e₁ * M ∧
      ∀ F S U : Matrix (Fin 2) (Fin 2) ℚ, (F * S * G + U) * e₂ = F * (S * e₁) * M + U * e₂ := by
  intro G M
  have h : G * e₂ = e₁ * M := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [G, M, Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨by decide, h, fun F S U => bilateral_step F S G U _ _ M h⟩

/-- With identity transport, equal old readings can have different next readings. -/
theorem rational_hidden_reader :
    let S : Matrix (Fin 1) (Fin 2) ℚ := !![0, 1]
    (0 : Matrix (Fin 1) (Fin 2) ℚ) * e₁ = S * e₁ ∧
      (0 : Matrix (Fin 1) (Fin 2) ℚ) * e₂ ≠ S * e₂ := by
  intro S
  constructor
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [S, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have he := congrArg (fun N : Matrix (Fin 1) (Fin 1) ℚ => N 0 0) h
    norm_num [S, Matrix.mul_apply, Fin.sum_univ_two] at he

/-- A zero left factor makes every state prediction exact even when no transfer exists. -/
theorem rational_zero_left :
    (¬ ∃ M : Matrix (Fin 1) (Fin 1) ℚ, e₂ = e₁ * M) ∧
      ∀ (S : Matrix (Fin 1) (Fin 2) ℚ) (M : Matrix (Fin 1) (Fin 1) ℚ),
        (0 : Matrix (Fin 1) (Fin 1) ℚ) * S * e₂ = 0 * (S * e₁) * M := by
  constructor
  · rintro ⟨M, h⟩
    have he := congrArg (fun N : Matrix (Fin 2) (Fin 1) ℚ => N 1 0) h
    simp [Matrix.mul_apply] at he
  · intro S M
    simp

end RationalExamples

section Communication

variable {K : Type*} [Field K] {r w n k d : ℕ}

/-- Split output coordinates and split residual readers realize every residual response on
the same old readout. This family witnesses the lower bound for arbitrary message encoders. -/
theorem hit_response (F : Matrix (Fin r) (Fin w) K) (J : Matrix (Fin w) (Fin r) K)
    (P : Matrix (Fin d) (Fin n) K) (C : Matrix (Fin n) (Fin d) K)
    (B : Matrix (Fin n) (Fin k) K) (hF : F*J=1) (hC : P*C=1) (hB : P*B=0)
    (T : Matrix (Fin r) (Fin d) K) :
    (J*T*P)*B = 0 ∧ F*(J*T*P)*C = T := by
  constructor
  · rw [Matrix.mul_assoc, hB, Matrix.mul_zero]
  · calc
      _ = ((F*J)*T)*(P*C) := by simp only [Matrix.mul_assoc]
      _ = T := by rw [hF,hC,Matrix.one_mul,Matrix.mul_one]

/-- Sharp alphabet size on a single old-readout fiber. Sending the residual matrix attains it. -/
theorem residual_message_bound [Fintype K] {M : Type*} [Fintype M]
    (F : Matrix (Fin r) (Fin w) K) (J : Matrix (Fin w) (Fin r) K)
    (P : Matrix (Fin d) (Fin n) K) (C : Matrix (Fin n) (Fin d) K)
    (B : Matrix (Fin n) (Fin k) K) (hF : F*J=1) (hC : P*C=1) (hB : P*B=0)
    (msg : Matrix (Fin w) (Fin n) K → M)
    (dec : Matrix (Fin w) (Fin k) K → M → Matrix (Fin r) (Fin d) K)
    (ok : ∀ S, dec (S*B) (msg S) = F*S*C) :
    Fintype.card K ^ (d*r) ≤ Fintype.card M := by
  classical
  have eqn (T : Matrix (Fin r) (Fin d) K) : dec 0 (msg (J*T*P)) = T := by
    have h := ok (J*T*P)
    have e := hit_response F J P C B hF hC hB T
    rwa [e.1, e.2] at h
  have inj : Function.Injective (fun T : Matrix (Fin r) (Fin d) K => msg (J*T*P)) := by
    intro a b h
    exact (eqn a).symm.trans ((congrArg (dec 0) h).trans (eqn b))
  calc
    _ = Fintype.card (Fin r → Fin d → K) := by
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_mul]
    _ ≤ _ := Fintype.card_le_of_injective _ inj

end Communication

end BilateralCertificates

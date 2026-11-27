import Mathlib

/-!
# Terminal contraction of linear error recursions

Let an error evolve by `E_j = F_j E_{j-1} + D_j` (local defects `D_j`, arbitrary transitions
`F_j`, singular or zero allowed). For a terminal reader `q`, transport it backwards:
`w_t = q`, `w_{j-1} = F_jᵀ w_j`. This file proves, with every claim labelled:

* **[L] adjoint identity**: `qᵀ E_t = w_bᵀ E_b + Σ_{j=b+1}^{t} w_jᵀ D_j` for every cut `b ≤ t`
  (`adjoint_identity`, matrix-valued errors over any commutative ring);
* **[L] independent-ball bound and its exactness**: if `‖E_b‖ ≤ e_b` and `‖D_j‖ ≤ δ_j`
  independently, then `|qᵀE_t| ≤ ‖w_b‖ e_b + Σ ‖w_j‖ δ_j`, and the supremum over that relaxed
  class is attained (`terminal_bound`, `terminal_bound_attained`);
* **[L] common generators give an exact forward certificate**: if the defects factor through
  one shared parameter, `D_j = G_j c` with `‖c‖ ≤ r`, then `E_t = M_t c` with the forward
  recursion `M_j = F_j M_{j-1} + G_j`; hence `sup |qᵀE_t| = r ‖M_tᵀ q‖` **for every reader
  simultaneously** (`error_eq_genCert`, `genCert_bound`, `genCert_bound_attained`);
* **[L] refutation of the independence relaxation as a size-efficient certificate**: with
  cancelling generators the exact supremum is `0` while the independent relaxation gives `2r`
  (`cancellation_example`), so the relaxation can be arbitrarily loose;
* **[L] sign constraints contract the certificate**: for nonnegative defects the exact
  supremum is `δ ‖w⁺‖ ≤ δ ‖w‖`, strictly smaller when `w` has a negative entry;
* **[L] size accounting**: a window of `L` signed directions plus controls exceeds an `n × n`
  binary64 state exactly when `L ≥ 64` for `n = 128` (`window_breakeven`), while the forward
  generator certificate (`n × m` entries) is smaller than an `n × p` state iff `m < p`.

Vectors are `Fin n → ℝ` with the Euclidean norm `norm2 v = √(Σ vᵢ²)`.
-/

namespace TerminalContraction

open Matrix Finset

/-! ## The adjoint identity (exact, any commutative ring, singular transitions allowed) -/

section Identity

variable {R : Type*} [CommRing R] {n p : ℕ}

/-- Reader transported `k` steps back from time `t`: `w_t = q`, `w_{j-1} = F_jᵀ w_j`. -/
def transport (F : ℕ → Matrix (Fin n) (Fin n) R) (q : Fin n → R) (t : ℕ) : ℕ → (Fin n → R)
  | 0 => q
  | k + 1 => transport F q t k ᵥ* F (t - k)

/-- Matrix-valued error recursion `E (j+1) = F (j+1) * E j + D (j+1)`. -/
def IsErrorRecursion (F : ℕ → Matrix (Fin n) (Fin n) R) (D E : ℕ → Matrix (Fin n) (Fin p) R) :
    Prop :=
  ∀ j, E (j + 1) = F (j + 1) * E j + D (j + 1)

/-- **[L] Adjoint identity.** For every cut `t - k` with `k ≤ t`:
`qᵀ E_t = w_{t-k}ᵀ E_{t-k} + Σ_{i<k} w_{t-i}ᵀ D_{t-i}`. -/
theorem adjoint_identity (F : ℕ → Matrix (Fin n) (Fin n) R) (D E : ℕ → Matrix (Fin n) (Fin p) R)
    (hE : IsErrorRecursion F D E) (q : Fin n → R) (t : ℕ) :
    ∀ k ≤ t, q ᵥ* E t =
      transport F q t k ᵥ* E (t - k) + ∑ i ∈ range k, transport F q t i ᵥ* D (t - i) := by
  intro k
  induction k with
  | zero => intro _; simp [transport]
  | succ k ih =>
    intro hk
    rw [ih (by omega), Finset.sum_range_succ]
    have hrec : E (t - k) = F (t - k) * E (t - (k + 1)) + D (t - k) := by
      have h := hE (t - (k + 1))
      rwa [show t - (k + 1) + 1 = t - k by omega] at h
    rw [hrec, Matrix.vecMul_add, ← Matrix.vecMul_vecMul]
    simp only [transport]
    abel

end Identity

/-! ## Euclidean bounds for vector-valued errors -/

section Bounds

variable {n : ℕ}

/-- Euclidean norm of a vector. -/
noncomputable def norm2 (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

theorem norm2_nonneg (v : Fin n → ℝ) : 0 ≤ norm2 v := Real.sqrt_nonneg _

theorem dot_self_eq (v : Fin n → ℝ) : v ⬝ᵥ v = norm2 v ^ 2 := by
  unfold norm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  simp [dotProduct, sq]

theorem norm2_smul (c : ℝ) (v : Fin n → ℝ) : norm2 (c • v) = |c| * norm2 v := by
  unfold norm2
  have h : ∑ i, (c • v) i ^ 2 = c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Cauchy–Schwarz for `dotProduct`. -/
theorem abs_dot_le (v w : Fin n → ℝ) : |v ⬝ᵥ w| ≤ norm2 v * norm2 w := by
  unfold norm2
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  apply Real.abs_le_sqrt
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  simpa [dotProduct] using h

/-- A vector of norm at most `r` aligned with `v`. -/
theorem exists_aligned (v : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ d : Fin n → ℝ, norm2 d ≤ r ∧ v ⬝ᵥ d = r * norm2 v := by
  by_cases hv : norm2 v = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [norm2, hr]
    · simp [hv]
  · have hpos : 0 < norm2 v := lt_of_le_of_ne (norm2_nonneg v) (Ne.symm hv)
    refine ⟨(r / norm2 v) • v, ?_, ?_⟩
    · rw [norm2_smul, abs_of_nonneg (div_nonneg hr hpos.le), div_mul_cancel₀ _ hv]
    · rw [dotProduct_smul, smul_eq_mul, dot_self_eq]
      field_simp

/-- Reader transported along vector-valued recursions. -/
def transportV (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (t : ℕ) : ℕ → (Fin n → ℝ)
  | 0 => q
  | k + 1 => transportV F q t k ᵥ* F (t - k)

/-- **[L] Adjoint identity, vector form**: `q ⬝ e_t = w_{t-k} ⬝ e_{t-k} + Σ_{i<k} w_{t-i} ⬝ d_{t-i}`. -/
theorem adjoint_identityV (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (d e : ℕ → (Fin n → ℝ))
    (hE : ∀ j, e (j + 1) = F (j + 1) *ᵥ e j + d (j + 1)) (q : Fin n → ℝ) (t : ℕ) :
    ∀ k ≤ t, q ⬝ᵥ e t =
      transportV F q t k ⬝ᵥ e (t - k) + ∑ i ∈ range k, transportV F q t i ⬝ᵥ d (t - i) := by
  intro k
  induction k with
  | zero => intro _; simp [transportV]
  | succ k ih =>
    intro hk
    rw [ih (by omega), Finset.sum_range_succ]
    have hrec : e (t - k) = F (t - k) *ᵥ e (t - (k + 1)) + d (t - k) := by
      have h := hE (t - (k + 1))
      rwa [show t - (k + 1) + 1 = t - k by omega] at h
    rw [hrec, dotProduct_add, dotProduct_mulVec]
    simp only [transportV]
    ring

/-- **[L] Independent-ball bound**: `|q ⬝ e_t| ≤ ‖w_{t-k}‖ e_b + Σ_{i<k} ‖w_{t-i}‖ δ_{t-i}`. -/
theorem terminal_bound (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (d e : ℕ → (Fin n → ℝ))
    (hE : ∀ j, e (j + 1) = F (j + 1) *ᵥ e j + d (j + 1)) (q : Fin n → ℝ) {t k : ℕ} (hk : k ≤ t)
    {eb : ℝ} (δ : ℕ → ℝ) (heb : norm2 (e (t - k)) ≤ eb)
    (hd : ∀ i < k, norm2 (d (t - i)) ≤ δ (t - i)) :
    |q ⬝ᵥ e t| ≤ norm2 (transportV F q t k) * eb +
      ∑ i ∈ range k, norm2 (transportV F q t i) * δ (t - i) := by
  rw [adjoint_identityV F d e hE q t k hk]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · exact le_trans (abs_dot_le _ _) (mul_le_mul_of_nonneg_left heb (norm2_nonneg _))
  · refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
    exact le_trans (abs_dot_le _ _)
      (mul_le_mul_of_nonneg_left (hd i (Finset.mem_range.1 hi)) (norm2_nonneg _))

/-- **[L] The independent-ball bound is the exact supremum of the relaxed class**: for any
transported readers `w`, aligned defects attain it. -/
theorem terminal_bound_attained (w : ℕ → (Fin n → ℝ)) (k : ℕ) {eb : ℝ} (δ : ℕ → ℝ)
    (heb : 0 ≤ eb) (hδ : ∀ i, 0 ≤ δ i) :
    ∃ (Eb : Fin n → ℝ) (Dv : ℕ → (Fin n → ℝ)), norm2 Eb ≤ eb ∧ (∀ i, norm2 (Dv i) ≤ δ i) ∧
      w k ⬝ᵥ Eb + ∑ i ∈ range k, w i ⬝ᵥ Dv i =
        norm2 (w k) * eb + ∑ i ∈ range k, norm2 (w i) * δ i := by
  obtain ⟨Eb, hEb, hEbw⟩ := exists_aligned (w k) heb
  choose Dv hDv hDvw using fun i => exists_aligned (w i) (hδ i)
  refine ⟨Eb, Dv, hEb, hDv, ?_⟩
  rw [hEbw, mul_comm eb]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hDvw i, mul_comm]

/-! ## Common generators: an exact forward certificate -/

variable {m : ℕ}

/-- Forward certificate `M_0`, `M_{j+1} = F_{j+1} M_j + G_{j+1}` (an `n × m` matrix). -/
def genCert (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (G : ℕ → Matrix (Fin n) (Fin m) ℝ)
    (M0 : Matrix (Fin n) (Fin m) ℝ) : ℕ → Matrix (Fin n) (Fin m) ℝ
  | 0 => M0
  | j + 1 => F (j + 1) * genCert F G M0 j + G (j + 1)

/-- **[L] Defects through a shared generator stay in the image of the certificate**:
`d_j = G_j c` and `e_0 = M_0 c` imply `e_t = M_t c` for every `t`. -/
theorem error_eq_genCert (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (G : ℕ → Matrix (Fin n) (Fin m) ℝ)
    (M0 : Matrix (Fin n) (Fin m) ℝ) (c : Fin m → ℝ) (d e : ℕ → (Fin n → ℝ))
    (hE : ∀ j, e (j + 1) = F (j + 1) *ᵥ e j + d (j + 1)) (hd : ∀ j, d (j + 1) = G (j + 1) *ᵥ c)
    (h0 : e 0 = M0 *ᵥ c) : ∀ t, e t = genCert F G M0 t *ᵥ c := by
  intro t
  induction t with
  | zero => simpa [genCert] using h0
  | succ t ih => rw [hE, ih, hd, genCert, Matrix.add_mulVec, Matrix.mulVec_mulVec]

/-- **[L] Exact bound for every reader**: `|q ⬝ e_t| ≤ r ‖M_tᵀ q‖` when `‖c‖ ≤ r`. -/
theorem genCert_bound (M : Matrix (Fin n) (Fin m) ℝ) (q : Fin n → ℝ) {c : Fin m → ℝ} {r : ℝ}
    (hc : norm2 c ≤ r) : |q ⬝ᵥ (M *ᵥ c)| ≤ norm2 (q ᵥ* M) * r := by
  rw [dotProduct_mulVec]
  exact le_trans (abs_dot_le _ _) (mul_le_mul_of_nonneg_left hc (norm2_nonneg _))

/-- **[L] … and it is attained**: the supremum over `‖c‖ ≤ r` is exactly `r ‖M_tᵀ q‖`. -/
theorem genCert_bound_attained (M : Matrix (Fin n) (Fin m) ℝ) (q : Fin n → ℝ) {r : ℝ}
    (hr : 0 ≤ r) : ∃ c : Fin m → ℝ, norm2 c ≤ r ∧ q ⬝ᵥ (M *ᵥ c) = norm2 (q ᵥ* M) * r := by
  obtain ⟨c, hc, hcv⟩ := exists_aligned (q ᵥ* M) hr
  exact ⟨c, hc, by rw [dotProduct_mulVec, hcv, mul_comm]⟩

/-- **[L] Cancellation refutes the independent relaxation.** One coordinate, identity
transitions, generators `G_1 = 1` and `G_2 = -1`, `M_0 = 0`: the forward certificate vanishes
at `t = 2` (exact supremum `0` for every reader), whereas the independent relaxation of the same
two defects, each of radius `r`, bounds the reader `q = 1` by `2r`. -/
theorem cancellation_example (r : ℝ) :
    genCert (n := 1) (m := 1) (fun _ => 1) (fun j => if j = 1 then 1 else -1) 0 2 = 0 ∧
      norm2 (transportV (n := 1) (fun _ => 1) (fun _ => 1) 2 0) * r +
        norm2 (transportV (n := 1) (fun _ => 1) (fun _ => 1) 2 1) * r = 2 * r := by
  constructor
  · ext i j
    simp [genCert]
  · simp [transportV, norm2]
    ring

/-! ## Sign-constrained defects -/

/-- Positive part of a vector. -/
noncomputable def posPart (w : Fin n → ℝ) : Fin n → ℝ := fun i => max (w i) 0

theorem norm2_posPart_le (w : Fin n → ℝ) : norm2 (posPart w) ≤ norm2 w := by
  unfold norm2 posPart
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_total (w i) 0 with h | h
  · rw [max_eq_right h, zero_pow two_ne_zero]; exact sq_nonneg _
  · rw [max_eq_left h]

/-- **[L] Sign constraints contract the certificate**: for nonnegative defects,
`w ⬝ d ≤ ‖w⁺‖ δ` (and `‖w⁺‖ ≤ ‖w‖`). -/
theorem sign_constrained_bound (w d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) {δ : ℝ}
    (hδ : norm2 d ≤ δ) : w ⬝ᵥ d ≤ norm2 (posPart w) * δ := by
  have h1 : w ⬝ᵥ d ≤ posPart w ⬝ᵥ d :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hd i)
  have h2 : posPart w ⬝ᵥ d ≤ norm2 (posPart w) * norm2 d := le_trans (le_abs_self _) (abs_dot_le _ _)
  exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left hδ (norm2_nonneg _)))

/-- **[L] … and the bound is attained by a nonnegative defect.** -/
theorem sign_constrained_attained (w : Fin n → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d : Fin n → ℝ, (∀ i, 0 ≤ d i) ∧ norm2 d ≤ δ ∧ w ⬝ᵥ d = norm2 (posPart w) * δ := by
  by_cases hv : norm2 (posPart w) = 0
  · exact ⟨0, fun _ => le_rfl, by simp [norm2, hδ], by simp [hv]⟩
  · have hpos : 0 < norm2 (posPart w) := lt_of_le_of_ne (norm2_nonneg _) (Ne.symm hv)
    refine ⟨(δ / norm2 (posPart w)) • posPart w, fun i => ?_, ?_, ?_⟩
    · exact mul_nonneg (div_nonneg hδ hpos.le) (le_max_right _ _)
    · rw [norm2_smul, abs_of_nonneg (div_nonneg hδ hpos.le), div_mul_cancel₀ _ hv]
    · have hw : w ⬝ᵥ posPart w = posPart w ⬝ᵥ posPart w := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [posPart]
        rcases le_total (w i) 0 with h | h
        · rw [max_eq_right h]; ring
        · rw [max_eq_left h]
      rw [dotProduct_smul, smul_eq_mul, hw, dot_self_eq]
      field_simp

/-- Strictness: for `w = (1, -1)`, `‖w⁺‖ = 1 < √2 = ‖w‖`. -/
theorem sign_constraint_strict :
    norm2 (posPart ![(1 : ℝ), -1]) = 1 ∧ norm2 ![(1 : ℝ), -1] = Real.sqrt 2 := by
  constructor
  · simp [norm2, posPart, Fin.sum_univ_two]
  · simp [norm2, Fin.sum_univ_two]
    norm_num

end Bounds

/-! ## Size accounting -/

/-- Bytes of a causal window of `L` signed directions (`n` binary64 each), `L` controls
(`n + 2` binary64 each) and `L + 1` scalar cut bounds. -/
def windowBytes (n L : ℕ) : ℕ := 8 * (L * n + L * (n + 2) + (L + 1))

/-- Bytes of a dense `n × n` binary64 state. -/
def denseBytes (n : ℕ) : ℕ := 8 * (n * n)

/-- **[L]** At `n = 128`: the window of `64` takes `132616` bytes, the dense state `131072`. -/
theorem window_64_exceeds_dense :
    windowBytes 128 64 = 132616 ∧ denseBytes 128 = 131072 ∧ denseBytes 128 < windowBytes 128 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [windowBytes, denseBytes]

/-- **[L] Exact break-even**: the independent window is smaller than the dense state iff
`L ≤ 63` (for `n = 128`). Enlarging the window beyond that cannot pay off. -/
theorem window_breakeven (L : ℕ) : windowBytes 128 L < denseBytes 128 ↔ L ≤ 63 := by
  unfold windowBytes denseBytes
  omega

/-- **[L]** The forward generator certificate (`n × m` binary64 entries) is smaller than an
`n × p` binary64 state iff `m < p`, independently of the horizon. -/
theorem genCert_smaller {n m p : ℕ} (hn : 0 < n) : 8 * (n * m) < 8 * (n * p) ↔ m < p := by
  constructor
  · intro h
    by_contra hmp
    push Not at hmp
    have := Nat.mul_le_mul_left n hmp
    omega
  · intro h
    have := Nat.mul_lt_mul_of_pos_left h hn
    omega

end TerminalContraction

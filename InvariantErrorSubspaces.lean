import Mathlib

/-!
# Subspaces closed under non-stationary linear evolution

An error evolves by `E_0 = D_0`, `E_{j+1} = F_{j+1}(E_j) + D_{j+1}` with arbitrary, time-varying
linear transitions `F_j` and local defects `D_j`. A family of subspaces `U_j` is **closed** if
`F_{j+1}(U_j) ⊆ U_{j+1}`. Results, with their class:

* **[L] exact closure ⟺ invariance** (`closed_iff`): the error stays in `U_t` for every `t`,
  for every defect sequence with `D_j ∈ U_j`, if and only if the family is closed;
* **[L] horizon-independent certificate** (`error_eq_basis`, `reading_eq`): if `F_{j+1} B_j =
  B_{j+1} T_{j+1}` for `n × m` bases `B_j` and defects `D_j = B_j c_j`, then `E_t = B_t z_t` with
  `z_{j+1} = T_{j+1} z_j + c_{j+1}`. Every reader is answered exactly by `(B_tᵀ q)ᵀ z_t`, from
  `n·m + m` numbers at every horizon;
* **[L] invariance under rank-one writes** (`rankOne_invariant_iff`): `x ↦ x − φ(x) k` preserves
  a subspace `U` iff `k ∈ U` or `U ⊆ ker φ`. This covers the delta rule `I − β k kᵀ` and any
  nonzero gate. Corollaries: keys confined to `K` make `K` invariant (`keys_in_span_invariant`), and a
  complement annihilated by every `φ_j` is frozen (`frozen_of_annihilated`);
* **refuted: layerwise amplification does not compose multiplicatively** (`cancellation_of_gains`):
  for every `M > 0`, two layers amplify some direction by `M` each, yet their composition is the
  identity;
* **[L] size** (`invariant_cert_smaller`): `n·m + m < n²` iff `m ≤ n − 1`, at every horizon, against
  the window bound `L ≤ 63` for `n = 128` of an independent-defect register.
-/

namespace InvariantErrorSubspaces

open Matrix

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Error recursion `E_0 = D_0`, `E_{j+1} = F_{j+1}(E_j) + D_{j+1}`. -/
def run (F : ℕ → V →ₗ[K] V) (D : ℕ → V) : ℕ → V
  | 0 => D 0
  | j + 1 => F (j + 1) (run F D j) + D (j + 1)

/-- A family of subspaces closed under the evolution. -/
def Closed (F : ℕ → V →ₗ[K] V) (U : ℕ → Submodule K V) : Prop :=
  ∀ j, ∀ x ∈ U j, F (j + 1) x ∈ U (j + 1)

theorem run_single_lt (F : ℕ → V →ₗ[K] V) (j : ℕ) (u : V) :
    ∀ i < j, run F (fun i => if i = j then u else 0) i = 0 := by
  intro i
  induction i with
  | zero => intro h; simp [run, Nat.pos_iff_ne_zero.1 h |>.symm]
  | succ i ih =>
    intro h
    simp only [run]
    rw [ih (by omega), map_zero, zero_add, if_neg (by omega)]

theorem run_single_eq (F : ℕ → V →ₗ[K] V) (j : ℕ) (u : V) :
    run F (fun i => if i = j then u else 0) j = u := by
  cases j with
  | zero => simp [run]
  | succ j =>
    simp only [run]
    rw [run_single_lt F (j + 1) u j (by omega), map_zero, zero_add]
    simp

/-- **[L] Exact closure ⟺ invariance.** -/
theorem closed_iff (F : ℕ → V →ₗ[K] V) (U : ℕ → Submodule K V) :
    Closed F U ↔ ∀ D : ℕ → V, (∀ j, D j ∈ U j) → ∀ t, run F D t ∈ U t := by
  constructor
  · intro hC D hD t
    induction t with
    | zero => exact hD 0
    | succ t ih => exact (U (t + 1)).add_mem (hC t _ ih) (hD (t + 1))
  · intro h j x hx
    set D : ℕ → V := fun i => if i = j then x else 0 with hDdef
    have hD : ∀ i, D i ∈ U i := by
      intro i
      by_cases hi : i = j
      · subst hi; simp [hDdef, hx]
      · simp [hDdef, hi]
    have h1 := h D hD (j + 1)
    simp only [run] at h1
    rw [run_single_eq F j x, show D (j + 1) = 0 by simp [hDdef]] at h1
    simpa using h1

/-- Rank-one write `x ↦ x − φ(x) k`. -/
def rankOne (φ : V →ₗ[K] K) (k : V) : V →ₗ[K] V := LinearMap.id - φ.smulRight k

theorem rankOne_apply (φ : V →ₗ[K] K) (k x : V) : rankOne φ k x = x - φ x • k := by
  simp [rankOne]

/-- **[L] Invariance under a rank-one write**: `x ↦ x − φ(x) k` preserves `U` iff `k ∈ U` or
`U ⊆ ker φ`. -/
theorem rankOne_invariant_iff (φ : V →ₗ[K] K) (k : V) (U : Submodule K V) :
    (∀ x ∈ U, rankOne φ k x ∈ U) ↔ (k ∈ U ∨ ∀ x ∈ U, φ x = 0) := by
  constructor
  · intro h
    by_cases hk : k ∈ U
    · exact Or.inl hk
    · refine Or.inr fun x hx => ?_
      by_contra hφ
      have hdiff : φ x • k ∈ U := by
        have h1 := U.sub_mem hx (h x hx)
        rwa [rankOne_apply, sub_sub_cancel] at h1
      have : k = (φ x)⁻¹ • (φ x • k) := by rw [smul_smul, inv_mul_cancel₀ hφ, one_smul]
      exact hk (this ▸ U.smul_mem _ hdiff)
  · rintro (hk | hφ) x hx
    · rw [rankOne_apply]; exact U.sub_mem hx (U.smul_mem _ hk)
    · rw [rankOne_apply, hφ x hx, zero_smul, sub_zero]; exact hx

/-- Gated writes `x ↦ a (x − φ(x) k)` with `a ≠ 0` have the same invariant subspaces. -/
theorem gated_invariant_iff (a : K) (ha : a ≠ 0) (φ : V →ₗ[K] K) (k : V) (U : Submodule K V) :
    (∀ x ∈ U, a • rankOne φ k x ∈ U) ↔ (k ∈ U ∨ ∀ x ∈ U, φ x = 0) := by
  rw [← rankOne_invariant_iff]
  constructor
  · intro h x hx
    have := U.smul_mem a⁻¹ (h x hx)
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  · intro h x hx; exact U.smul_mem a (h x hx)

/-- **[L] Keys confined to a subspace make it invariant**, whatever the write functionals. -/
theorem keys_in_span_invariant (φ : ℕ → V →ₗ[K] K) (k : ℕ → V) (S : Submodule K V)
    (hk : ∀ j, k j ∈ S) : Closed (fun j => rankOne (φ j) (k j)) (fun _ => S) :=
  fun j x hx => (rankOne_invariant_iff _ _ S).2 (Or.inl (hk (j + 1))) x hx

/-- **[L] Frozen complement**: on vectors annihilated by `φ`, the write acts as the identity, so
a complement annihilated by every write functional never changes. -/
theorem frozen_of_annihilated (φ : V →ₗ[K] K) (k x : V) (hx : φ x = 0) : rankOne φ k x = x := by
  rw [rankOne_apply, hx, zero_smul, sub_zero]

end Abstract

section Matrices

variable {n m : ℕ}

/-- Matrix error recursion. -/
def runM (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (D : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => D 0
  | j + 1 => F (j + 1) *ᵥ runM F D j + D (j + 1)

/-- Reduced coordinates `z_0 = c_0`, `z_{j+1} = T_{j+1} z_j + c_{j+1}`. -/
def reduced (T : ℕ → Matrix (Fin m) (Fin m) ℝ) (c : ℕ → Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => c 0
  | j + 1 => T (j + 1) *ᵥ reduced T c j + c (j + 1)

/-- **[L] Horizon-independent certificate**: closure in coordinates `F_{j+1} B_j = B_{j+1} T_{j+1}`
and defects `D_j = B_j c_j` give `E_t = B_t z_t` for every `t`. -/
theorem error_eq_basis (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (B : ℕ → Matrix (Fin n) (Fin m) ℝ)
    (T : ℕ → Matrix (Fin m) (Fin m) ℝ) (c : ℕ → Fin m → ℝ) (D : ℕ → Fin n → ℝ)
    (hclosed : ∀ j, F (j + 1) * B j = B (j + 1) * T (j + 1)) (hD : ∀ j, D j = B j *ᵥ c j) :
    ∀ t, runM F D t = B t *ᵥ reduced T c t := by
  intro t
  induction t with
  | zero => simp [runM, reduced, hD 0]
  | succ t ih =>
    rw [runM, reduced, ih, hD (t + 1), mulVec_mulVec, hclosed t, ← mulVec_mulVec, ← mulVec_add]

/-- **[L] Every reader is answered exactly from the certificate `(B_t, z_t)`.** -/
theorem reading_eq (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (B : ℕ → Matrix (Fin n) (Fin m) ℝ)
    (T : ℕ → Matrix (Fin m) (Fin m) ℝ) (c : ℕ → Fin m → ℝ) (D : ℕ → Fin n → ℝ)
    (hclosed : ∀ j, F (j + 1) * B j = B (j + 1) * T (j + 1)) (hD : ∀ j, D j = B j *ᵥ c j)
    (q : Fin n → ℝ) (t : ℕ) : q ⬝ᵥ runM F D t = (q ᵥ* B t) ⬝ᵥ reduced T c t := by
  rw [error_eq_basis F B T c D hclosed hD t, dotProduct_mulVec]

/-- **Refuted: per-layer amplification does not compose multiplicatively.** For every `M > 0`,
`F₁ = diag(M, M⁻¹)` amplifies `e₀` by `M`, `F₂ = diag(M⁻¹, M)` amplifies `e₁` by `M`, and
`F₂ F₁ = I`. -/
theorem cancellation_of_gains (M : ℝ) (hM : 0 < M) :
    diagonal ![M, M⁻¹] *ᵥ Pi.single 0 1 = M • Pi.single 0 1 ∧
      diagonal ![M⁻¹, M] *ᵥ Pi.single 1 1 = M • Pi.single 1 1 ∧
      diagonal ![M⁻¹, M] * diagonal ![M, M⁻¹] = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hM0 : M ≠ 0 := hM.ne'
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [mulVec_diagonal]
  · ext i; fin_cases i <;> simp [mulVec_diagonal]
  · rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM0]

/-- **[L] Size**: an invariant certificate with `m` coordinates (`n·m` basis entries plus `m`
coordinates) is smaller than a dense `n × n` state iff `m ≤ n − 1`, at every horizon. -/
theorem invariant_cert_smaller (n m : ℕ) (hn : 1 ≤ n) : n * m + m < n * n ↔ m ≤ n - 1 := by
  constructor
  · intro h
    by_contra hm
    push Not at hm
    have : n ≤ m := by omega
    have := Nat.mul_le_mul_left n this
    omega
  · intro h
    have h1 : n * m + m = (n + 1) * m := by ring
    have h2 : (n + 1) * m ≤ (n + 1) * (n - 1) := Nat.mul_le_mul_left _ h
    have h3 : (n + 1) * (n - 1) < n * n := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith
    omega

end Matrices

end InvariantErrorSubspaces

import Mathlib

/-!
# Recovery of late linear readers

An affine history splits into a stored prefix state and a replayable suffix.
Linear projections commute with replay when their per-step simulations commute.
A separate transport law accounts for the debt of omitting the prefix state.
-/

namespace LateReaderRecovery

section Algebra

variable {R V W : Type*} [Semiring R] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- A linear action with an additive write. -/
abbrev Step (R V : Type*) [Semiring R] [AddCommGroup V] [Module R V] :=
  (V →ₗ[R] V) × V

def replay (history : List (Step R V)) (initial : V) : V :=
  history.foldl (fun state action => action.1 state + action.2) initial

def transport (history : List (Step R V)) (initialError : V) : V :=
  history.foldl (fun err action => action.1 err) initialError

theorem replay_append (past tail : List (Step R V)) (initial : V) :
    replay (past ++ tail) initial = replay tail (replay past initial) := by
  simp only [replay, List.foldl_append]

theorem replay_add_error (history : List (Step R V)) (initial err : V) :
    replay history (initial + err) = replay history initial + transport history err := by
  induction history generalizing initial err with
  | nil => rfl
  | cons action rest ih =>
    change replay rest (action.1 (initial + err) + action.2) =
      replay rest (action.1 initial + action.2) + transport rest (action.1 err)
    rw [map_add, add_right_comm (action.1 initial) (action.1 err), ih]

/-- A step simulation for a projection gives a simulation for the whole suffix. -/
theorem replay_project (p : V →ₗ[R] W) (adapt : Step R V → Step R W)
    (history : List (Step R V))
    (commutes : ∀ action ∈ history, ∀ x : V,
      p (action.1 x + action.2) = (adapt action).1 (p x) + (adapt action).2)
    (initial : V) :
    p (replay history initial) = replay (history.map adapt) (p initial) := by
  induction history generalizing initial with
  | nil => rfl
  | cons action rest ih =>
    change p (replay rest (action.1 initial + action.2)) =
      replay (rest.map adapt) ((adapt action).1 (p initial) + (adapt action).2)
    rw [ih (fun b hb => commutes b (List.mem_cons_of_mem _ hb)), commutes action (by simp)]

/-- A valid projected checkpoint and the suffix give the exact projected state. -/
theorem checkpoint_recovery (p : V →ₗ[R] W) (adapt : Step R V → Step R W)
    (past tail : List (Step R V))
    (commutes : ∀ action ∈ tail, ∀ x : V,
      p (action.1 x + action.2) = (adapt action).1 (p x) + (adapt action).2)
    (initial : V) (checkpoint : W)
    (valid : checkpoint = p (replay past initial)) :
    p (replay (past ++ tail) initial) = replay (tail.map adapt) checkpoint := by
  rw [replay_append, replay_project p adapt tail commutes, ← valid]

/-- For arbitrary prefix states, a suffix-only exact read is possible precisely when the reader
annihilates the transported prefix error. -/
theorem suffix_only_exact_iff (tail : List (Step R V)) (read : V →ₗ[R] W) :
    (∀ x : V, read (replay tail x) = read (replay tail 0)) ↔
      ∀ x : V, read (transport tail x) = 0 := by
  have split (x : V) : read (replay tail x) = read (replay tail 0) + read (transport tail x) := by
    rw [← map_add, ← replay_add_error, zero_add]
  constructor
  · intro h x
    have h' := (split x).symm.trans (h x)
    exact add_left_cancel (h'.trans (add_zero _).symm)
  · intro h x
    rw [split, h, add_zero]

end Algebra

section Matrix

variable {R I J : Type*} [Semiring R] [Fintype I]

/-- A left affine matrix action can be simulated using any single selected column. -/
theorem matrix_column_step (F : Matrix I I R) (S D : Matrix I J R) (j : J) :
    (fun i => (F * S + D) i j) = F.mulVec (fun i => S i j) + fun i => D i j := by
  funext i
  rfl

/-- Concrete checkpoint contract for any column of a history of left matrix actions. -/
theorem matrix_checkpoint_recovery
    (past tail : List (Matrix I I R × Matrix I J R)) (initial : Matrix I J R) (j : J)
    (checkpoint : I → R)
    (valid : checkpoint = fun i => (past.foldl (fun state a => a.1 * state + a.2) initial) i j) :
    (fun i => ((past ++ tail).foldl (fun state a => a.1 * state + a.2) initial) i j) =
      tail.foldl (fun state a => a.1.mulVec state + fun i => a.2 i j) checkpoint := by
  rw [List.foldl_append, valid]
  let atCut := past.foldl (fun state a => a.1 * state + a.2) initial
  change (fun i => (tail.foldl (fun state a => a.1 * state + a.2) atCut) i j) =
    tail.foldl (fun state a => a.1.mulVec state + fun i => a.2 i j) (fun i => atCut i j)
  clear valid checkpoint
  generalize atCut = state
  clear atCut
  induction tail generalizing state with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [ih, matrix_column_step]

end Matrix

section Bounds

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

def gain (rate : Step ℝ V → ℝ) (history : List (Step ℝ V)) : ℝ :=
  (history.map rate).prod

def envelope (rate injection : Step ℝ V → ℝ) (history : List (Step ℝ V)) (b : ℝ) : ℝ :=
  history.foldl (fun bound action => rate action * bound + injection action) b

theorem gain_nonneg (rate : Step ℝ V → ℝ) (h : List (Step ℝ V))
    (nonneg : ∀ a ∈ h, 0 ≤ rate a) : 0 ≤ gain rate h := by
  apply List.prod_nonneg
  intro found hf
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
  exact nonneg a ha

/-- Propagating the omitted initial state costs the product of the local gains. -/
theorem transport_norm_le (rate : Step ℝ V → ℝ) (h : List (Step ℝ V))
    (bounds : ∀ a ∈ h, 0 ≤ rate a ∧ ∀ x : V, ‖a.1 x‖ ≤ rate a * ‖x‖) (e : V) :
    ‖transport h e‖ ≤ gain rate h * ‖e‖ := by
  induction h generalizing e with
  | nil => simp [transport, gain]
  | cons a rest ih =>
    have ha := bounds a (by simp)
    have hr (c : Step ℝ V) (hc : c ∈ rest) := bounds c (List.mem_cons_of_mem _ hc)
    have hp := gain_nonneg rate rest (fun c hc => (hr c hc).1)
    change ‖transport rest (a.1 e)‖ ≤ (rate a * gain rate rest) * ‖e‖
    calc
      _ ≤ gain rate rest * ‖a.1 e‖ := ih hr _
      _ ≤ gain rate rest * (rate a * ‖e‖) := mul_le_mul_of_nonneg_left (ha.2 e) hp
      _ = _ := by ring

/-- A scalar causal envelope upper-bounds the norm of the current state. -/
theorem replay_norm_le_envelope (rate injection : Step ℝ V → ℝ) (h : List (Step ℝ V))
    (bounds : ∀ a ∈ h, 0 ≤ rate a ∧ (∀ x : V, ‖a.1 x‖ ≤ rate a * ‖x‖) ∧ ‖a.2‖ ≤ injection a)
    (initial : V) (b : ℝ) (initial_bound : ‖initial‖ ≤ b) :
    ‖replay h initial‖ ≤ envelope rate injection h b := by
  induction h generalizing initial b with
  | nil => exact initial_bound
  | cons a rest ih =>
    have ha := bounds a (by simp)
    have hr (c : Step ℝ V) (hc : c ∈ rest) := bounds c (List.mem_cons_of_mem _ hc)
    change ‖replay rest (a.1 initial + a.2)‖ ≤
      envelope rate injection rest (rate a * b + injection a)
    apply ih hr
    calc
      _ ≤ ‖a.1 initial‖ + ‖a.2‖ := norm_add_le _ _
      _ ≤ rate a * b + injection a := add_le_add
        ((ha.2.1 initial).trans (mul_le_mul_of_nonneg_left initial_bound ha.1)) ha.2.2

/-- A computed step adds its local defect to the contracted incoming error. -/
theorem one_step_numerical_error (a : Step ℝ V) (center exact next : V) {rate noise : ℝ}
    (h_rate : ∀ x : V, ‖a.1 x‖ ≤ rate * ‖x‖)
    (h_local : ‖next - (a.1 center + a.2)‖ ≤ noise) :
    ‖next - (a.1 exact + a.2)‖ ≤ rate * ‖center - exact‖ + noise := by
  have split : next - (a.1 exact + a.2) =
      (next - (a.1 center + a.2)) + a.1 (center - exact) := by
    rw [map_sub]
    abel
  rw [split, add_comm (rate * ‖center - exact‖)]
  exact (norm_add_le _ _).trans (add_le_add h_local (h_rate _))

def replayWithDebt (advance : Step ℝ V → V → V) (rate : Step ℝ V → ℝ)
    (localError : Step ℝ V → V → ℝ) (history : List (Step ℝ V)) (initial : V × ℝ) : V × ℝ :=
  history.foldl (fun state action =>
    (advance action state.1, rate action * state.2 + localError action state.1)) initial

/-- The accumulated debt bounds the trajectory error whenever each step's local error test
and gain are valid. In particular the initial debt need not be zero. -/
theorem replayWithDebt_sound (advance : Step ℝ V → V → V) (rate : Step ℝ V → ℝ)
    (localError : Step ℝ V → V → ℝ) (history : List (Step ℝ V))
    (gain_bounds : ∀ a ∈ history, 0 ≤ rate a ∧ ∀ x : V, ‖a.1 x‖ ≤ rate a * ‖x‖)
    (local_bounds : ∀ a ∈ history, ∀ x : V, ‖advance a x - (a.1 x + a.2)‖ ≤ localError a x)
    (center initial : V) (b : ℝ) (initial_bound : ‖center - initial‖ ≤ b) :
    ‖(replayWithDebt advance rate localError history (center, b)).1 - replay history initial‖ ≤
      (replayWithDebt advance rate localError history (center, b)).2 := by
  induction history generalizing center initial b with
  | nil => exact initial_bound
  | cons a rest ih =>
    have hgain := gain_bounds a (by simp)
    have hlocal := local_bounds a (by simp) center
    apply ih (fun c hc => gain_bounds c (List.mem_cons_of_mem _ hc))
      (fun c hc => local_bounds c (List.mem_cons_of_mem _ hc))
    exact (one_step_numerical_error a center initial (advance a center) hgain.2 hlocal).trans
      (add_le_add (mul_le_mul_of_nonneg_left initial_bound hgain.1) le_rfl)

/-- The missing prefix and a numerical approximation of the zero-start suffix give separate
terms in the late-read error bound. The numerical error must be supplied. -/
theorem late_read_error_le (rate : Step ℝ V → ℝ) (past tail : List (Step ℝ V))
    (bounds : ∀ a ∈ tail, 0 ≤ rate a ∧ ∀ x : V, ‖a.1 x‖ ≤ rate a * ‖x‖)
    (initial : V) (read : V →ₗ[ℝ] ℝ) {b l eta answer : ℝ}
    (prepaid : ‖replay past initial‖ ≤ b)
    (reader_nonneg : 0 ≤ l) (reader_bound : ∀ x, ‖read x‖ ≤ l * ‖x‖)
    (numerical : ‖answer - read (replay tail 0)‖ ≤ eta) :
    ‖answer - read (replay (past ++ tail) initial)‖ ≤ eta + l * gain rate tail * b := by
  have decompose : read (replay (past ++ tail) initial) =
      read (replay tail 0) + read (transport tail (replay past initial)) := by
    rw [replay_append, ← map_add, ← replay_add_error, zero_add]
  have hgain := gain_nonneg rate tail (fun a ha => (bounds a ha).1)
  have hlinear : ‖read (transport tail (replay past initial))‖ ≤ l * gain rate tail * b := by
    calc
      _ ≤ l * ‖transport tail (replay past initial)‖ := reader_bound _
      _ ≤ l * (gain rate tail * ‖replay past initial‖) :=
        mul_le_mul_of_nonneg_left (transport_norm_le rate tail bounds _) reader_nonneg
      _ = l * gain rate tail * ‖replay past initial‖ := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left prepaid (mul_nonneg reader_nonneg hgain)
  rw [decompose, sub_add_eq_sub_sub]
  exact (norm_sub_le _ _).trans (add_le_add numerical hlinear)

end Bounds

section RankOne

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The rank-one gated transition is contractive up to the scalar gate if the rank-one
eigenvalue lies in the interval `[-1, 1]`. -/
theorem rank_one_norm_le (a β : ℝ) (key x : V) (beta_nonneg : 0 ≤ β)
    (key_bound : β * ‖key‖ ^ 2 ≤ 2) :
    ‖a • (x - (β * ⟪key, x⟫_ℝ) • key)‖ ≤ |a| * ‖x‖ := by
  have hexpand : ‖x - (β * ⟪key, x⟫_ℝ) • key‖ ^ 2 =
      ‖x‖ ^ 2 - β * (2 - β * ‖key‖ ^ 2) * ⟪key, x⟫_ℝ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_comm x key]
    ring
  have hterm := mul_nonneg (mul_nonneg beta_nonneg (sub_nonneg.mpr key_bound))
    (sq_nonneg ⟪key, x⟫_ℝ)
  have hplain : ‖x - (β * ⟪key, x⟫_ℝ) • key‖ ≤ ‖x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith only [hexpand, hterm])
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hplain (abs_nonneg a)

end RankOne

end LateReaderRecovery

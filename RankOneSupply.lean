import Mathlib

/-! Energy estimates for a scalar input driving a rank-one linear update. -/

namespace RankOneSupply

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- One gated step, written as a multiple of the previous state and a rank-one input. -/
def step (k : V) (a b v : ℝ) (x : V) : V :=
  a • x + (b * (v - a * ⟪k, x⟫_ℝ)) • k

/-- The exact discarded square in the one-step energy inequality. -/
theorem supply_identity (k x : V) (a b v : ℝ) :
    (2 - b * ‖k‖ ^ 2) * (‖step k a b v x‖ ^ 2 - a ^ 2 * ‖x‖ ^ 2) =
      b * v ^ 2 - b * ((2 - b * ‖k‖ ^ 2) * a * ⟪k, x⟫_ℝ -
        (1 - b * ‖k‖ ^ 2) * v) ^ 2 := by
  simp only [step, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm x k]
  ring

/-- Nonnegative inputs to the squared-error budget do not require estimating the current dot product. -/
theorem supply_le (k x : V) (a b v : ℝ) (hb : 0 ≤ b) (hd : 0 < 2 - b * ‖k‖ ^ 2) :
    ‖step k a b v x‖ ^ 2 ≤ a ^ 2 * ‖x‖ ^ 2 + b / (2 - b * ‖k‖ ^ 2) * v ^ 2 := by
  have h := supply_identity k x a b v
  have hsmall := mul_nonneg hb
    (sq_nonneg ((2 - b * ‖k‖ ^ 2) * a * ⟪k, x⟫_ℝ - (1 - b * ‖k‖ ^ 2) * v))
  have hdiv : ‖step k a b v x‖ ^ 2 - a ^ 2 * ‖x‖ ^ 2 ≤ b * v ^ 2 / (2 - b * ‖k‖ ^ 2) := by
    apply (le_div_iff₀ hd).2
    rw [mul_comm, h]
    linarith only [hsmall]
  linarith only [hdiv, show b * v ^ 2 / (2 - b * ‖k‖ ^ 2) =
    b / (2 - b * ‖k‖ ^ 2) * v ^ 2 by ring]

/-- The same dynamics transports a difference of inputs and initial states. -/
theorem step_sub (k x y : V) (a b v w : ℝ) :
    step k a b v x - step k a b w y = step k a b (v - w) (x - y) := by
  simp only [step, inner_sub_right, smul_sub]
  module

theorem step_add (k x y : V) (a b v w : ℝ) :
    step k a b (v + w) (x + y) = step k a b v x + step k a b w y := by
  simp only [step, inner_add_right, smul_add]
  module

theorem step_smul (k x : V) (a b v c : ℝ) :
    step k a b (c * v) (c • x) = c • step k a b v x := by
  simp only [step, real_inner_smul_right, smul_add, smul_smul]
  module

/-- Any finite weighted dictionary of trajectories obeys the same input law. -/
theorem step_dictionary {ι : Type*} (s : Finset ι) (k : V) (a b : ℝ)
    (v c : ι → ℝ) (x : ι → V) :
    step k a b (∑ i ∈ s, c i * v i) (∑ i ∈ s, c i • x i) =
      ∑ i ∈ s, c i • step k a b (v i) (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [step]
  | insert j s hj ih => simp only [Finset.sum_insert hj, step_add, step_smul, ih]

/-- The input residual is exactly the drive of the error against a shared dictionary. -/
theorem dictionary_residual {ι : Type*} (s : Finset ι) (k x : V) (a b u : ℝ)
    (v c : ι → ℝ) (y : ι → V) :
    step k a b u x - ∑ i ∈ s, c i • step k a b (v i) (y i) =
      step k a b (u - ∑ i ∈ s, c i * v i) (x - ∑ i ∈ s, c i • y i) := by
  rw [← step_dictionary, step_sub]

theorem reader_of_sq_budget (q x : V) (e : ℝ) (safe : ‖x‖ ^ 2 ≤ e) :
    |⟪q, x⟫_ℝ| ≤ ‖q‖ * Real.sqrt e := by
  have bound := Real.sqrt_le_sqrt safe
  rw [Real.sqrt_sq (norm_nonneg x)] at bound
  exact (abs_real_inner_le_norm q x).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg q))

structure Kick (V : Type*) where
  key : V
  gate : ℝ
  strength : ℝ
  drive : ℝ

def trajectory (history : List (Kick V)) (x : V) : V :=
  history.foldl (fun y s => step s.key s.gate s.strength s.drive y) x

noncomputable def budget (history : List (Kick V)) (initial : ℝ) : ℝ :=
  history.foldl (fun e s => s.gate ^ 2 * e +
    s.strength / (2 - s.strength * ‖s.key‖ ^ 2) * s.drive ^ 2) initial

theorem trajectory_sq_le_budget (history : List (Kick V)) (x : V) (initial : ℝ)
    (safe : ∀ s ∈ history, 0 ≤ s.strength ∧ 0 < 2 - s.strength * ‖s.key‖ ^ 2)
    (initial_bound : ‖x‖ ^ 2 ≤ initial) :
    ‖trajectory history x‖ ^ 2 ≤ budget history initial := by
  induction history generalizing x initial with
  | nil => exact initial_bound
  | cons act rest ih =>
    have hs := safe act (by simp)
    apply ih _ _ (fun s h => safe s (List.mem_cons_of_mem _ h))
    exact (supply_le act.key x act.gate act.strength act.drive hs.1 hs.2).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left initial_bound (sq_nonneg _)) _)

/-- At the reflection endpoint there is no uniform additive cost for a fixed unit drive.
Here the scalar update has key and gate one and strength two. -/
theorem reflection_endpoint_unbounded (cap : ℝ) :
    ∃ x : ℝ, cap < (-x + 2) ^ 2 - x ^ 2 := by
  refine ⟨-(|cap| + 1), ?_⟩
  nlinarith only [le_abs_self cap, abs_nonneg cap]

end RankOneSupply

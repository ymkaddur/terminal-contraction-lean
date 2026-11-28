import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace FastGramBudget

/-- A write discounts accumulated energy, then adds its own nonnegative budget. -/
def update (value : ℝ) (step : ℝ × ℝ) : ℝ :=
  step.1 * value + step.2

def carriedGain (steps : List (ℝ × ℝ)) : ℝ :=
  (steps.map Prod.fst).prod

def budget (steps : List (ℝ × ℝ)) : ℝ :=
  steps.foldl update 0

theorem fold_eq_affine (steps : List (ℝ × ℝ)) (initial : ℝ) :
    steps.foldl update initial = carriedGain steps * initial + budget steps := by
  induction steps generalizing initial with
  | nil => simp [carriedGain, budget]
  | cons step steps ih =>
    simp only [List.foldl_cons, carriedGain, List.map_cons, List.prod_cons, budget]
    rw [ih (update initial step), ih (update 0 step)]
    simp only [update, carriedGain]
    ring

/-- This is the exact contract for replacing a block by one affine update. -/
theorem merge_blocks (past block : List (ℝ × ℝ)) :
    budget (past ++ block) = carriedGain block * budget past + budget block := by
  unfold budget
  rw [List.foldl_append]
  exact fold_eq_affine block (budget past)

theorem suffix_weight (first : ℝ × ℝ) (rest : List (ℝ × ℝ)) :
    budget (first :: rest) = carriedGain rest * first.2 + budget rest := by
  have h := fold_eq_affine rest (update 0 first)
  simpa [budget, update] using h

theorem budget_consume_upper {energy energyUpper gain gainUpper supply supplyUpper : ℝ}
    (he : energy ≤ energyUpper) (hE : 0 ≤ energyUpper) (hg : 0 ≤ gain)
    (hh : gain ≤ gainUpper) (hs : supply ≤ supplyUpper) :
    update energy (gain, supply) ≤ update energyUpper (gainUpper, supplyUpper) :=
  add_le_add ((mul_le_mul_of_nonneg_left he hg).trans
    (mul_le_mul_of_nonneg_right hh hE)) hs

theorem budget_nonnegative (steps : List (ℝ × ℝ))
    (h : ∀ s ∈ steps, 0 ≤ s.1 ∧ 0 ≤ s.2) (initial : ℝ) (hi : 0 ≤ initial) :
    0 ≤ steps.foldl update initial := by
  induction steps generalizing initial with
  | nil => exact hi
  | cons step rest ih =>
    obtain ⟨hg, hs⟩ := h step (List.mem_cons_self ..)
    exact ih (fun s hm => h s (List.mem_cons_of_mem _ hm)) _
      (add_nonneg (mul_nonneg hg hi) hs)

theorem residual_supply_mono (residue lower upper : ℝ) (h : lower ≤ upper) :
    lower * residue ^ 2 ≤ upper * residue ^ 2 :=
  mul_le_mul_of_nonneg_right h (sq_nonneg residue)

open scoped BigOperators

/-- Direct reader contract, written before constructing sufficient statistics. -/
def readerEnergy {t f : Type*} [Fintype t] [Fintype f]
    (w v : t → ℝ) (z : t → f → ℝ) (c : f → ℝ) : ℝ :=
  ∑ s, w s * (v s - ∑ i, z s i * c i) ^ 2

theorem weighted_gram {t f : Type*} [Fintype t] [Fintype f]
    (w v : t → ℝ) (z : t → f → ℝ) (c : f → ℝ) :
    readerEnergy w v z c =
      (∑ s, w s * v s ^ 2) -
        2 * (∑ i, c i * ∑ s, w s * (z s i * v s)) +
        (∑ i, c i * ∑ j, (∑ s, w s * (z s i * z s j)) * c j) := by
  classical
  have linear :
      (∑ i, c i * ∑ s, w s * (z s i * v s)) =
        ∑ s, w s * v s * ∑ i, z s i * c i := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ s, ∑ i, c i * (w s * (z s i * v s)) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have quadratic :
      (∑ i, c i * ∑ j, (∑ s, w s * (z s i * z s j)) * c j) =
        ∑ s, w s * (∑ i, z s i * c i) ^ 2 := by
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ s, ∑ j, c i * (w s * (z s i * z s j) * c j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ s, ∑ i, ∑ j, c i * (w s * (z s i * z s j) * c j) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
  unfold readerEnergy
  rw [linear, quadratic, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- A roundoff path multiplies by one additional near-unit factor. -/
theorem path_roundoff_step (x delta bound unit : ℝ)
    (hx : |x - 1| ≤ bound) (hd : |delta| ≤ unit) :
    |x * (1 + delta) - 1| ≤ (1 + bound) * (1 + unit) - 1 := by
  have hb : 0 ≤ bound := (abs_nonneg _).trans hx
  have hu : 0 ≤ unit := (abs_nonneg _).trans hd
  calc
    |x * (1 + delta) - 1| = |(x - 1) + (x - 1) * delta + delta| := by ring_nf
    _ ≤ |x - 1| + |(x - 1) * delta| + |delta| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ bound + bound * unit + unit := by
      rw [abs_mul]
      exact add_le_add (add_le_add hx (mul_le_mul hx hd (abs_nonneg _) hb)) hd
    _ = (1 + bound) * (1 + unit) - 1 := by ring

theorem path_roundoff (deltas : List ℝ) (unit : ℝ)
    (h : ∀ δ ∈ deltas, |δ| ≤ unit) :
    |(deltas.map (fun δ => 1 + δ)).prod - 1| ≤ (1 + unit) ^ deltas.length - 1 := by
  induction deltas with
  | nil => simp
  | cons δ rest ih =>
    have hr := ih fun x hm => h x (List.mem_cons_of_mem _ hm)
    have hd := h δ (List.mem_cons_self ..)
    have step := path_roundoff_step _ δ _ _ hr hd
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    convert step using 1 <;> ring_nf

/-- The allowance for a signed quadratic scales with unsigned monomial mass. -/
theorem signed_roundoff {ι : Type*} [Fintype ι] (exactTerm approxTerm : ι → ℝ)
    (bound : ℝ) (h : ∀ i, |approxTerm i - exactTerm i| ≤ bound * |exactTerm i|) :
    |(∑ i, approxTerm i) - ∑ i, exactTerm i| ≤ bound * ∑ i, |exactTerm i| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

/-- A common absolute row envelope suffices to bound the roundoff allowance. -/
theorem absolute_row_mass {t : Type*} [Fintype t] (weight row : t → ℝ) (envelope : ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hr : ∀ s, 0 ≤ row s) (he : ∀ s, row s ≤ envelope) :
    (∑ s, weight s * row s ^ 2) ≤ (∑ s, weight s) * envelope ^ 2 := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hw s)
  simp only [pow_two]
  exact mul_le_mul (he s) (he s) (hr s) ((hr s).trans (he s))

/-- Compose the residual certificate, stored-state debt and demand arithmetic. -/
theorem certified_reader (target ideal stored returned direction residual debt rounding : ℝ)
    (h₁ : |target - ideal| ≤ direction * residual)
    (h₂ : |ideal - stored| ≤ direction * debt)
    (h₃ : |stored - returned| ≤ rounding) :
    |target - returned| ≤ direction * (residual + debt) + rounding := by
  calc
    |target - returned| = |(target - ideal) + (ideal - stored) + (stored - returned)| := by
      ring_nf
    _ ≤ |target - ideal| + |ideal - stored| + |stored - returned| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ direction * residual + direction * debt + rounding :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = direction * (residual + debt) + rounding := by ring

end FastGramBudget

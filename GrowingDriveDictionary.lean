import RankOneSupply

/-! Residual supply estimates for causal additions and restarts of a finite dictionary. -/

namespace GrowingDriveDictionary

open RankOneSupply

variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A channel driven by zero before its birth has an identically zero prefix state. -/
theorem zero_prefix (h : List (Kick V)) (zero : ∀ s ∈ h, s.drive = 0) :
    trajectory h (0 : V) = 0 := by
  induction h with
  | nil => rfl
  | cons a rest ih =>
    change trajectory rest (step a.key a.gate a.strength a.drive 0) = 0
    rw [zero a (by simp)]
    simpa [step] using ih (fun s hs => zero s (List.mem_cons_of_mem _ hs))

/-- Adding channels with zero initial state preserves the existing reconstruction. -/
theorem extend_by_zero (old live : Finset ι) (sub : old ⊆ live) (c : ι → ℝ) (y : ι → V)
    (birth : ∀ i ∈ live, i ∉ old → y i = 0) :
    ∑ i ∈ live, c i • y i = ∑ i ∈ old, c i • y i := by
  classical
  exact (Finset.sum_subset sub (fun i hi hn => by rw [birth i hi hn, smul_zero])).symm

/-- New channels participate in the present input. Only the old channels carry prefix state. -/
theorem growth_certificate (old live : Finset ι) (sub : old ⊆ live) (k x : V)
    (a b v e : ℝ) (c z : ι → ℝ) (y : ι → V) (hb : 0 ≤ b) (hd : 0 < 2 - b * ‖k‖ ^ 2)
    (birth : ∀ i ∈ live, i ∉ old → y i = 0)
    (bound : ‖x - ∑ i ∈ old, c i • y i‖ ^ 2 ≤ e) :
    ‖step k a b v x - ∑ i ∈ live, c i • step k a b (z i) (y i)‖ ^ 2 ≤
      a ^ 2 * e + b / (2 - b * ‖k‖ ^ 2) * (v - ∑ i ∈ live, c i * z i) ^ 2 := by
  rw [dictionary_residual, extend_by_zero old live sub c y birth]
  exact (supply_le _ _ _ _ _ hb hd).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left bound (sq_nonneg _)) _)

/-- If the extended dictionary exactly supplies the present drive, only contracted old debt remains. -/
theorem exact_new_drive (old live : Finset ι) (sub : old ⊆ live) (k x : V)
    (a b v e : ℝ) (c z : ι → ℝ) (y : ι → V) (hb : 0 ≤ b) (hd : 0 < 2 - b * ‖k‖ ^ 2)
    (birth : ∀ i ∈ live, i ∉ old → y i = 0)
    (bound : ‖x - ∑ i ∈ old, c i • y i‖ ^ 2 ≤ e)
    (drive : v = ∑ i ∈ live, c i * z i) :
    ‖step k a b v x - ∑ i ∈ live, c i • step k a b (z i) (y i)‖ ^ 2 ≤ a ^ 2 * e := by
  have h := growth_certificate old live sub k x a b v e c z y hb hd birth bound
  simpa only [← drive, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h

/-- At a full restart the squared norm of the true prefix is a valid incoming debt. -/
theorem restart_certificate (live : Finset ι) (k x : V) (a b v e : ℝ)
    (c z : ι → ℝ) (hb : 0 ≤ b) (hd : 0 < 2 - b * ‖k‖ ^ 2) (initial_bound : ‖x‖ ^ 2 ≤ e) :
    ‖step k a b v x - ∑ i ∈ live, c i • step k a b (z i) (0 : V)‖ ^ 2 ≤
      a ^ 2 * e + b / (2 - b * ‖k‖ ^ 2) * (v - ∑ i ∈ live, c i * z i) ^ 2 := by
  exact growth_certificate ∅ live (Finset.empty_subset _) k x a b v e c z (fun _ => 0) hb hd
    (fun _ _ _ => rfl) (by simpa using initial_bound)

/-- A newly born channel with the correct current drive cannot erase an arbitrary past error. -/
theorem prefix_debt_persists :
    ‖step (1 : ℝ) 1 0 0 1 - step (1 : ℝ) 1 0 0 0‖ = 1 := by
  simp [step]

end GrowingDriveDictionary

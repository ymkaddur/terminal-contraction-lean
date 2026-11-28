import BilateralCertificates

namespace FiberMessagePins

/-- Receiver behavior stated using indistinguishability alone. -/
def Separates {X O M Y : Type*} (side : X → O) (send : X → M) (want : X → Y) : Prop :=
  ∀ x y, side x = side y → send x = send y → want x = want y

theorem decoder_iff_separates {X O M Y : Type*} [Nonempty Y]
    (side : X → O) (send : X → M) (want : X → Y) :
    (∃ dec : O → M → Y, ∀ x, dec (side x) (send x) = want x) ↔ Separates side send want := by
  classical
  constructor
  · rintro ⟨dec, h⟩ x y hs hm
    rw [← h x, ← h y, hs, hm]
  · intro h
    let dec (o : O) (m : M) : Y :=
      if ex : ∃ x, side x = o ∧ send x = m then want ex.choose else Classical.ofNonempty
    refine ⟨dec, fun x => ?_⟩
    have ex : ∃ y, side y = side x ∧ send y = send x := ⟨x,rfl,rfl⟩
    simpa only [dec, dif_pos ex] using h ex.choose x ex.choose_spec.1 ex.choose_spec.2

/-- The least alphabet size for classification on fibers, including arbitrary labels. -/
theorem residual_alphabet {K : Type*} [Field K] [Fintype K] {r w n k d : ℕ}
    (F : Matrix (Fin r) (Fin w) K) (J : Matrix (Fin w) (Fin r) K)
    (P : Matrix (Fin d) (Fin n) K) (C : Matrix (Fin n) (Fin d) K)
    (B : Matrix (Fin n) (Fin k) K) (hF : F*J=1) (hC : P*C=1) (hB : P*B=0) :
    IsLeast {a : ℕ | ∃ label : Matrix (Fin w) (Fin n) K → Fin a,
      Separates (fun s => s*B) label (fun s => F*s*C)} (Fintype.card K ^ (r*d)) := by
  classical
  have hcard : Fintype.card (Matrix (Fin r) (Fin d) K) = Fintype.card K ^ (r*d) := by
    change Fintype.card (Fin r → Fin d → K) = _
    simp only [Fintype.card_fun,Fintype.card_fin, ← pow_mul, Nat.mul_comm d r]
  constructor
  · let e := Fintype.equivFinOfCardEq hcard
    exact ⟨fun s => e (F*s*C), fun _ _ _ h => e.injective h⟩
  · rintro a ⟨label,hl⟩
    obtain ⟨dec,hd⟩ := (decoder_iff_separates _ _ _).mpr hl
    simpa [Nat.mul_comm] using
      BilateralCertificates.residual_message_bound F J P C B hF hC hB label dec hd

end FiberMessagePins

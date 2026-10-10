module
public import proofs.ReverseRateLimits.SourceBounds
public import proofs.ReverseRateLimits.TimeComparison

@[expose] public section

namespace ReverseRateLimits.SourceBounds

noncomputable def Parameters.p (P : Parameters) : ℝ := P.u * P.h

theorem Parameters.p_pos (P : Parameters) : 0 < P.p := mul_pos P.hu.1 P.hh.1

end ReverseRateLimits.SourceBounds

namespace ReverseRateLimits.CorridorDynamics
open Set CoupledSource SourceBounds

/-- Only the three exact ODE equations are fields. Region membership,
convergence, invariance, and capture are conclusions proved below. -/
structure Trajectory (P : Parameters) where
  A : ℝ → ℝ
  B : ℝ → ℝ
  Q : ℝ → ℝ
  dA : ∀ t, 0 ≤ t → HasDerivAt A (P.p^2 * RA P.r P.h P.u (Q t) (A t) (B t)) t
  dB : ∀ t, 0 ≤ t → HasDerivAt B (P.p^2 * P.h^3 * (Q t)^3 *
    RB P.r P.h P.u (Q t) (A t) (B t)) t
  dQ : ∀ t, 0 ≤ t → HasDerivAt Q (qdot P.r P.p P.h (Q t) (A t) (B t)) t

def Outer (A B Q : ℝ) : Prop :=
  (3 ≤ A ∧ A ≤ 5) ∧ (1 ≤ B ∧ B ≤ 3) ∧ ((1/4:ℝ) ≤ Q ∧ Q ≤ 1)

def Inner (A B Q : ℝ) : Prop :=
  ((7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ)) ∧
  ((3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ)) ∧ ((1/2:ℝ) ≤ Q ∧ Q ≤ (3/4:ℝ))

noncomputable def margins (A B Q : ℝ) : Fin 6 → ℝ :=
  ![A-3,5-A,B-1,3-B,Q-(1/4:ℝ),1-Q]

theorem margins_nonneg (A B Q : ℝ) :
    (∀ i, 0 ≤ margins A B Q i) ↔ Outer A B Q := by
  simp only [Outer,margins,Fin.forall_fin_succ,Fin.forall_fin_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, sub_nonneg]
  tauto

/-- All six faces are checked simultaneously, including corner ties. -/
theorem outer_invariant (P : Parameters) (v : Trajectory P)
    (hinit : Outer (v.A 0) (v.B 0) (v.Q 0)) :
    ∀ t, 0 ≤ t → Outer (v.A t) (v.B t) (v.Q t) := by
  intro t ht
  let f : Fin 6 → ℝ → ℝ := fun i s => margins (v.A s) (v.B s) (v.Q s) i
  have hc : ∀ i, ContinuousOn (f i) (Icc 0 t) := by
    intro i s hs
    fin_cases i <;> dsimp only [f,margins]
    · exact ((v.dA s hs.1).sub_const 3).continuousAt.continuousWithinAt
    · exact ((v.dA s hs.1).const_sub 5).continuousAt.continuousWithinAt
    · exact ((v.dB s hs.1).sub_const 1).continuousAt.continuousWithinAt
    · exact ((v.dB s hs.1).const_sub 3).continuousAt.continuousWithinAt
    · exact ((v.dQ s hs.1).sub_const (1/4:ℝ)).continuousAt.continuousWithinAt
    · exact ((v.dQ s hs.1).const_sub 1).continuousAt.continuousWithinAt
  have hd : ∀ i, ∃ d, HasDerivAt (f i) d 0 := by
    intro i
    fin_cases i <;> dsimp only [f,margins]
    · exact ⟨_, (v.dA 0 le_rfl).sub_const 3⟩
    · exact ⟨_, (v.dA 0 le_rfl).const_sub 5⟩
    · exact ⟨_, (v.dB 0 le_rfl).sub_const 1⟩
    · exact ⟨_, (v.dB 0 le_rfl).const_sub 3⟩
    · exact ⟨_, (v.dQ 0 le_rfl).sub_const (1/4:ℝ)⟩
    · exact ⟨_, (v.dQ 0 le_rfl).const_sub 1⟩
  have hp2 : 0 < P.p^2 := pow_pos P.p_pos 2
  have hh3 : 0 < P.h^3 := pow_pos P.hh.1 3
  have hh7 : 0 < P.h^7 := pow_pos P.hh.1 7
  have hin : ∀ s ∈ Icc 0 t, (∀ i, 0 ≤ f i s) → ∀ i, f i s = 0 →
      ∃ d, HasDerivAt (f i) d s ∧ 0 < d := by
    intro s hs hall i hi
    have ho := (margins_nonneg (v.A s) (v.B s) (v.Q s)).mp hall
    have hQp : 0 < v.Q s := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4) ho.2.2.1
    have hbpos : 0 < P.p^2 * P.h^3 * (v.Q s)^3 :=
      mul_pos (mul_pos hp2 hh3) (pow_pos hQp 3)
    have hqpos : 0 < (13/2:ℝ)*P.p^2*P.h^7*(v.Q s)^2 := by positivity
    fin_cases i <;> norm_num [f,margins] at hi
    · have hsign := outer_A_lo P (v.Q s) (v.A s) (v.B s) ho.2.2
        (by constructor <;> linarith) ho.2.1
      exact ⟨_, (v.dA s hs.1).sub_const 3, mul_pos hp2 hsign⟩
    · have hsign := outer_A_hi P (v.Q s) (v.A s) (v.B s) ho.2.2
        (by constructor <;> linarith) ho.2.1
      exact ⟨_, (v.dA s hs.1).const_sub 5, neg_pos.mpr (mul_neg_of_pos_of_neg hp2 hsign)⟩
    · have hsign := outer_B_lo P (v.Q s) (v.A s) (v.B s) ho.2.2 ho.1
        (by constructor <;> linarith)
      exact ⟨_, (v.dB s hs.1).sub_const 1, mul_pos hbpos hsign⟩
    · have hsign := outer_B_hi P (v.Q s) (v.A s) (v.B s) ho.2.2 ho.1
        (by constructor <;> linarith)
      exact ⟨_, (v.dB s hs.1).const_sub 3, neg_pos.mpr (mul_neg_of_pos_of_neg hbpos hsign)⟩
    · have hsign := outer_Q_lo P (v.Q s) (v.A s) (v.B s)
        (by constructor <;> linarith) ho.1 ho.2.1
      exact ⟨_, (v.dQ s hs.1).sub_const (1/4:ℝ), mul_pos hqpos hsign⟩
    · have hsign := outer_Q_hi P (v.Q s) (v.A s) (v.B s)
        (by constructor <;> linarith) ho.1 ho.2.1
      exact ⟨_, (v.dQ s hs.1).const_sub 1, neg_pos.mpr (mul_neg_of_pos_of_neg hqpos hsign)⟩
  exact (margins_nonneg (v.A t) (v.B t) (v.Q t)).mp
    (closed_box_invariance f 0 t ht hc ((margins_nonneg _ _ _).mpr hinit) hd hin
      t ⟨ht,le_rfl⟩)

noncomputable def tA (P : Parameters) : ℝ := 2/P.p^2
noncomputable def tB (P : Parameters) : ℝ := tA P + 32/(P.p^2*P.h^3)
noncomputable def tQ (P : Parameters) : ℝ := tB P + 80/(13*P.p^2*P.h^7)

theorem entry_A (P : Parameters) (v : Trajectory P)
    (hinit : Outer (v.A 0) (v.B 0) (v.Q 0)) :
    ∀ t, tA P ≤ t → (7/2:ℝ) ≤ v.A t ∧ v.A t ≤ (9/2:ℝ) := by
  intro t ht
  have hp2 : 0 < P.p^2 := pow_pos P.p_pos 2
  have htime0 : 0 ≤ tA P := by unfold tA; positivity
  have ht0 := htime0.trans ht
  have ho := outer_invariant P v hinit
  have hδ : 0 < P.p^2/4 := by positivity
  have heq : ((7/2:ℝ)-3)/(P.p^2/4) = tA P := by
    unfold tA; field_simp; ring
  have heq' : (5-(9/2:ℝ))/(P.p^2/4) = tA P := by
    unfold tA; field_simp; ring
  constructor
  · apply lower_entry v.A (fun s => P.p^2*RA P.r P.h P.u (v.Q s) (v.A s) (v.B s))
      3 (7/2:ℝ) (P.p^2/4) 0 t hδ ht0
      (by simpa only [heq,sub_zero] using ht)
      (fun s hs => v.dA s hs.1)
      (fun s hs => (ho s hs.1).1.1)
    intro s hs hA
    have houter := ho s hs.1
    have hsign := SourceBounds.entry_A_lo P (v.Q s) (v.A s) (v.B s)
      houter.2.2 ⟨houter.1.1,hA⟩ houter.2.1
    have hm := mul_le_mul_of_nonneg_left hsign hp2.le
    nlinarith only [hm]
  · apply upper_entry v.A (fun s => P.p^2*RA P.r P.h P.u (v.Q s) (v.A s) (v.B s))
      5 (9/2:ℝ) (P.p^2/4) 0 t hδ ht0
      (by simpa only [heq',sub_zero] using ht)
      (fun s hs => v.dA s hs.1)
      (fun s hs => (ho s hs.1).1.2)
    intro s hs hA
    have houter := ho s hs.1
    have hsign := SourceBounds.entry_A_hi P (v.Q s) (v.A s) (v.B s)
      houter.2.2 ⟨hA,houter.1.2⟩ houter.2.1
    have hm := mul_le_mul_of_nonneg_left hsign hp2.le
    nlinarith only [hm]

theorem entry_B (P : Parameters) (v : Trajectory P)
    (hinit : Outer (v.A 0) (v.B 0) (v.Q 0)) :
    ∀ t, tB P ≤ t → (3/2:ℝ) ≤ v.B t ∧ v.B t ≤ (5/2:ℝ) := by
  intro t ht
  have hp2 : 0 < P.p^2 := pow_pos P.p_pos 2
  have hh3 : 0 < P.h^3 := pow_pos P.hh.1 3
  have hcpos : 0 < P.p^2*P.h^3 := mul_pos hp2 hh3
  have hδ : 0 < P.p^2*P.h^3/64 := by positivity
  have hTA0 : 0 ≤ tA P := by unfold tA; positivity
  have hTATB : tA P ≤ tB P := by unfold tB; exact le_add_of_nonneg_right (by positivity)
  have hst := hTATB.trans ht
  have hdeadline : ((3/2:ℝ)-1)/(P.p^2*P.h^3/64) ≤ t-tA P := by
    have heq : ((3/2:ℝ)-1)/(P.p^2*P.h^3/64) = 32/(P.p^2*P.h^3) := by
      field_simp; ring
    rw [heq]
    dsimp [tB] at ht
    linarith
  have hdeadline' : (3-(5/2:ℝ))/(P.p^2*P.h^3/64) ≤ t-tA P := by
    convert hdeadline using 1; norm_num
  have ho := outer_invariant P v hinit
  have hqbound : ∀ s, 0 ≤ s → (1/64:ℝ) ≤ (v.Q s)^3 := by
    intro s hs
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) (ho s hs).2.2.1 3
    norm_num at h
    exact h
  constructor
  · apply lower_entry v.B (fun s => P.p^2*P.h^3*(v.Q s)^3*
        RB P.r P.h P.u (v.Q s) (v.A s) (v.B s))
      1 (3/2:ℝ) (P.p^2*P.h^3/64) (tA P) t hδ hst hdeadline
      (fun s hs => v.dB s (hTA0.trans hs.1))
      (fun s hs => (ho s (hTA0.trans hs.1)).2.1.1)
    intro s hs hB
    have hs0 := hTA0.trans hs.1
    have houter := ho s hs0
    have hsign := SourceBounds.entry_B_lo P (v.Q s) (v.A s) (v.B s)
      houter.2.2 (entry_A P v hinit s hs.1) ⟨houter.2.1.1,hB⟩
    have hfac : P.p^2*P.h^3/64 ≤ P.p^2*P.h^3*(v.Q s)^3 := by
      have hm := mul_le_mul_of_nonneg_left (hqbound s hs0) hcpos.le
      nlinarith only [hm]
    have hm := mul_le_mul_of_nonneg_left hsign
      (mul_nonneg hcpos.le (pow_nonneg (houter.2.2.1.trans' (by norm_num)) 3))
    nlinarith only [hm,hfac]
  · apply upper_entry v.B (fun s => P.p^2*P.h^3*(v.Q s)^3*
        RB P.r P.h P.u (v.Q s) (v.A s) (v.B s))
      3 (5/2:ℝ) (P.p^2*P.h^3/64) (tA P) t hδ hst hdeadline'
      (fun s hs => v.dB s (hTA0.trans hs.1))
      (fun s hs => (ho s (hTA0.trans hs.1)).2.1.2)
    intro s hs hB
    have hs0 := hTA0.trans hs.1
    have houter := ho s hs0
    have hsign := SourceBounds.entry_B_hi P (v.Q s) (v.A s) (v.B s)
      houter.2.2 (entry_A P v hinit s hs.1) ⟨hB,houter.2.1.2⟩
    have hfac : P.p^2*P.h^3/64 ≤ P.p^2*P.h^3*(v.Q s)^3 := by
      have hm := mul_le_mul_of_nonneg_left (hqbound s hs0) hcpos.le
      nlinarith only [hm]
    have hm := mul_le_mul_of_nonneg_left hsign
      (mul_nonneg hcpos.le (pow_nonneg (houter.2.2.1.trans' (by norm_num)) 3))
    nlinarith only [hm,hfac]

theorem entry_Q (P : Parameters) (v : Trajectory P)
    (hinit : Outer (v.A 0) (v.B 0) (v.Q 0)) :
    ∀ t, tQ P ≤ t → (1/2:ℝ) ≤ v.Q t ∧ v.Q t ≤ (3/4:ℝ) := by
  intro t ht
  have hp2 : 0 < P.p^2 := pow_pos P.p_pos 2
  have hh3 : 0 < P.h^3 := pow_pos P.hh.1 3
  have hh7 : 0 < P.h^7 := pow_pos P.hh.1 7
  have hcpos : 0 < (13/2:ℝ)*P.p^2*P.h^7 := by positivity
  have hδ : 0 < (13/320:ℝ)*P.p^2*P.h^7 := by positivity
  have hTA0 : 0 ≤ tA P := by unfold tA; positivity
  have hTATB : tA P ≤ tB P := by unfold tB; exact le_add_of_nonneg_right (by positivity)
  have hTB0 := hTA0.trans hTATB
  have hTBTQ : tB P ≤ tQ P := by unfold tQ; exact le_add_of_nonneg_right (by positivity)
  have hst := hTBTQ.trans ht
  have hdeadline : ((1/2:ℝ)-(1/4:ℝ))/((13/320:ℝ)*P.p^2*P.h^7) ≤ t-tB P := by
    have heq : ((1/2:ℝ)-(1/4:ℝ))/((13/320:ℝ)*P.p^2*P.h^7) =
        80/(13*P.p^2*P.h^7) := by field_simp; ring
    rw [heq]
    dsimp [tQ] at ht
    linarith
  have hdeadline' : (1-(3/4:ℝ))/((13/320:ℝ)*P.p^2*P.h^7) ≤ t-tB P := by
    convert hdeadline using 1; norm_num
  have ho := outer_invariant P v hinit
  have hqbound : ∀ s, 0 ≤ s → (1/16:ℝ) ≤ (v.Q s)^2 := by
    intro s hs
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) (ho s hs).2.2.1 2
    norm_num at h
    exact h
  constructor
  · apply lower_entry v.Q (fun s => qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))
      (1/4:ℝ) (1/2:ℝ) ((13/320:ℝ)*P.p^2*P.h^7) (tB P) t hδ hst hdeadline
      (fun s hs => v.dQ s (hTB0.trans hs.1))
      (fun s hs => (ho s (hTB0.trans hs.1)).2.2.1)
    intro s hs hQ
    have hs0 := hTB0.trans hs.1
    have houter := ho s hs0
    have hsign := SourceBounds.entry_Q_lo P (v.Q s) (v.A s) (v.B s)
      ⟨houter.2.2.1,hQ⟩ (entry_A P v hinit s (hTATB.trans hs.1))
      (entry_B P v hinit s hs.1)
    have hfac := mul_le_mul_of_nonneg_left (hqbound s hs0) hcpos.le
    have hm := mul_le_mul_of_nonneg_left hsign (mul_nonneg hcpos.le (sq_nonneg (v.Q s)))
    dsimp [qdot]
    nlinarith only [hm,hfac]
  · apply upper_entry v.Q (fun s => qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))
      1 (3/4:ℝ) ((13/320:ℝ)*P.p^2*P.h^7) (tB P) t hδ hst hdeadline'
      (fun s hs => v.dQ s (hTB0.trans hs.1))
      (fun s hs => (ho s (hTB0.trans hs.1)).2.2.2)
    intro s hs hQ
    have hs0 := hTB0.trans hs.1
    have houter := ho s hs0
    have hsign := SourceBounds.entry_Q_hi P (v.Q s) (v.A s) (v.B s)
      ⟨hQ,houter.2.2.2⟩ (entry_A P v hinit s (hTATB.trans hs.1))
      (entry_B P v hinit s hs.1)
    have hfac := mul_le_mul_of_nonneg_left (hqbound s hs0) hcpos.le
    have hm := mul_le_mul_of_nonneg_left hsign (mul_nonneg hcpos.le (sq_nonneg (v.Q s)))
    dsimp [qdot]
    nlinarith only [hm,hfac]

theorem recovery (P : Parameters) (v : Trajectory P)
    (hinit : Outer (v.A 0) (v.B 0) (v.Q 0)) :
    ∀ t, tQ P ≤ t → Inner (v.A t) (v.B t) (v.Q t) := by
  intro t ht
  have hp2 : 0 < P.p^2 := pow_pos P.p_pos 2
  have hh3 : 0 < P.h^3 := pow_pos P.hh.1 3
  have hh7 : 0 < P.h^7 := pow_pos P.hh.1 7
  have hTATB : tA P ≤ tB P := by unfold tB; exact le_add_of_nonneg_right (by positivity)
  have hTBTQ : tB P ≤ tQ P := by unfold tQ; exact le_add_of_nonneg_right (by positivity)
  exact ⟨entry_A P v hinit t (hTATB.trans (hTBTQ.trans ht)),
    entry_B P v hinit t (hTBTQ.trans ht), entry_Q P v hinit t ht⟩

end ReverseRateLimits.CorridorDynamics



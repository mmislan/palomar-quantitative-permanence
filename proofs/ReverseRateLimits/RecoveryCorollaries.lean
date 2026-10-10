module
public import proofs.ReverseRateLimits.CoupledTheorem

@[expose] public section

namespace ReverseRateLimits.RecoveryCorollaries
open Set CoupledSource SourceBounds CorridorDynamics PhysicalConnection PhysicalBounds CoupledTheorem
noncomputable section

theorem deadline_seven (P : Parameters) : tQ P ≤ 7/(P.p^2*P.h^7) := by
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hh : P.h ≠ 0 := P.hh.1.ne'
  have hh0 := P.hh.1.le
  have hhsmall : P.h ≤ (1/10:ℝ) := P.hh.2.trans (by norm_num)
  have hh4 : P.h^4 ≤ (1/10000:ℝ) := by
    have h := pow_le_pow_left₀ hh0 hhsmall 4
    norm_num at h
    exact h
  have hh7 : P.h^7 ≤ (1/10000000:ℝ) := by
    have h := pow_le_pow_left₀ hh0 hhsmall 7
    norm_num at h
    exact h
  have heq : tQ P = (2*P.h^7+32*P.h^4+(80/13:ℝ))/(P.p^2*P.h^7) := by
    unfold tQ tB tA
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- Only the upward inventory speed is needed for a restoration lower bound. -/
theorem qdot_upper_seven (P : Parameters) (q a b : ℝ) (ho : Outer a b q) :
    qdot P.r P.p P.h q a b ≤ 7*P.p^2*P.h^7 := by
  obtain ⟨hCl,hCu⟩ := C_bounds P q a b ho
  have hq0 : 0 ≤ q := by linarith [ho.2.2.1]
  have hb0 : 0 ≤ b := by linarith [ho.2.1.1]
  have hC0 : 0 ≤ C P.h q a b := by linarith
  have ha3 : 0 ≤ P.r.a3 := (by norm_num : (0:ℝ) ≤ 99/100).trans P.ha3.1
  have hb3 : 0 ≤ P.r.b3 := (by norm_num : (0:ℝ) ≤ 99/100).trans P.hb3.1
  have hforward : 0 ≤ P.r.a3*a^2*b*q^6 := by positivity
  have hreverse : P.r.b3*(C P.h q a b)^2 ≤ (101/100:ℝ) := by
    calc
      P.r.b3*(C P.h q a b)^2 ≤ (101/100:ℝ)*1^2 := by gcongr; exact P.hb3.2
      _ = (101/100:ℝ) := by norm_num
  have hR : RQ P.r P.h q a b ≤ (101/100:ℝ) := by
    unfold RQ
    linarith
  have hq2 : q^2 ≤ 1 := by simpa using pow_le_pow_left₀ hq0 ho.2.2.2 2
  have hc : 0 ≤ (13/2:ℝ)*P.p^2*P.h^7 := by
    have hh := P.hh.1.le
    positivity
  have h1 := mul_le_mul_of_nonneg_left hR (mul_nonneg hc (sq_nonneg q))
  have h2 := mul_le_mul_of_nonneg_left hq2 hc
  unfold qdot
  nlinarith only [h1,h2,hc]

theorem witness_time_lower (P : Parameters) (v : LiteralTrajectory P)
    (hinit : Outer (A P v 0) (B P v 0) (Q P v 0))
    (hQ0 : Q P v 0 = (1/4:ℝ)) (t : ℝ) (ht : 0 ≤ t) (hQtarget : (1/2:ℝ) ≤ Q P v t) :
    1/(28*P.p^2*P.h^7) ≤ t := by
  have hc : ContinuousOn (Q P v) (Icc 0 t) :=
    fun s hs => (deriv_Q P v s hs.1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (Q P v) (interior (Icc 0 t)) :=
    fun s hs => (deriv_Q P v s (interior_subset hs).1).differentiableAt.differentiableWithinAt
  have hu : ∀ s ∈ interior (Icc 0 t), deriv (Q P v) s ≤ 7*P.p^2*P.h^7 := by
    intro s hs
    have hs0 := (interior_subset hs).1
    rw [(deriv_Q P v s hs0).deriv]
    exact qdot_upper_seven P (Q P v s) (A P v s) (B P v s)
      ((literal_recovery P v hinit).1 s hs0)
  have hdiff := (convex_Icc 0 t).image_sub_le_mul_sub_of_deriv_le hc hd hu
    0 ⟨le_rfl,ht⟩ t ⟨ht,le_rfl⟩ ht
  rw [hQ0,sub_zero] at hdiff
  have hden : 0 < 28*P.p^2*P.h^7 := by
    have hp := P.p_pos
    have hh := P.hh.1
    positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hdiff,hQtarget]

theorem prepared_recovery (P : Parameters) (x0 : Fin 3 → ℝ)
    (hpos : OAI.Problem326.PositiveState x0) (hprepared : Prepared P x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
      ∀ v : LiteralTrajectory P, Starts P x0 v →
        (∀ t, 0 ≤ t →
          ((3/64:ℝ)*P.p*P.h^3 ≤ v.x t ∧ v.x t ≤ 5*P.p*P.h^3) ∧
          ((1/16:ℝ)*P.p*P.h^2 ≤ v.y t ∧ v.y t ≤ 3*P.p*P.h^2) ∧
          ((1/8:ℝ)*P.p*P.h ≤ v.z t ∧ v.z t ≤ P.p*P.h)) ∧
        (∀ t, 7/(P.p^2*P.h^7) ≤ t → Inner (A P v t) (B P v t) (Q P v t)) := by
  refine ⟨(prepared_family P x0 hpos hprepared).1,?_⟩
  intro v hs
  have hcoords := initial_coordinates P x0 v hs
  have hinit : Outer (A P v 0) (B P v 0) (Q P v 0) := by
    rw [hcoords.1,hcoords.2.1,hcoords.2.2]
    exact hprepared
  exact ⟨all_time_coordinate_bounds P v hinit,
    fun t ht => (literal_recovery P v hinit).2 t ((deadline_seven P).trans ht)⟩

theorem improved_witness (P : Parameters) :
    ∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
      ∀ t, 0 ≤ t → Inner (A P v t) (B P v t) (Q P v t) →
        1/(28*P.p^2*P.h^7) ≤ t := by
  obtain ⟨hpos,hprep,hQ⟩ := witness_state P
  obtain ⟨v,hs⟩ := (prepared_recovery P (witnessState P) hpos hprep).1
  have hc := initial_coordinates P (witnessState P) v hs
  have hinit : Outer (A P v 0) (B P v 0) (Q P v 0) := by
    rw [hc.1,hc.2.1,hc.2.2]
    exact hprep
  exact ⟨v,hs,fun t ht hi => witness_time_lower P v hinit (hc.2.2.trans hQ) t ht hi.2.2.1⟩

def sx (P : Parameters) : ℝ := P.p*P.h^3
def sy (P : Parameters) : ℝ := P.p*P.h^2
def sz (P : Parameters) : ℝ := P.p*P.h

theorem scale_tradeoff (P : Parameters) :
    (sy P)^2 = sx P*sz P ∧
      1/(P.p^2*P.h^7) = sy P/(sx P)^3 ∧
      1/(P.p^2*P.h^7) = (sz P)^3/(sy P)^5 := by
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hh : P.h ≠ 0 := P.hh.1.ne'
  unfold sx sy sz
  refine ⟨by ring,?_,?_⟩ <;> field_simp

theorem no_linear_inventory (mx my mz : ℝ)
    (h1 : 2*mx-2*my-mz=0) (h2 : -mx+2*my-2*mz=0)
    (h3 : -2*mx-my+2*mz=0) : mx=0 ∧ my=0 ∧ mz=0 := by
  constructor
  · linarith
  · constructor <;> linarith

end
end ReverseRateLimits.RecoveryCorollaries

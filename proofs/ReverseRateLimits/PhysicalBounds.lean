module
public import proofs.ReverseRateLimits.PhysicalConnection

@[expose] public section

namespace ReverseRateLimits.PhysicalBounds
open Set CoupledSource SourceBounds CorridorDynamics PhysicalConnection

theorem C_bounds (P : Parameters) (Q A B : ℝ) (ho : Outer A B Q) :
    (1/2:ℝ) ≤ C P.h Q A B ∧ C P.h Q A B ≤ 1 := by
  obtain ⟨⟨hA,hAu⟩,⟨hB,hBu⟩,⟨hQ,hQu⟩⟩ := ho
  have hh := P.hh.1.le
  have hQ0 : 0 ≤ Q := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hQ2 : Q^2 ≤ 1 := by simpa using pow_le_pow_left₀ hQ0 hQu 2
  have htermA : 3*P.h^2*A*Q^2 ≤ 15*P.h^2 := by
    calc
      3*P.h^2*A*Q^2 ≤ 3*P.h^2*5*1 := by gcongr
      _ = 15*P.h^2 := by ring
  have htermB : (5/2:ℝ)*P.h*B*Q ≤ (15/2:ℝ)*P.h := by
    calc
      (5/2:ℝ)*P.h*B*Q ≤ (5/2:ℝ)*P.h*3*1 := by gcongr
      _ = (15/2:ℝ)*P.h := by ring
  have hh2 : P.h^2 ≤ (1/360000:ℝ) := by
    have hb := pow_le_pow_left₀ hh P.hh.2 2
    norm_num at hb
    exact hb
  unfold C
  constructor
  · nlinarith [P.hh.2]
  · have hna : 0 ≤ 3*P.h^2*A*Q^2 := by positivity
    have hnb : 0 ≤ (5/2:ℝ)*P.h*B*Q := by positivity
    linarith

theorem coordinate_bounds (P : Parameters) (Q A B : ℝ) (ho : Outer A B Q) :
    ((3/64:ℝ)*P.p*P.h^3 ≤ P.p*P.h^3*A*Q^3 ∧ P.p*P.h^3*A*Q^3 ≤ 5*P.p*P.h^3) ∧
    ((1/16:ℝ)*P.p*P.h^2 ≤ P.p*P.h^2*B*Q^2 ∧ P.p*P.h^2*B*Q^2 ≤ 3*P.p*P.h^2) ∧
    ((1/8:ℝ)*P.p*P.h ≤ P.p*P.h*Q*C P.h Q A B ∧ P.p*P.h*Q*C P.h Q A B ≤ P.p*P.h) := by
  obtain ⟨hCl,hCu⟩ := C_bounds P Q A B ho
  obtain ⟨⟨hA,hAu⟩,⟨hB,hBu⟩,⟨hQ,hQu⟩⟩ := ho
  have hp := P.p_pos.le
  have hh := P.hh.1.le
  have hQ0 : 0 ≤ Q := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hC0 : 0 ≤ C P.h Q A B := by linarith
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · calc
      (3/64:ℝ)*P.p*P.h^3 = P.p*P.h^3*3*(1/4:ℝ)^3 := by ring
      _ ≤ P.p*P.h^3*A*Q^3 := by gcongr
  · calc
      P.p*P.h^3*A*Q^3 ≤ P.p*P.h^3*5*1^3 := by gcongr
      _ = 5*P.p*P.h^3 := by ring
  · calc
      (1/16:ℝ)*P.p*P.h^2 = P.p*P.h^2*1*(1/4:ℝ)^2 := by ring
      _ ≤ P.p*P.h^2*B*Q^2 := by gcongr
  · calc
      P.p*P.h^2*B*Q^2 ≤ P.p*P.h^2*3*1^2 := by gcongr
      _ = 3*P.p*P.h^2 := by ring
  · calc
      (1/8:ℝ)*P.p*P.h = P.p*P.h*(1/4:ℝ)*(1/2:ℝ) := by ring
      _ ≤ P.p*P.h*Q*C P.h Q A B := by gcongr
  · calc
      P.p*P.h*Q*C P.h Q A B ≤ P.p*P.h*1*1 := by gcongr
      _ = P.p*P.h := by ring

theorem all_time_coordinate_bounds (P : Parameters) (v : LiteralTrajectory P)
    (hinit : Outer (A P v 0) (B P v 0) (Q P v 0)) :
    ∀ t, 0 ≤ t →
      ((3/64:ℝ)*P.p*P.h^3 ≤ v.x t ∧ v.x t ≤ 5*P.p*P.h^3) ∧
      ((1/16:ℝ)*P.p*P.h^2 ≤ v.y t ∧ v.y t ≤ 3*P.p*P.h^2) ∧
      ((1/8:ℝ)*P.p*P.h ≤ v.z t ∧ v.z t ≤ P.p*P.h) := by
  intro t ht
  have ho := (literal_recovery P v hinit).1 t ht
  have hb := coordinate_bounds P (Q P v t) (A P v t) (B P v t) ho
  have hr := reconstruction P v t ht
  simpa only [← hr.1,← hr.2.1,← hr.2.2] using hb

theorem total_deadline (P : Parameters) : tQ P ≤ 46/(P.p^2*P.h^7) := by
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hh : P.h ≠ 0 := P.hh.1.ne'
  have hh0 := P.hh.1.le
  have hh1 : P.h ≤ 1 := P.hh.2.trans (by norm_num)
  have hh4 : P.h^4 ≤ 1 := pow_le_one₀ hh0 hh1
  have hh7 : P.h^7 ≤ 1 := pow_le_one₀ hh0 hh1
  have heq : tQ P = (2*P.h^7+32*P.h^4+(80/13:ℝ))/(P.p^2*P.h^7) := by
    unfold tQ tB tA
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

theorem RQ_bounds (P : Parameters) (Q A B : ℝ) (ho : Outer A B Q) :
    -77 ≤ RQ P.r P.h Q A B ∧ RQ P.r P.h Q A B ≤ 77 := by
  obtain ⟨hCl,hCu⟩ := C_bounds P Q A B ho
  obtain ⟨⟨hA,hAu⟩,⟨hB,hBu⟩,⟨hQ,hQu⟩⟩ := ho
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C P.h Q A B := by linarith
  have ha3 : 0 ≤ P.r.a3 := (by norm_num : (0:ℝ) ≤ 99/100).trans P.ha3.1
  have hb3 : 0 ≤ P.r.b3 := (by norm_num : (0:ℝ) ≤ 99/100).trans P.hb3.1
  have hneg : P.r.a3*A^2*B*Q^6 ≤ (303/4:ℝ) := by
    calc
      P.r.a3*A^2*B*Q^6 ≤ (101/100:ℝ)*5^2*3*1^6 := by gcongr; exact P.ha3.2
      _ = (303/4:ℝ) := by norm_num
  have hpos : P.r.b3*(C P.h Q A B)^2 ≤ (101/100:ℝ) := by
    calc
      P.r.b3*(C P.h Q A B)^2 ≤ (101/100:ℝ)*1^2 := by gcongr; exact P.hb3.2
      _ = (101/100:ℝ) := by norm_num
  have hn0 : 0 ≤ P.r.a3*A^2*B*Q^6 := by positivity
  have hp0 : 0 ≤ P.r.b3*(C P.h Q A B)^2 := by positivity
  unfold RQ
  constructor <;> linarith

theorem qdot_bounds (P : Parameters) (Q A B : ℝ) (ho : Outer A B Q) :
    -(501*P.p^2*P.h^7) ≤ qdot P.r P.p P.h Q A B ∧
      qdot P.r P.p P.h Q A B ≤ 501*P.p^2*P.h^7 := by
  have hR := RQ_bounds P Q A B ho
  have hQ := ho.2.2
  have hQ0 : 0 ≤ Q := by linarith [hQ.1]
  have hQ2 : Q^2 ≤ 1 := by simpa using pow_le_pow_left₀ hQ0 hQ.2 2
  have hc : 0 ≤ (13/2:ℝ)*P.p^2*P.h^7 := by
    have hh := P.hh.1.le
    positivity
  have hf : (13/2:ℝ)*P.p^2*P.h^7*Q^2 ≤ (13/2:ℝ)*P.p^2*P.h^7 := by
    have h := mul_le_mul_of_nonneg_left hQ2 hc
    simpa only [mul_one] using h
  have hlo := mul_le_mul_of_nonneg_left hR.1 (mul_nonneg hc (sq_nonneg Q))
  have hhi := mul_le_mul_of_nonneg_left hR.2 (mul_nonneg hc (sq_nonneg Q))
  unfold qdot
  constructor <;> nlinarith only [hlo,hhi,hf,hc]

theorem recovery_time_lower (P : Parameters) (v : LiteralTrajectory P)
    (hinit : Outer (A P v 0) (B P v 0) (Q P v 0))
    (hQ0 : Q P v 0 = (1/4:ℝ)) (t : ℝ) (ht : 0 ≤ t) (hQtarget : (1/2:ℝ) ≤ Q P v t) :
    1/(2004*P.p^2*P.h^7) ≤ t := by
  have hc : ContinuousOn (Q P v) (Icc 0 t) :=
    fun s hs => (deriv_Q P v s hs.1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (Q P v) (interior (Icc 0 t)) :=
    fun s hs => (deriv_Q P v s (interior_subset hs).1).differentiableAt.differentiableWithinAt
  have hu : ∀ s ∈ interior (Icc 0 t), deriv (Q P v) s ≤ 501*P.p^2*P.h^7 := by
    intro s hs
    have hs0 := (interior_subset hs).1
    rw [(deriv_Q P v s hs0).deriv]
    exact (qdot_bounds P (Q P v s) (A P v s) (B P v s)
      ((literal_recovery P v hinit).1 s hs0)).2
  have hdiff := (convex_Icc 0 t).image_sub_le_mul_sub_of_deriv_le hc hd hu
    0 ⟨le_rfl,ht⟩ t ⟨ht,le_rfl⟩ ht
  rw [hQ0,sub_zero] at hdiff
  have hden : 0 < 2004*P.p^2*P.h^7 := by
    have hp := P.p_pos
    have hh := P.hh.1
    positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hdiff,hQtarget]

end ReverseRateLimits.PhysicalBounds

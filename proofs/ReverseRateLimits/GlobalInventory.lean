module
public import proofs.ReverseRateLimits.SharpRecovery
public import proofs.ReverseRateLimits.ReactionExtent

@[expose] public section

/-!
# Global inventory clocks for arbitrary positive seeds

The prepared-basin theorem needs the initial state in the corridor.  The
inventory `W = 6x+5y+2z` nevertheless obeys two-sided differential
inequalities on the *whole* positive orthant, because `z ≤ W/2`, `x ≤ W/6`
and `y ≤ W/5` hold for every positive state:

* `W' = -13 J₃ ≤ 13 b₃ p h⁶ z² ≤ (13/4) b₃ p h⁶ W²`   (restoration capacity),
* `W' ≥ -13 a₃ x² y ≥ -(13/180) a₃ W³`                 (depletion capacity).

Comparing `1/W` and `1/W²` gives seed-dependent necessary times for raising
or lowering the inventory from any positive initial state, with no basin
hypothesis.  Global existence from every positive seed is the attributed
global-solution theorem (`exists_literal_trajectory`).
-/

namespace ReverseRateLimits.GlobalInventory
open Set CoupledSource SourceBounds PhysicalConnection ReactionExtent SharpRecovery
  CoupledTheorem SourceExistence
noncomputable section

theorem inventory_pos (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    0 < inventory P v t := by
  obtain ⟨hx,hy,hz⟩ := v.positive t ht
  unfold inventory
  linarith

theorem rates_pos (P : Parameters) : 0 < P.r.a3 ∧ 0 < P.r.b3 :=
  ⟨(by norm_num : (0:ℝ) < 99/100).trans_le P.ha3.1,
   (by norm_num : (0:ℝ) < 99/100).trans_le P.hb3.1⟩

/-- Restoration capacity on the whole positive orthant. -/
theorem deriv_inventory_upper (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    -13*current3 P v t ≤ (13/4:ℝ)*P.r.b3*P.p*P.h^6*(inventory P v t)^2 := by
  obtain ⟨hx,hy,hz⟩ := v.positive t ht
  obtain ⟨ha3,hb3⟩ := rates_pos P
  have hp := P.p_pos
  have hh := P.hh.1
  have hz2 : 2*v.z t ≤ inventory P v t := by unfold inventory; linarith
  have hforward : 0 ≤ P.r.a3*(v.x t)^2*(v.y t) := by positivity
  have hc : 0 ≤ (13/4:ℝ)*P.r.b3*P.p*P.h^6 := by positivity
  have hsq : (2*v.z t)^2 ≤ (inventory P v t)^2 :=
    pow_le_pow_left₀ (by linarith) hz2 2
  have hm := mul_le_mul_of_nonneg_left hsq hc
  unfold current3 j3
  nlinarith only [hforward,hm,hc]

/-- Depletion capacity on the whole positive orthant. -/
theorem deriv_inventory_lower (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    -((13/180:ℝ)*P.r.a3*(inventory P v t)^3) ≤ -13*current3 P v t := by
  obtain ⟨hx,hy,hz⟩ := v.positive t ht
  obtain ⟨ha3,hb3⟩ := rates_pos P
  have hp := P.p_pos
  have hh := P.hh.1
  have hx6 : 6*v.x t ≤ inventory P v t := by unfold inventory; linarith
  have hy5 : 5*v.y t ≤ inventory P v t := by unfold inventory; linarith
  have hreverse : 0 ≤ P.r.b3*P.p*P.h^6*(v.z t)^2 := by positivity
  have hsq : (6*v.x t)^2 ≤ (inventory P v t)^2 :=
    pow_le_pow_left₀ (by linarith) hx6 2
  have hprod : (6*v.x t)^2*(5*v.y t) ≤ (inventory P v t)^2*(inventory P v t) :=
    mul_le_mul hsq hy5 (by positivity) (by positivity)
  have hc : 0 ≤ (13/180:ℝ)*P.r.a3 := by positivity
  have hm := mul_le_mul_of_nonneg_left hprod hc
  unfold current3 j3
  nlinarith only [hreverse,hm,hc]

def recipW (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ := (inventory P v t)⁻¹
def recipW2 (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  (inventory P v t*inventory P v t)⁻¹

theorem recipW_deriv (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (recipW P v) (-(-13*current3 P v t)/(inventory P v t)^2) t := by
  have h := (deriv_inventory P v t ht).inv (inventory_pos P v t ht).ne'
  exact h

theorem recipW2_deriv (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (recipW2 P v)
      (-((-13*current3 P v t)*inventory P v t+inventory P v t*(-13*current3 P v t))/
        (inventory P v t*inventory P v t)^2) t := by
  have hW := deriv_inventory P v t ht
  have hpos := inventory_pos P v t ht
  have h := (hW.mul hW).inv (mul_pos hpos hpos).ne'
  exact h

/-- Any positive trajectory that raises its inventory from `W₀` to `W₁` needs
time at least `(4/(13 b₃ p h⁶))(1/W₀ - 1/W₁)`. No basin hypothesis. -/
theorem restoration_clock (P : Parameters) (v : LiteralTrajectory P) (T : ℝ) (hT : 0 ≤ T) :
    4/(13*P.r.b3*P.p*P.h^6)*(1/inventory P v 0-1/inventory P v T) ≤ T := by
  obtain ⟨ha3,hb3⟩ := rates_pos P
  have hp := P.p_pos
  have hh := P.hh.1
  have hc : ContinuousOn (recipW P v) (Icc 0 T) :=
    fun s hs => (recipW_deriv P v s hs.1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (recipW P v) (interior (Icc 0 T)) :=
    fun s hs => (recipW_deriv P v s (interior_subset hs).1).differentiableAt.differentiableWithinAt
  have hlow : ∀ s ∈ interior (Icc 0 T),
      -((13/4:ℝ)*P.r.b3*P.p*P.h^6) ≤ deriv (recipW P v) s := by
    intro s hs
    have hs0 := (interior_subset hs).1
    rw [(recipW_deriv P v s hs0).deriv]
    have hWs := inventory_pos P v s hs0
    rw [le_div_iff₀ (pow_pos hWs 2)]
    have hup := deriv_inventory_upper P v s hs0
    nlinarith only [hup]
  have hdiff := (convex_Icc 0 T).mul_sub_le_image_sub_of_le_deriv hc hd hlow
    0 ⟨le_rfl,hT⟩ T ⟨hT,le_rfl⟩ hT
  rw [sub_zero] at hdiff
  have hk : 0 < 13*P.r.b3*P.p*P.h^6 := by positivity
  have hrw : recipW P v T-recipW P v 0 = -(1/inventory P v 0-1/inventory P v T) := by
    unfold recipW
    rw [inv_eq_one_div,inv_eq_one_div]
    ring
  rw [hrw] at hdiff
  have hmul : 4/(13*P.r.b3*P.p*P.h^6)*(1/inventory P v 0-1/inventory P v T) =
      (4/(13*P.r.b3*P.p*P.h^6))*(1/inventory P v 0-1/inventory P v T) := rfl
  rw [hmul]
  have hpos4 : 0 < 4/(13*P.r.b3*P.p*P.h^6) := by positivity
  have hkey : (1/inventory P v 0-1/inventory P v T) ≤ (13/4:ℝ)*P.r.b3*P.p*P.h^6*T := by
    nlinarith only [hdiff]
  calc
    4/(13*P.r.b3*P.p*P.h^6)*(1/inventory P v 0-1/inventory P v T)
        ≤ 4/(13*P.r.b3*P.p*P.h^6)*((13/4:ℝ)*P.r.b3*P.p*P.h^6*T) :=
          mul_le_mul_of_nonneg_left hkey hpos4.le
    _ = T := by field_simp

/-- Any positive trajectory that lowers its inventory from `W₀` to `W₁` needs
time at least `(90/(13 a₃))(1/W₁² - 1/W₀²)`. No basin hypothesis. -/
theorem depletion_clock (P : Parameters) (v : LiteralTrajectory P) (T : ℝ) (hT : 0 ≤ T) :
    90/(13*P.r.a3)*(1/(inventory P v T)^2-1/(inventory P v 0)^2) ≤ T := by
  obtain ⟨ha3,hb3⟩ := rates_pos P
  have hc : ContinuousOn (recipW2 P v) (Icc 0 T) :=
    fun s hs => (recipW2_deriv P v s hs.1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (recipW2 P v) (interior (Icc 0 T)) :=
    fun s hs => (recipW2_deriv P v s (interior_subset hs).1).differentiableAt.differentiableWithinAt
  have hup : ∀ s ∈ interior (Icc 0 T), deriv (recipW2 P v) s ≤ (13/90:ℝ)*P.r.a3 := by
    intro s hs
    have hs0 := (interior_subset hs).1
    rw [(recipW2_deriv P v s hs0).deriv]
    have hWs := inventory_pos P v s hs0
    have hden : 0 < (inventory P v s*inventory P v s)^2 := by positivity
    rw [div_le_iff₀ hden]
    have hlow := deriv_inventory_lower P v s hs0
    have h2W : 0 ≤ 2*inventory P v s := by linarith
    have hm := mul_le_mul_of_nonneg_left hlow h2W
    nlinarith only [hm]
  have hdiff := (convex_Icc 0 T).image_sub_le_mul_sub_of_deriv_le hc hd hup
    0 ⟨le_rfl,hT⟩ T ⟨hT,le_rfl⟩ hT
  rw [sub_zero] at hdiff
  have hrw : recipW2 P v T-recipW2 P v 0 =
      1/(inventory P v T)^2-1/(inventory P v 0)^2 := by
    unfold recipW2
    rw [inv_eq_one_div,inv_eq_one_div]
    ring
  rw [hrw] at hdiff
  have hpos : 0 < 90/(13*P.r.a3) := by positivity
  calc
    90/(13*P.r.a3)*(1/(inventory P v T)^2-1/(inventory P v 0)^2)
        ≤ 90/(13*P.r.a3)*((13/90:ℝ)*P.r.a3*T) := mul_le_mul_of_nonneg_left hdiff hpos.le
    _ = T := by field_simp

/-- Global statement: every positive seed has a global positive trajectory, and
every such trajectory obeys both inventory clocks. -/
theorem global_inventory_clocks (P : Parameters) (x0 : Fin 3 → ℝ)
    (hpos : OAI.Problem326.PositiveState x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
      ∀ v : LiteralTrajectory P, ∀ T, 0 ≤ T →
        4/(13*P.r.b3*P.p*P.h^6)*(1/inventory P v 0-1/inventory P v T) ≤ T ∧
        90/(13*P.r.a3)*(1/(inventory P v T)^2-1/(inventory P v 0)^2) ≤ T :=
  ⟨exists_literal_trajectory P x0 hpos,
    fun v T hT => ⟨restoration_clock P v T hT,depletion_clock P v T hT⟩⟩

/-- The witness bound is the global restoration clock evaluated at
`W₀ = ph/2`, `W₁ = ph`: `(4/(13 b₃)) λ⁻¹ ≥ (400/1313) λ⁻¹`. -/
theorem witness_from_global_clock (P : Parameters) (v : LiteralTrajectory P) (T : ℝ) (hT : 0 ≤ T)
    (h0 : inventory P v 0 = P.p*P.h/2) (hT1 : P.p*P.h ≤ inventory P v T) :
    400/(1313*P.p^2*P.h^7) ≤ T := by
  obtain ⟨ha3,hb3⟩ := rates_pos P
  have hp := P.p_pos
  have hh := P.hh.1
  have hclock := restoration_clock P v T hT
  have hWT := inventory_pos P v T hT
  have hrecip : 1/inventory P v T ≤ 1/(P.p*P.h) :=
    one_div_le_one_div_of_le (by positivity) hT1
  have hgap : 1/(P.p*P.h) ≤ 1/inventory P v 0-1/inventory P v T := by
    rw [h0]
    have : 1/(P.p*P.h/2) = 2/(P.p*P.h) := by field_simp
    rw [this]
    have h2 : 2/(P.p*P.h)-1/(P.p*P.h) = 1/(P.p*P.h) := by ring
    linarith
  have hb3' : P.r.b3 ≤ (101/100:ℝ) := P.hb3.2
  have hpos4 : 0 < 4/(13*P.r.b3*P.p*P.h^6) := by positivity
  have hstep : 4/(13*P.r.b3*P.p*P.h^6)*(1/(P.p*P.h)) ≤ T :=
    (mul_le_mul_of_nonneg_left hgap hpos4.le).trans hclock
  have hval : 4/(13*P.r.b3*P.p*P.h^6)*(1/(P.p*P.h)) = 4/(13*P.r.b3*P.p^2*P.h^7) := by
    field_simp
  rw [hval] at hstep
  have hcmp : 400/(1313*P.p^2*P.h^7) ≤ 4/(13*P.r.b3*P.p^2*P.h^7) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hb3',pow_pos hp 2,pow_pos hh 7,mul_pos (pow_pos hp 2) (pow_pos hh 7)]
  exact hcmp.trans hstep

/-- Explicit `ε`-scaling of the inventory bottleneck: slow channels of rate
`C ε^a` force recovery time `(ΔU/C) ε^{-a}`. -/
theorem inventory_bottleneck_scaling (U : ℝ → ℝ) (C a eps ΔU T : ℝ)
    (hC : 0 < C) (heps : 0 < eps) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ C*eps^a)
    (hrise : U 0 + ΔU ≤ U T) : ΔU/C*eps^(-a) ≤ T := by
  have hM : 0 < C*eps^a := mul_pos hC (Real.rpow_pos_of_pos heps a)
  have h := inventory_bottleneck U (C*eps^a) ΔU T hM hT hd hrise
  have hrw : ΔU/C*eps^(-a) = ΔU/(C*eps^a) := by
    rw [Real.rpow_neg heps.le]
    field_simp
  rw [hrw]
  exact h

end
end ReverseRateLimits.GlobalInventory

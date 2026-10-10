module
public import proofs.ReverseRateLimits.RecoveryCorollaries

@[expose] public section

namespace ReverseRateLimits.ReactionExtent
open Set MeasureTheory CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem
noncomputable section

def inventory (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  6*v.x t+5*v.y t+2*v.z t
def current3 (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  j3 P.r P.p P.h (v.x t) (v.y t) (v.z t)
def reverse3 (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  P.r.b3*P.p*P.h^6*(v.z t)^2

theorem deriv_inventory (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (inventory P v) (-13*current3 P v t) t := by
  have hd := (((v.dx t ht).const_mul 6).add ((v.dy t ht).const_mul 5)).add
    ((v.dz t ht).const_mul 2)
  change HasDerivAt (inventory P v) _ t at hd
  rw [neutral_pool] at hd
  exact hd

theorem integral_identity (P : Parameters) (v : LiteralTrajectory P) (T : ℝ) (hT : 0 ≤ T) :
    -(∫ t in (0:ℝ)..T, current3 P v t) =
      (inventory P v T-inventory P v 0)/13 := by
  have hx : ContinuousOn v.x (Icc 0 T) :=
    fun t ht => (v.dx t ht.1).continuousAt.continuousWithinAt
  have hy : ContinuousOn v.y (Icc 0 T) :=
    fun t ht => (v.dy t ht.1).continuousAt.continuousWithinAt
  have hz : ContinuousOn v.z (Icc 0 T) :=
    fun t ht => (v.dz t ht.1).continuousAt.continuousWithinAt
  have hj : ContinuousOn (current3 P v) (Icc 0 T) := by
    unfold current3 j3
    exact ((continuousOn_const.mul (hx.pow 2)).mul hy).sub
      (continuousOn_const.mul (hz.pow 2))
  have hint : IntervalIntegrable (fun t => -13*current3 P v t) volume 0 T :=
    (hj.const_mul (-13)).intervalIntegrable_of_Icc hT
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => deriv_inventory P v t (by rw [uIcc_of_le hT] at ht; exact ht.1)) hint
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith

theorem reverse_extent_dominates (P : Parameters) (v : LiteralTrajectory P)
    (T : ℝ) (hT : 0 ≤ T) :
    -(∫ t in (0:ℝ)..T, current3 P v t) ≤ ∫ t in (0:ℝ)..T, reverse3 P v t := by
  have hx : ContinuousOn v.x (Icc 0 T) :=
    fun t ht => (v.dx t ht.1).continuousAt.continuousWithinAt
  have hy : ContinuousOn v.y (Icc 0 T) :=
    fun t ht => (v.dy t ht.1).continuousAt.continuousWithinAt
  have hz : ContinuousOn v.z (Icc 0 T) :=
    fun t ht => (v.dz t ht.1).continuousAt.continuousWithinAt
  have hj : ContinuousOn (current3 P v) (Icc 0 T) := by
    unfold current3 j3
    exact ((continuousOn_const.mul (hx.pow 2)).mul hy).sub
      (continuousOn_const.mul (hz.pow 2))
  have hr : ContinuousOn (reverse3 P v) (Icc 0 T) := by
    unfold reverse3
    exact continuousOn_const.mul (hz.pow 2)
  have hnegI : IntervalIntegrable (fun t => -current3 P v t) volume 0 T :=
    hj.neg.intervalIntegrable_of_Icc hT
  have hrevI : IntervalIntegrable (reverse3 P v) volume 0 T :=
    hr.intervalIntegrable_of_Icc hT
  have h := intervalIntegral.integral_mono_on hT hnegI hrevI (by
      intro t ht
      have ha : 0 < P.r.a3 := (by norm_num : (0:ℝ)<99/100).trans_le P.ha3.1
      have hypos := (v.positive t ht.1).2.1
      have hforward : 0 ≤ P.r.a3*(v.x t)^2*(v.y t) := by positivity
      unfold current3 j3 reverse3
      linarith)
  simpa only [intervalIntegral.integral_neg] using h

theorem restoration_extent (P : Parameters) (v : LiteralTrajectory P)
    (hs : Starts P (witnessState P) v) (T : ℝ) (hT : 0 ≤ T)
    (hinner : Inner (A P v T) (B P v T) (Q P v T)) :
    P.p*P.h/26 ≤ -(∫ t in (0:ℝ)..T, current3 P v t) ∧
      P.p*P.h/26 ≤ ∫ t in (0:ℝ)..T, reverse3 P v t := by
  have hQ0 := (initial_coordinates P (witnessState P) v hs).2.2.trans (witness_state P).2.2
  have hQtarget := hinner.2.2.1
  have hw (t : ℝ) : inventory P v t=2*P.p*P.h*Q P v t := by
    unfold inventory Q
    have hp : P.p ≠ 0 := P.p_pos.ne'
    have hh : P.h ≠ 0 := P.hh.1.ne'
    field_simp
  have hgap : P.p*P.h/2 ≤ inventory P v T-inventory P v 0 := by
    rw [hw T,hw 0,hQ0]
    have hp := P.p_pos
    have hh := P.hh.1
    have hscaled := mul_le_mul_of_nonneg_left hQtarget
      (by positivity : (0:ℝ)≤2*P.p*P.h)
    nlinarith
  have hi := integral_identity P v T hT
  have hnet : P.p*P.h/26 ≤ -(∫ t in (0:ℝ)..T, current3 P v t) := by
    rw [hi]
    linarith
  exact ⟨hnet,hnet.trans (reverse_extent_dominates P v T hT)⟩

end
end ReverseRateLimits.ReactionExtent

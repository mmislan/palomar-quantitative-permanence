module
public import proofs.ReverseRateLimits.CorridorDynamics

@[expose] public section

namespace ReverseRateLimits.PhysicalConnection
open CoupledSource SourceBounds CorridorDynamics

structure LiteralTrajectory (P : Parameters) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  z : ℝ → ℝ
  dx : ∀ t, 0 ≤ t → HasDerivAt x (CoupledSource.dx P.r P.p P.h (x t) (y t) (z t)) t
  dy : ∀ t, 0 ≤ t → HasDerivAt y (CoupledSource.dy P.r P.p P.h (x t) (y t) (z t)) t
  dz : ∀ t, 0 ≤ t → HasDerivAt z (CoupledSource.dz P.r P.p P.h (x t) (y t) (z t)) t
  positive : ∀ t, 0 ≤ t → 0 < x t ∧ 0 < y t ∧ 0 < z t

noncomputable def Q (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  (6*v.x t+5*v.y t+2*v.z t)/(2*P.p*P.h)
noncomputable def A (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  v.x t/(P.p*P.h^3*(Q P v t)^3)
noncomputable def B (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  v.y t/(P.p*P.h^2*(Q P v t)^2)

theorem Q_pos (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    0 < Q P v t := by
  have hp := P.p_pos
  have hh := P.hh.1
  obtain ⟨hx,hy,hz⟩ := v.positive t ht
  unfold Q
  positivity

theorem reconstruction (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    v.x t = P.p*P.h^3*A P v t*(Q P v t)^3 ∧
    v.y t = P.p*P.h^2*B P v t*(Q P v t)^2 ∧
    v.z t = P.p*P.h*Q P v t*C P.h (Q P v t) (A P v t) (B P v t) := by
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hh : P.h ≠ 0 := P.hh.1.ne'
  have hq : Q P v t ≠ 0 := (Q_pos P v t ht).ne'
  constructor
  · unfold A
    field_simp
  · constructor
    · unfold B
      field_simp
    · unfold C A B
      field_simp
      have heq : (2*P.p*P.h)*Q P v t = 6*v.x t+5*v.y t+2*v.z t := by
        unfold Q
        field_simp
      nlinarith only [heq]

theorem full_field (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    CoupledSource.dx P.r P.p P.h (v.x t) (v.y t) (v.z t) =
      P.p*P.h^3*(P.p^2*(Q P v t)^3*RA P.r P.h P.u (Q P v t) (A P v t) (B P v t)+
        3*A P v t*(Q P v t)^2*qdot P.r P.p P.h (Q P v t) (A P v t) (B P v t)) ∧
    CoupledSource.dy P.r P.p P.h (v.x t) (v.y t) (v.z t) =
      P.p*P.h^2*(P.p^2*P.h^3*(Q P v t)^5*RB P.r P.h P.u (Q P v t) (A P v t) (B P v t)+
        2*B P v t*Q P v t*qdot P.r P.p P.h (Q P v t) (A P v t) (B P v t)) ∧
    6*CoupledSource.dx P.r P.p P.h (v.x t) (v.y t) (v.z t)+
      5*CoupledSource.dy P.r P.p P.h (v.x t) (v.y t) (v.z t)+
      2*CoupledSource.dz P.r P.p P.h (v.x t) (v.y t) (v.z t) =
      2*P.p*P.h*qdot P.r P.p P.h (Q P v t) (A P v t) (B P v t) := by
  have hr := reconstruction P v t ht
  have hs := transformed_source P.r P.h P.u (Q P v t) (A P v t) (B P v t)
    (Q_pos P v t ht).ne'
  dsimp only at hs
  simpa only [Parameters.p,hr.1,hr.2.1,hr.2.2] using hs

theorem deriv_Q (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (Q P v) (qdot P.r P.p P.h (Q P v t) (A P v t) (B P v t)) t := by
  have hd := (((v.dx t ht).const_mul 6).add ((v.dy t ht).const_mul 5)).add
    ((v.dz t ht).const_mul 2)
  have hd' := hd.div_const (2*P.p*P.h)
  have hs := (full_field P v t ht).2.2
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hh : P.h ≠ 0 := P.hh.1.ne'
  change HasDerivAt (Q P v) _ t at hd'
  rw [hs] at hd'
  convert hd' using 1
  field_simp

noncomputable def normalize (P : Parameters) (v : LiteralTrajectory P) : Trajectory P where
  A := A P v
  B := B P v
  Q := Q P v
  dA := by
    intro t ht
    have hp : P.p ≠ 0 := P.p_pos.ne'
    have hh : P.h ≠ 0 := P.hh.1.ne'
    have hq : Q P v t ≠ 0 := (Q_pos P v t ht).ne'
    have hden : P.p*P.h^3*(Q P v t)^3 ≠ 0 := by positivity
    have hd := (v.dx t ht).div
      (((deriv_Q P v t ht).pow 3).const_mul (P.p*P.h^3)) hden
    simp only [Pi.pow_apply] at hd
    change HasDerivAt (A P v) _ t at hd
    have hs := (full_field P v t ht).1
    have hx := (reconstruction P v t ht).1
    rw [hs,hx] at hd
    convert hd using 1
    field_simp
    ring
  dB := by
    intro t ht
    have hp : P.p ≠ 0 := P.p_pos.ne'
    have hh : P.h ≠ 0 := P.hh.1.ne'
    have hq : Q P v t ≠ 0 := (Q_pos P v t ht).ne'
    have hden : P.p*P.h^2*(Q P v t)^2 ≠ 0 := by positivity
    have hd := (v.dy t ht).div
      (((deriv_Q P v t ht).pow 2).const_mul (P.p*P.h^2)) hden
    simp only [Pi.pow_apply] at hd
    change HasDerivAt (B P v) _ t at hd
    have hs := (full_field P v t ht).2.1
    have hy := (reconstruction P v t ht).2.1
    rw [hs,hy] at hd
    convert hd using 1
    field_simp
    ring
  dQ := deriv_Q P v

/-- Literal positive mass-action trajectories, with only their initial basin
inequality supplied, stay in the outer region and recover into the inner one. -/
theorem literal_recovery (P : Parameters) (v : LiteralTrajectory P)
    (hinit : Outer (A P v 0) (B P v 0) (Q P v 0)) :
    (∀ t, 0 ≤ t → Outer (A P v t) (B P v t) (Q P v t)) ∧
    (∀ t, tQ P ≤ t → Inner (A P v t) (B P v t) (Q P v t)) := by
  exact ⟨outer_invariant P (normalize P v) hinit, recovery P (normalize P v) hinit⟩

end ReverseRateLimits.PhysicalConnection

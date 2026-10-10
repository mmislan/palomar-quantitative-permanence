module
public import proofs.ReverseRateLimits.SourceExistence

@[expose] public section

namespace ReverseRateLimits.CoupledTheorem
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection PhysicalBounds
  SourceExistence OAI.Problem326
noncomputable section

def stateQ (P : Parameters) (x : Fin 3 → ℝ) : ℝ :=
  (6*x 0+5*x 1+2*x 2)/(2*P.p*P.h)
def stateA (P : Parameters) (x : Fin 3 → ℝ) : ℝ := x 0/(P.p*P.h^3*(stateQ P x)^3)
def stateB (P : Parameters) (x : Fin 3 → ℝ) : ℝ := x 1/(P.p*P.h^2*(stateQ P x)^2)
def Prepared (P : Parameters) (x : Fin 3 → ℝ) : Prop :=
  Outer (stateA P x) (stateB P x) (stateQ P x)
def Starts (P : Parameters) (x : Fin 3 → ℝ) (v : LiteralTrajectory P) : Prop :=
  v.x 0 = x 0 ∧ v.y 0 = x 1 ∧ v.z 0 = x 2

theorem initial_coordinates (P : Parameters) (x : Fin 3 → ℝ) (v : LiteralTrajectory P)
    (hs : Starts P x v) : A P v 0 = stateA P x ∧ B P v 0 = stateB P x ∧ Q P v 0 = stateQ P x := by
  simp only [Starts] at hs
  simp [A,B,Q,stateA,stateB,stateQ,hs.1,hs.2.1,hs.2.2]

/-- The robust literal selected-family endpoint. Parameter and initial-state
data contain no capture, invariance, convergence or deadline assumptions. -/
theorem prepared_family (P : Parameters) (x0 : Fin 3 → ℝ)
    (hpos : PositiveState x0) (hprepared : Prepared P x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
    ∀ v : LiteralTrajectory P, Starts P x0 v →
      (∀ t, 0 ≤ t →
        ((3/64:ℝ)*P.p*P.h^3 ≤ v.x t ∧ v.x t ≤ 5*P.p*P.h^3) ∧
        ((1/16:ℝ)*P.p*P.h^2 ≤ v.y t ∧ v.y t ≤ 3*P.p*P.h^2) ∧
        ((1/8:ℝ)*P.p*P.h ≤ v.z t ∧ v.z t ≤ P.p*P.h)) ∧
      (∀ t, 46/(P.p^2*P.h^7) ≤ t → Inner (A P v t) (B P v t) (Q P v t)) := by
  constructor
  · exact exists_literal_trajectory P x0 hpos
  · intro v hs
    have hcoords := initial_coordinates P x0 v hs
    have hinit : Outer (A P v 0) (B P v 0) (Q P v 0) := by
      rw [hcoords.1,hcoords.2.1,hcoords.2.2]
      exact hprepared
    exact ⟨all_time_coordinate_bounds P v hinit,
      fun t ht => (literal_recovery P v hinit).2 t ((total_deadline P).trans ht)⟩

def witnessState (P : Parameters) : Fin 3 → ℝ :=
  ![P.p*P.h^3*4*(1/4:ℝ)^3,
    P.p*P.h^2*2*(1/4:ℝ)^2,
    P.p*P.h*(1/4:ℝ)*C P.h (1/4:ℝ) 4 2]

theorem witness_state (P : Parameters) :
    PositiveState (witnessState P) ∧ Prepared P (witnessState P) ∧
      stateQ P (witnessState P) = (1/4:ℝ) := by
  have ho : Outer 4 2 (1/4:ℝ) := by norm_num [Outer]
  have hC := (C_bounds P (1/4:ℝ) 4 2 ho).1
  have hp := P.p_pos
  have hh := P.hh.1
  have hpne := hp.ne'
  have hhne := hh.ne'
  have hQ : stateQ P (witnessState P) = (1/4:ℝ) := by
    unfold stateQ witnessState C
    norm_num [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    field_simp
    ring
  have hA : stateA P (witnessState P) = 4 := by
    unfold stateA
    rw [hQ]
    norm_num [witnessState]
    field_simp
  have hB : stateB P (witnessState P) = 2 := by
    unfold stateB
    rw [hQ]
    norm_num [witnessState]
    field_simp
  refine ⟨?_,?_,hQ⟩
  · intro i
    fin_cases i <;> norm_num [witnessState]
    all_goals positivity
  · unfold Prepared
    rw [hA,hB,hQ]
    exact ho

/-- A genuine global trajectory witnesses the lower physical clock. The
coordinate orders also match along every trajectory in the proved basin. -/
theorem sharp_time_witness (P : Parameters) :
    ∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
      ∀ t, 0 ≤ t → Inner (A P v t) (B P v t) (Q P v t) →
        1/(2004*P.p^2*P.h^7) ≤ t := by
  obtain ⟨hpos,hprep,hQ⟩ := witness_state P
  obtain ⟨v,hs⟩ := (prepared_family P (witnessState P) hpos hprep).1
  have hc := initial_coordinates P (witnessState P) v hs
  have hinit : Outer (A P v 0) (B P v 0) (Q P v 0) := by
    rw [hc.1,hc.2.1,hc.2.2]
    exact hprep
  refine ⟨v,hs,?_⟩
  intro t ht htarget
  exact recovery_time_lower P v hinit (hc.2.2.trans hQ) t ht htarget.2.2.1

end
end ReverseRateLimits.CoupledTheorem

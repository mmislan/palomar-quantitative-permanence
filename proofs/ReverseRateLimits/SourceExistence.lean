module
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import proofs.ReverseRateLimits.SourceNetwork
public import proofs.ReverseRateLimits.UpstreamCompatibility
public import proofs.ReverseRateLimits.PhysicalBounds

@[expose] public section

namespace ReverseRateLimits.SourceExistence
open CoupledSource SourceBounds SourceNetwork OAI.Problem326 PhysicalConnection

/-- Global positivity is supplied by the compiled published theorem for the
literal network; it is not a hypothesis on a desired basin trajectory. -/
theorem exists_literal_trajectory (P : Parameters) (x0 : Fin 3 → ℝ)
    (hx0 : PositiveState x0) :
    ∃ v : LiteralTrajectory P,
      v.x 0 = x0 0 ∧ v.y 0 = x0 1 ∧ v.z 0 = x0 2 := by
  obtain ⟨g,hg,hpos⟩ := published_global_solution 3 network (SourceNetwork.rate P)
    (by norm_num) weakly_reversible (rates_positive P) x0 hx0
  let v : LiteralTrajectory P := {
    x := fun t => g t 0
    y := fun t => g t 1
    z := fun t => g t 2
    dx := by
      intro t ht
      have hd := hasDerivAt_pi.mp (hg.2 t ht) 0
      rw [field_identity] at hd
      exact hd
    dy := by
      intro t ht
      have hd := hasDerivAt_pi.mp (hg.2 t ht) 1
      rw [field_identity] at hd
      exact hd
    dz := by
      intro t ht
      have hd := hasDerivAt_pi.mp (hg.2 t ht) 2
      rw [field_identity] at hd
      exact hd
    positive := fun t ht => ⟨hpos t ht 0,hpos t ht 1,hpos t ht 2⟩ }
  exact ⟨v,congrFun hg.1 0,congrFun hg.1 1,congrFun hg.1 2⟩

/-- Every finite classical segment of the literal polynomial field extends to
a global solution. No positivity of the segment or prepared basin is assumed. -/
theorem finite_solution_extends (P : Parameters) (x0 : Fin 3 → ℝ)
    (hx0 : PositiveState x0) (T : ℝ) (hT : 0 ≤ T)
    (x : ℝ → Fin 3 → ℝ)
    (hx : IsForwardSolutionOn network (SourceNetwork.rate P) x0 T x) :
    ∃ g : ℝ → Fin 3 → ℝ,
      IsGlobalForwardSolution network (SourceNetwork.rate P) x0 g ∧
      Set.EqOn g x (Set.Icc 0 T) := by
  obtain ⟨K,_,_,_,hxK,_,hinv⟩ := compact_convex_invariant_polytope
    3 network (SourceNetwork.rate P) (by norm_num) weakly_reversible
    (rates_positive P) x0 hx0
  exact ((hinv x0 hxK).2 T x hT hx).2

end ReverseRateLimits.SourceExistence

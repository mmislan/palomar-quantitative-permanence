module
public import proofs.ReverseRateLimits.Upstream.AffineTrajectory
public import proofs.ReverseRateLimits.Upstream.MassActionFlux

@[expose] public section

namespace ReverseRateLimits
open Set OAI.Problem326
open scoped BigOperators
noncomputable section

def Annihilator {d : ℕ} (N : ReactionNetwork d) (r : Fin d → ℝ) : Prop :=
  ∀ e : Reaction N, dot r (fun i => (e.val.2 i:ℝ))-dot r (fun i => (e.val.1 i:ℝ)) = 0

/-- Equality of all stoichiometric conservation laws defines the literal
affine compatibility class. Positivity is a separate hypothesis. -/
def SameClass {d : ℕ} (N : ReactionNetwork d) (c x : Fin d → ℝ) : Prop :=
  ∀ r : Fin d → ℝ, Annihilator N r → dot r x = dot r c

theorem annihilator_work {d : ℕ} (N : ReactionNetwork d) (k : Reaction N → ℝ)
    (x r : Fin d → ℝ) (hr : Annihilator N r) : dot r (massAction N k x) = 0 := by
  rw [dot_massAction_eq_flux]
  exact Finset.sum_eq_zero (fun e _ => by rw [hr e,mul_zero])

theorem preserves_sameClass {d : ℕ} (N : ReactionNetwork d) (k : Reaction N → ℝ)
    (c x0 : Fin d → ℝ) (hc : SameClass N c x0)
    (x : ℝ → Fin d → ℝ) (hx : IsGlobalForwardSolution N k x0 x) :
    ∀ t, 0 ≤ t → SameClass N c (x t) := by
  intro t ht r hr
  have hd : ∀ s ∈ Icc 0 t, HasDerivAt (fun u => dot r (x u)) 0 s := by
    intro s hs
    have h := hasDerivAt_dot_curve r (hx.2 s hs.1)
    rwa [annihilator_work N k (x s) r hr] at h
  have hcont : ContinuousOn (fun s => dot r (x s)) (Icc 0 t) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => dot r (x s)) (interior (Icc 0 t)) :=
    fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ interior (Icc 0 t), deriv (fun u => dot r (x u)) s = 0 :=
    fun s hs => (hd s (interior_subset hs)).deriv
  have hlo := (convex_Icc 0 t).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun s hs => (hderiv s hs).ge) 0 ⟨le_rfl,ht⟩ t ⟨ht,le_rfl⟩ ht
  have hhi := (convex_Icc 0 t).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun s hs => (hderiv s hs).le) 0 ⟨le_rfl,ht⟩ t ⟨ht,le_rfl⟩ ht
  rw [hx.1,hc r hr] at hlo hhi
  linarith

end
end ReverseRateLimits

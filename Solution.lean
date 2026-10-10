module
public import proofs.ReverseRateLimits.Publication
public import proofs.ReverseRateLimits.StateCapacity

@[expose] public section
namespace QuantitativeRegistry
open ReverseRateLimits.CoupledSource ReverseRateLimits.SourceBounds ReverseRateLimits.ExponentFamily
theorem family_parameters (template : Parameters) (epsilon gamma : ℝ)
    (he : 0 < epsilon) (hg : (1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ))
    (hcut : epsilon ≤ improvedCutoff gamma) :
    ∃ P : Parameters, P.r=template.r ∧ P.h=epsilon^(hExponent gamma) ∧
      P.u=epsilon^(uExponent gamma) := by
  exact ⟨parameters template epsilon gamma he hg hcut,rfl,rfl,rfl⟩

theorem admitted_parameters : Nonempty Parameters := by
  refine ⟨{
    h := 1/600
    u := 1/20
    r := {
      a1 := 1
      a2 := 1
      a3 := 1
      k := 4
      b1 := 1
      b2 := 1
      b3 := 1
      b4 := 1 }
    hh := ?_
    hu := ?_
    ha1 := ?_
    ha2 := ?_
    ha3 := ?_
    hK := ?_
    hb1 := ?_
    hb2 := ?_
    hb3 := ?_
    hb4 := ?_ }⟩ <;> norm_num
end QuantitativeRegistry

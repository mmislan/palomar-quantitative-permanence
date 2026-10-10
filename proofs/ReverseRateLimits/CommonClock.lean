module
public import proofs.ReverseRateLimits.Upstream.Model

@[expose] public section

namespace ReverseRateLimits.CommonClock
open OAI.Problem326
noncomputable section

theorem massAction_scale {d : ℕ} (N : ReactionNetwork d)
    (k : Reaction N → ℝ) (clock : ℝ) (x : Fin d → ℝ) :
    massAction N (fun e => clock*k e) x = clock • massAction N k x := by
  funext i
  simp only [massAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Multiplying every autonomous rate by one positive clock changes only time. -/
theorem rescale {d : ℕ} (N : ReactionNetwork d) (k : Reaction N → ℝ)
    (x0 : Fin d → ℝ) (x : ℝ → Fin d → ℝ) (clock : ℝ) (hc : 0 < clock)
    (hs : IsGlobalForwardSolution N k x0 x) :
    IsGlobalForwardSolution N (fun e => clock*k e) x0 (fun t => x (clock*t)) := by
  refine ⟨by simpa using hs.1,?_⟩
  intro t ht
  have hd := (hs.2 (clock*t) (mul_nonneg hc.le ht)).scomp t
    ((hasDerivAt_id t).const_mul clock)
  simpa only [massAction_scale,mul_one,Function.comp_def,id_eq] using hd

theorem rescale_iff {d : ℕ} (N : ReactionNetwork d) (k : Reaction N → ℝ)
    (x0 : Fin d → ℝ) (x : ℝ → Fin d → ℝ) (clock : ℝ) (hc : 0 < clock) :
    IsGlobalForwardSolution N (fun e => clock*k e) x0 (fun t => x (clock*t)) ↔
      IsGlobalForwardSolution N k x0 x := by
  constructor
  · intro hs
    have h := rescale N (fun e => clock*k e) x0 (fun t => x (clock*t))
      clock⁻¹ (inv_pos.mpr hc) hs
    have hk : (fun e => clock⁻¹*(clock*k e)) = k := by
      funext e
      field_simp
    have hx : (fun t => x (clock*(clock⁻¹*t))) = x := by
      funext t
      congr 1
      field_simp
    simpa only [hk,hx] using h
  · exact rescale N k x0 x clock hc

end
end ReverseRateLimits.CommonClock

module
public import proofs.ReverseRateLimits.ScaleChain
public import proofs.ReverseRateLimits.UpstreamCompatibility

@[expose] public section

namespace ReverseRateLimits
open Set Filter OAI.Problem326
open scoped Topology
noncomputable section

/-- Actual classwise absorption at a fixed scale. All geometry gates are
uniform smallness conditions; no absorption or existence conclusion is assumed. -/
theorem classwise_absorption {d : ℕ} (hd : 0 < d) (N : ReactionNetwork d)
    (G : NetworkGeometry N) (c : Fin d → ℝ) (hc : PositiveState c)
    (k : Reaction N → ℝ) (lower target : ℝ) (D : ℕ)
    (hweak : WeaklyReversible N) (hlower : 0 < lower) (hk : ∀ e, lower ≤ k e)
    (htarget : 0 < target) (htarget1 : target < 1)
    (hgates : ∀ h, 0 < h → h ≤ target → h < G.hmax ∧ h < 1 ∧
      ∀ i, |Real.log (c i)/Real.log h| < G.H)
    (hmargins : ∀ h, 0 < h → h ≤ target → h^G.H*(∑ e, k e) ≤ lower/2)
    (hdegree : ∀ e : Reaction N, ∑ i, e.val.1 i ≤ D) :
    ∀ x0 : Fin d → ℝ, PositiveState x0 → SameClass N c x0 →
      (∃ x, IsGlobalForwardSolution N k x0 x) ∧
      ∀ x, IsGlobalForwardSolution N k x0 x → ∃ T, 0 ≤ T ∧
        ∀ t, T ≤ t → ∀ i, target^(1/2:ℝ) ≤ x t i ∧ x t i ≤ (target^(1/2:ℝ))⁻¹ := by
  classical
  let P : ∀ n, ScalePlateau G c (dyadicScale target n) := fun n =>
    Classical.choice (exists_scalePlateau G c hc _ (dyadicScale_pos htarget n)
      ((dyadicScale_le htarget.le htarget1.le n).trans_lt htarget1)
      (hgates _ (dyadicScale_pos htarget n) (dyadicScale_le htarget.le htarget1.le n)).1
      (hgates _ (dyadicScale_pos htarget n) (dyadicScale_le htarget.le htarget1.le n)).2.2)
  have hsmall : ∀ n, dyadicScale target n < G.hmax := fun n =>
    (hgates _ (dyadicScale_pos htarget n) (dyadicScale_le htarget.le htarget1.le n)).1
  have hmargin : ∀ n, (dyadicScale target n)^G.H*(∑ e, k e) ≤ lower/2 := fun n =>
    hmargins _ (dyadicScale_pos htarget n) (dyadicScale_le htarget.le htarget1.le n)
  intro x0 hx0 hclass
  constructor
  · obtain ⟨x,hx,_⟩ := published_global_solution d N k hd hweak
      (fun e => hlower.trans_le (hk e)) x0 hx0
    exact ⟨x,hx⟩
  · intro x hx
    have hevent : ∀ᶠ n : ℕ in atTop,
        ∀ i, |Real.log (x0 i)/Real.log (dyadicScale target n)| < G.H := by
      apply Filter.eventually_all.mpr
      intro i
      have hlim : Tendsto
          (fun n => |Real.log (x0 i)/Real.log (dyadicScale target n)|) atTop (𝓝 0) := by
        simpa only [Function.comp_def,abs_zero] using
          ((tendsto_log_coordinate_div_log (x0 i)).comp
            (dyadicScale_tendsto htarget htarget1)).abs
      exact hlim.eventually_lt_const G.H_pos
    obtain ⟨n,hn⟩ := hevent.exists
    have hxK : x0 ∈ (P n).set := by
      apply initial_mem_of_active_zero (P n) x0
      intro L ha
      have hpoint : Affine.powerPoint (dyadicScale target n)
          (fun i => Real.log (x0 i)/Real.log (dyadicScale target n)) = x0 :=
        funext (fun i => rpow_log_ratio (dyadicScale_pos htarget n)
          ((dyadicScale_le htarget.le htarget1.le n).trans_lt htarget1) (hx0 i))
      apply G.active_slope_zero _ (dyadicScale_pos htarget n) (hsmall n) _ hn L
      rwa [hpoint]
    have hinit : ∀ t, 0 ≤ t → x t ∈ (P n).set :=
      global_solution_stays ((P n).invariant k lower D hweak (dyadicScale_pos htarget n)
        ((dyadicScale_le htarget.le htarget1.le n).trans_lt htarget1) (hsmall n)
        hlower hk (hmargin n) hdegree) hx 0 le_rfl (by rwa [hx.1])
    obtain ⟨T,hT,hstay⟩ := dyadic_plateau_descent G c target htarget htarget1 P k lower D
      hweak hlower hk hsmall hmargin hdegree x0 hclass x hx n ⟨0,le_rfl,hinit⟩
    refine ⟨T,hT,?_⟩
    intro t ht i
    have hb := (P 0).inside_sqrt_box (dyadicScale_pos htarget 0)
      ((dyadicScale_le htarget.le htarget1.le 0).trans_lt htarget1) (hsmall 0) (x t) (hstay t ht)
    have hb' : x t ∈ Icc (fun _ => target^(1/2:ℝ)) (fun _ => (target^(1/2:ℝ))⁻¹) := by
      simpa only [dyadicScale,pow_zero,pow_one] using hb
    exact ⟨hb'.1 i,hb'.2 i⟩

end
end ReverseRateLimits

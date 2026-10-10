module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section
namespace QuantitativeRegistry
open Set MeasureTheory
noncomputable section

/-- State-dependent capacity on an open interval (more generally any open
convex subset of the real line). No monotonicity of the inventory is assumed.
Derivative and region conditions concern only the interval before the target.
-/
theorem state_capacity_clock (U g : ℝ → ℝ) (S : Set ℝ)
    (hsopen : IsOpen S) (hsconv : Convex ℝ S)
    (hg : ContinuousOn g S) (hgpos : ∀ u ∈ S, 0 < g u)
    (target T : ℝ) (hT : 0 ≤ T)
    (hregion : ∀ t ∈ Icc (0:ℝ) T, U t ∈ S)
    (htarget : target ∈ S) (hrise : target ≤ U T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ g (U t)) :
    (∫ s in (U 0)..target, 1/g s) ≤ T := by
  let f : ℝ → ℝ := fun u => 1/g u
  let Phi : ℝ → ℝ := fun u => ∫ s in (U 0)..u, f s
  have hfc : ContinuousOn f S :=
    continuousOn_const.div hg (fun u hu => (hgpos u hu).ne')
  have hfi : ∀ u ∈ S, ∀ v ∈ S, IntervalIntegrable f volume u v := by
    intro u hu v hv
    exact (hfc.mono (hsconv.ordConnected.uIcc_subset hu hv)).intervalIntegrable
  have h0 : U 0 ∈ S := hregion 0 ⟨le_rfl,hT⟩
  have hlast : U T ∈ S := hregion T ⟨hT,le_rfl⟩
  have hphi : ∀ u ∈ S, HasDerivAt Phi (f u) u := by
    intro u hu
    exact intervalIntegral.integral_hasDerivAt_right (hfi (U 0) h0 u hu)
      (ContinuousOn.stronglyMeasurableAtFilter hsopen hfc u hu)
      (hfc.continuousAt (hsopen.mem_nhds hu))
  have hcomp : ∀ t ∈ Icc (0:ℝ) T,
      ∃ d, HasDerivAt (fun s => Phi (U s)) d t ∧ d ≤ 1 := by
    intro t ht
    obtain ⟨d,hdt,hbound⟩ := hd t ht
    refine ⟨f (U t)*d,(hphi (U t) (hregion t ht)).comp t hdt,?_⟩
    dsimp [f]
    rw [one_div,mul_comm,← div_eq_mul_inv,div_le_iff₀ (hgpos (U t) (hregion t ht))]
    simpa using hbound
  have hc : ContinuousOn (fun s => Phi (U s)) (Icc (0:ℝ) T) := by
    intro t ht
    obtain ⟨_,hdt,_⟩ := hcomp t ht
    exact hdt.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => Phi (U s)) (interior (Icc (0:ℝ) T)) := by
    intro t ht
    obtain ⟨_,hdt,_⟩ := hcomp t (interior_subset ht)
    exact hdt.differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ interior (Icc (0:ℝ) T), deriv (fun s => Phi (U s)) t ≤ 1 := by
    intro t ht
    obtain ⟨d,hdt,hle⟩ := hcomp t (interior_subset ht)
    rw [hdt.deriv]
    exact hle
  have hclock := (convex_Icc 0 T).image_sub_le_mul_sub_of_deriv_le hc hdiff hbound
    0 ⟨le_rfl,hT⟩ T ⟨hT,le_rfl⟩ hT
  have htotal : (∫ s in (U 0)..(U T), f s) ≤ T := by
    simpa [Phi] using hclock
  have hnonneg : 0 ≤ ∫ s in target..(U T), f s := by
    apply intervalIntegral.integral_nonneg hrise
    intro u hu
    have huS : u ∈ S := hsconv.ordConnected.uIcc_subset htarget hlast
      (by simpa only [uIcc_of_le hrise] using hu)
    exact (one_div_pos.mpr (hgpos u huS)).le
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hfi (U 0) h0 target htarget) (hfi target htarget (U T) hlast)
  dsimp only [f] at htotal hnonneg hadd
  linarith

end
end QuantitativeRegistry

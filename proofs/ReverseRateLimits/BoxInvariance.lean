module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Data.Finset.Order
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

namespace ReverseRateLimits
open Set Filter
open scoped Topology

lemma eventually_lt_left_of_hasDerivAt_pos {f : ℝ → ℝ} {d t : ℝ}
    (hf : HasDerivAt f d t) (hd : 0 < d) :
    ∀ᶠ u in 𝓝[<] t, f u < f t := by
  have hs := hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t)
  filter_upwards [hs.eventually (Ioi_mem_nhds hd), self_mem_nhdsWithin] with u hu htu
  have hdiv : 0 < (f u - f t) / (u - t) := by
    simpa only [slope_def_field] using hu
  have hneg : f u - f t < 0 := by
    rcases div_pos_iff.mp hdiv with h | h
    · exact False.elim ((not_lt_of_ge (sub_neg.mpr htu).le) h.2)
    · exact h.1
  exact sub_neg.mp hneg

lemma eventually_lt_right_of_hasDerivAt_pos {f : ℝ → ℝ} {d t : ℝ}
    (hf : HasDerivAt f d t) (hd : 0 < d) :
    ∀ᶠ u in 𝓝[>] t, f t < f u := by
  have hs := hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  filter_upwards [hs.eventually (Ioi_mem_nhds hd), self_mem_nhdsWithin] with u hu htu
  have hdiv : 0 < (f u - f t) / (u - t) := by
    simpa only [slope_def_field] using hu
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr htu)).mp hdiv)

/-- Finite simultaneous constraints cannot reach their first boundary when
each active boundary has a strict inward derivative. -/
theorem strict_box_invariance {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a b : ℝ)
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (hinit : ∀ i, 0 < f i a)
    (hin : ∀ t ∈ Icc a b, (∀ i, 0 ≤ f i t) → ∀ i, f i t = 0 →
      ∃ d, HasDerivAt (f i) d t ∧ 0 < d) :
    ∀ t ∈ Icc a b, ∀ i, 0 < f i t := by
  classical
  intro t ht
  by_contra hbad
  push Not at hbad
  obtain ⟨i, hi⟩ := hbad
  obtain ⟨v, hv, hz⟩ := intermediate_value_Icc' ht.1
    ((hc i).mono (Icc_subset_Icc le_rfl ht.2)) ⟨hi, (hinit i).le⟩
  let K := Icc a t ∩ {u | ∃ j, f j u = 0}
  have hKn : K.Nonempty := ⟨v, hv, i, hz⟩
  have hKc : IsCompact K := by
    apply isCompact_Icc.of_isClosed_subset
    · have hclosed : IsClosed (Icc a t ∩ {u | ∃ j, f j u = 0}) := by
        have heq : {u | ∃ j, f j u = 0} = ⋃ j, (f j) ⁻¹' {0} := by ext; simp
        rw [heq, inter_iUnion]
        exact isClosed_iUnion_of_finite (fun j =>
          ((hc j).mono (Icc_subset_Icc le_rfl ht.2)).preimage_isClosed_of_isClosed
            isClosed_Icc isClosed_singleton)
      exact hclosed
    · exact inter_subset_left
  obtain ⟨s, hs, hmin⟩ := hKc.exists_isMinOn hKn continuousOn_id
  have has : a < s := by
    apply lt_of_le_of_ne hs.1.1
    intro heq
    obtain ⟨j, hj⟩ := hs.2
    rw [← heq] at hj
    exact (hinit j).ne' hj
  have hnonneg : ∀ u ∈ Icc a s, ∀ j, 0 ≤ f j u := by
    intro u hu j
    by_contra hn
    have hneg : f j u < 0 := lt_of_not_ge hn
    obtain ⟨w, hw, hfw⟩ := intermediate_value_Icc' hu.1
      ((hc j).mono (Icc_subset_Icc le_rfl (hu.2.trans (hs.1.2.trans ht.2))))
      ⟨hneg.le, (hinit j).le⟩
    have hsw : s ≤ w := hmin ⟨⟨hw.1, hw.2.trans (hu.2.trans hs.1.2)⟩, j, hfw⟩
    have hwu : w = u := le_antisymm hw.2 (hu.2.trans hsw)
    rw [hwu] at hfw
    exact hneg.ne hfw
  obtain ⟨j, hj⟩ := hs.2
  obtain ⟨d, hd, hdp⟩ := hin s ⟨hs.1.1, hs.1.2.trans ht.2⟩
    (hnonneg s ⟨hs.1.1, le_rfl⟩) j hj
  obtain ⟨u, hu, hau⟩ :=
    ((eventually_lt_left_of_hasDerivAt_pos hd hdp).and (Ico_mem_nhdsLT has)).exists
  have hn := hnonneg u ⟨hau.1, hau.2.le⟩ j
  rw [hj] at hu
  exact (not_lt_of_ge hn) hu

/-- Closed initial boxes also work: an initially active face enters the
interior immediately. No invariant-region hypothesis is assumed. -/
theorem closed_box_invariance {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (hinit : ∀ i, 0 ≤ f i a)
    (hderiv : ∀ i, ∃ d, HasDerivAt (f i) d a)
    (hin : ∀ t ∈ Icc a b, (∀ i, 0 ≤ f i t) → ∀ i, f i t = 0 →
      ∃ d, HasDerivAt (f i) d t ∧ 0 < d) :
    ∀ t ∈ Icc a b, ∀ i, 0 ≤ f i t := by
  classical
  have heach : ∀ i, ∀ᶠ u in 𝓝[>] a, 0 < f i u := by
    intro i
    rcases eq_or_lt_of_le (hinit i) with hi | hi
    · obtain ⟨d, hd, hdp⟩ := hin a ⟨le_rfl, hab⟩ hinit i hi.symm
      simpa only [← hi] using eventually_lt_right_of_hasDerivAt_pos hd hdp
    · obtain ⟨d, hd⟩ := hderiv i
      exact hd.continuousAt.continuousWithinAt.eventually (Ioi_mem_nhds hi)
  have hall : ∀ᶠ u in 𝓝[>] a, ∀ i, 0 < f i u := eventually_all.mpr heach
  obtain ⟨e, hae, he⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
  intro t ht i
  rcases ht.1.eq_or_lt with hat | hat
  · simpa only [← hat] using hinit i
  · obtain ⟨s, has, hsm⟩ := exists_between (lt_min hae hat)
    have hst : s ≤ t := (lt_of_lt_of_le hsm (min_le_right _ _)).le
    have hcs : ∀ j, ContinuousOn (f j) (Icc s t) :=
      fun j => (hc j).mono (Icc_subset_Icc has.le ht.2)
    have hp : ∀ j, 0 < f j s := he ⟨has, hsm.trans_le (min_le_left _ _)⟩
    exact (strict_box_invariance f s t hcs hp
      (fun u hu => hin u ⟨has.le.trans hu.1, hu.2.trans ht.2⟩)
      t ⟨hst, le_rfl⟩ i).le

end ReverseRateLimits

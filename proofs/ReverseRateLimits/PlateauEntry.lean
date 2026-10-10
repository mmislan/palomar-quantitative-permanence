module
public import proofs.ReverseRateLimits.Upstream.ActiveBranchMinimum

@[expose] public section

namespace ReverseRateLimits
open Set OAI.Problem326

/-- Active positive drift below a genuine global ceiling gives finite entry
into its plateau. Neither entry nor absorption is assumed. Ties are included. -/
theorem finite_minimum_plateau_entry {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (a b M δ : ℝ) (hab : a ≤ b) (_hδ : 0 < δ)
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hceiling : ∀ t ∈ Icc a b, s.inf' hne (fun i => f i t) ≤ M)
    (hnonneg : ∀ t ∈ Ico a b, ∀ i ∈ s,
      s.inf' hne (fun j => f j t) = f i t →
      ∃ d, HasDerivAt (f i) d t ∧ 0 ≤ d)
    (hspeed : ∀ t ∈ Ico a b, s.inf' hne (fun i => f i t) < M → ∀ i ∈ s,
      s.inf' hne (fun j => f j t) = f i t →
      ∃ d, HasDerivAt (f i) d t ∧ δ ≤ d)
    (hdeadline : M-s.inf' hne (fun i => f i a) ≤ δ*(b-a)) :
    s.inf' hne (fun i => f i b) = M := by
  have hm := finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg s hne f a b hc hnonneg
  apply le_antisymm (hceiling b ⟨hab,le_rfl⟩)
  by_contra hn
  have hlt : s.inf' hne (fun i => f i b) < M := lt_of_not_ge hn
  have hbelow : ∀ t ∈ Icc a b, s.inf' hne (fun i => f i t) < M := by
    intro t ht
    exact (hm ht ⟨hab,le_rfl⟩ ht.2).trans_lt hlt
  let g : ι → ℝ → ℝ := fun i t => f i t + (-δ)*t
  have hgc : ∀ i ∈ s, ContinuousOn (g i) (Icc a b) := by
    intro i hi
    exact (hc i hi).add (continuousOn_const.mul continuousOn_id)
  have hgd : ∀ t ∈ Ico a b, ∀ i ∈ s,
      s.inf' hne (fun j => g j t) = g i t →
      ∃ d, HasDerivAt (g i) d t ∧ 0 ≤ d := by
    intro t ht i hi ha
    have ha' : s.inf' hne (fun j => f j t) = f i t := by
      dsimp only [g] at ha
      rw [finite_minimum_add_const] at ha
      exact add_right_cancel ha
    obtain ⟨d, hd, hdp⟩ := hspeed t ht (hbelow t (Ico_subset_Icc_self ht)) i hi ha'
    refine ⟨d+(-δ),?_,by linarith⟩
    simpa only [g,mul_one,id_eq] using hd.fun_add ((hasDerivAt_id t).const_mul (-δ))
  have hgm := finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg s hne g a b hgc hgd
    ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  simp only [g,finite_minimum_add_const] at hgm
  linarith

end ReverseRateLimits

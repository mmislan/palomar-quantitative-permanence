module
public import proofs.ReverseRateLimits.BoxInvariance

@[expose] public section

namespace ReverseRateLimits
open Set

/-- A strict derivative at a threshold preserves residence above it. -/
theorem lower_residence (f v : ℝ → ℝ) (l s t : ℝ) (hst : s ≤ t)
    (hf : ∀ u ∈ Icc s t, HasDerivAt f (v u) u)
    (hin : ∀ u ∈ Icc s t, f u = l → 0 < v u)
    (hs : l ≤ f s) : l ≤ f t := by
  let g : Fin 1 → ℝ → ℝ := fun _ u => f u - l
  have hc : ContinuousOn f (Icc s t) :=
    fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have h := closed_box_invariance g s t hst
    (fun _ => hc.sub continuousOn_const)
    (fun _ => sub_nonneg.mpr hs)
    (fun _ => ⟨v s, (hf s ⟨le_rfl, hst⟩).sub_const l⟩)
    (by
      intro u hu _ i hi
      have heq : f u = l := sub_eq_zero.mp hi
      exact ⟨v u, (hf u hu).sub_const l, hin u hu heq⟩)
    t ⟨hst, le_rfl⟩ 0
  exact sub_nonneg.mp h

/-- Full-slab speed and a lower floor give a deadline for residence, rather
than only a first hitting time. -/
theorem lower_entry (f v : ℝ → ℝ) (L l δ s t : ℝ)
    (hδ : 0 < δ) (hst : s ≤ t)
    (hdeadline : (l-L)/δ ≤ t-s)
    (hf : ∀ u ∈ Icc s t, HasDerivAt f (v u) u)
    (hfloor : ∀ u ∈ Icc s t, L ≤ f u)
    (hslab : ∀ u ∈ Icc s t, f u ≤ l → δ ≤ v u) : l ≤ f t := by
  by_contra hn
  have hlt : f t < l := lt_of_not_ge hn
  have hbelow : ∀ u ∈ Icc s t, f u ≤ l := by
    intro u hu
    by_contra hnu
    have hur : l ≤ f u := (lt_of_not_ge hnu).le
    have hret := lower_residence f v l u t hu.2
      (fun w hw => hf w ⟨hu.1.trans hw.1, hw.2⟩)
      (fun w hw heq => hδ.trans_le (hslab w ⟨hu.1.trans hw.1, hw.2⟩ heq.le)) hur
    exact (not_le_of_gt hlt) hret
  have hcont : ContinuousOn f (Icc s t) := fun u hu =>
    (hf u hu).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc s t)) := by
    intro u hu
    exact (hf u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hslope : ∀ u ∈ interior (Icc s t), δ ≤ deriv f u := by
    intro u hu
    rw [(hf u (interior_subset hu)).deriv]
    exact hslab u (interior_subset hu) (hbelow u (interior_subset hu))
  have hgrowth := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv hcont hdiff hslope
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have htime : l-L ≤ δ*(t-s) := by
    have hd := (div_le_iff₀ hδ).mp hdeadline
    simpa only [mul_comm] using hd
  have hstart := hfloor s ⟨le_rfl, hst⟩
  linarith

theorem upper_entry (f v : ℝ → ℝ) (U l δ s t : ℝ)
    (hδ : 0 < δ) (hst : s ≤ t)
    (hdeadline : (U-l)/δ ≤ t-s)
    (hf : ∀ u ∈ Icc s t, HasDerivAt f (v u) u)
    (hceiling : ∀ u ∈ Icc s t, f u ≤ U)
    (hslab : ∀ u ∈ Icc s t, l ≤ f u → v u ≤ -δ) : f t ≤ l := by
  have hn := lower_entry (fun u => -f u) (fun u => -v u) (-U) (-l) δ s t
    hδ hst (by convert hdeadline using 1; ring)
    (fun u hu => (hf u hu).neg)
    (fun u hu => by linarith [hceiling u hu])
    (fun u hu h => by linarith [hslab u hu (by linarith)])
  linarith

end ReverseRateLimits

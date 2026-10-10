module
public import proofs.ReverseRateLimits.ScalePlateau
public import proofs.ReverseRateLimits.PlateauEntry

@[expose] public section

namespace ReverseRateLimits
open Set OAI.Problem326
noncomputable section

theorem global_solution_shift {d : ℕ} {N : ReactionNetwork d} {k : Reaction N → ℝ}
    {x0 : Fin d → ℝ} {x : ℝ → Fin d → ℝ} (hx : IsGlobalForwardSolution N k x0 x)
    (a : ℝ) (ha : 0 ≤ a) :
    IsGlobalForwardSolution N k (x a) (fun t => x (t+a)) := by
  refine ⟨by simp,?_⟩
  intro t ht
  simpa [Function.comp_def] using
    (hx.2 (t+a) (add_nonneg ht ha)).scomp t ((hasDerivAt_id t).add_const a)

theorem global_solution_stays {d : ℕ} {N : ReactionNetwork d} {k : Reaction N → ℝ}
    {K : Set (Fin d → ℝ)} (hinv : IsForwardInvariant N k K)
    {x0 : Fin d → ℝ} {x : ℝ → Fin d → ℝ} (hx : IsGlobalForwardSolution N k x0 x)
    (a : ℝ) (ha : 0 ≤ a) (hxK : x a ∈ K) : ∀ t, a ≤ t → x t ∈ K := by
  intro t ht
  have hs := global_solution_shift hx a ha
  have hT : 0 ≤ t-a := sub_nonneg.mpr ht
  have hf : IsForwardSolutionOn N k (x a) (t-a) (fun s => x (s+a)) :=
    ⟨hs.1,fun s hst => (hs.2 s hst.1).continuousAt.continuousWithinAt,
      fun s hst => hs.2 s hst.1.le⟩
  have hm := ((hinv (x a) hxK).2 (t-a) _ hT hf).1 (t-a) ⟨hT,le_rfl⟩
  simpa using hm

/-- Literal single-scale entry: the global mass-action equation, compatibility
class and box residence discharge every active-minimum premise. -/
theorem ScalePlateau.entry {d : ℕ} {N : ReactionNetwork d}
    {G : NetworkGeometry N} {c : Fin d → ℝ} {h : ℝ}
    (P : ScalePlateau G c h) (k : Reaction N → ℝ) (lower : ℝ) (D : ℕ)
    (hweak : WeaklyReversible N) (hh : 0 < h) (hh1 : h < 1)
    (hsmall : h < G.hmax) (hlower : 0 < lower) (hk : ∀ e, lower ≤ k e)
    (hmargin : h^G.H*(∑ e, k e) ≤ lower/2)
    (hdegree : ∀ e : Reaction N, ∑ i, e.val.1 i ≤ D)
    (x0 : Fin d → ℝ) (hclass : SameClass N c x0)
    (x : ℝ → Fin d → ℝ) (hx : IsGlobalForwardSolution N k x0 x)
    (a : ℝ) (ha : 0 ≤ a)
    (hbox : ∀ t, a ≤ t → x t ∈ Icc (fun _ => h) (fun _ => h⁻¹)) :
    ∃ b, a ≤ b ∧
      b = a+(P.level-G.minimum h (x a))/(G.H*lower*h^D) ∧
      ∀ t, b ≤ t → x t ∈ P.set := by
  classical
  let δ : ℝ := G.H*lower*h^D
  have hδ : 0 < δ := mul_pos (mul_pos G.H_pos hlower) (pow_pos hh D)
  let b : ℝ := a+(P.level-G.minimum h (x a))/δ
  have hab : a ≤ b := by
    dsimp only [b]
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (P.ceiling (x a))) hδ.le)
  have hc := preserves_sameClass N k c x0 hclass x hx
  have hnonneg : ∀ t ∈ Ico a b, ∀ L ∈ G.certificate.labels,
      G.minimum h (x t) = L.value h (x t) →
      ∃ v, HasDerivAt (fun s => L.value h (x s)) v t ∧ 0 ≤ v := by
    intro t ht L hL hval
    have haL := (G.active_iff_minimum h (x t) L).mpr ⟨hL,hval.symm⟩
    refine ⟨dot L.slope (massAction N k (x t)),
      (hasDerivAt_dot_curve L.slope (hx.2 t (ha.trans ht.1))).add_const (L.offset h),?_⟩
    by_cases hann : Annihilator N L.slope
    · rw [annihilator_work N k (x t) L.slope hann]
    · exact hδ.le.trans (G.active_drift k h lower D hweak hh hh1 hsmall hlower hk
        hmargin hdegree (x t) (hbox t ht.1) L haL hann)
  have hspeed : ∀ t ∈ Ico a b, G.minimum h (x t) < P.level →
      ∀ L ∈ G.certificate.labels, G.minimum h (x t) = L.value h (x t) →
      ∃ v, HasDerivAt (fun s => L.value h (x s)) v t ∧ δ ≤ v := by
    intro t ht hbelow L hL hval
    have haL := (G.active_iff_minimum h (x t) L).mpr ⟨hL,hval.symm⟩
    exact ⟨dot L.slope (massAction N k (x t)),
      (hasDerivAt_dot_curve L.slope (hx.2 t (ha.trans ht.1))).add_const (L.offset h),
      G.active_drift k h lower D hweak hh hh1 hsmall hlower hk hmargin hdegree
        (x t) (hbox t ht.1) L haL
        (P.nonannihilator_below (x t) (hc t (ha.trans ht.1)) hbelow L haL)⟩
  have hentry := finite_minimum_plateau_entry G.certificate.labels G.certificate.nonempty
    (fun L t => L.value h (x t)) a b P.level δ hab hδ
    (fun L _ t ht =>
      ((hasDerivAt_dot_curve L.slope (hx.2 t (ha.trans ht.1))).add_const
        (L.offset h)).continuousAt.continuousWithinAt)
    (fun t _ => P.ceiling (x t)) hnonneg hspeed (by
      dsimp only [b]
      rw [add_sub_cancel_left,mul_div_cancel₀ _ hδ.ne']
      exact le_rfl)
  refine ⟨b,hab,rfl,?_⟩
  exact global_solution_stays
    (P.invariant k lower D hweak hh hh1 hsmall hlower hk hmargin hdegree)
    hx b (ha.trans hab) ((P.mem_iff (x b)).mpr hentry)

end
end ReverseRateLimits

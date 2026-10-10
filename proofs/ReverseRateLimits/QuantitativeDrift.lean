module
public import proofs.ReverseRateLimits.RateBounds
public import proofs.ReverseRateLimits.Upstream.MassActionFlux

@[expose] public section

namespace ReverseRateLimits
open scoped BigOperators
open OAI.Problem326.CutFlux

/-- Full crossed-cut margin, obtained from a selected upward edge and the
source-order separation. Empty downward cuts are included automatically. -/
theorem crossed_cut_lower {V E : Type*} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (k : E → ℝ) (gap L floor c : ℝ)
    (hL : 0 ≤ L) (hk : ∀ e, 0 ≤ k e) (hkl : ∀ e, L ≤ k e)
    (hw : ∀ e, 0 ≤ w (s e)) (hfloor : ∀ e, floor ≤ w (s e))
    (hgap : 0 ≤ gap) (hmargin : gap*(∑ e, k e) ≤ L/2)
    (horder : ∀ e f, a (s e) < a (s f) → w (s f) ≤ gap*w (s e))
    (f : E) (hf : a (s f) ≤ c ∧ c < a (t f)) :
    (L/2)*floor ≤
      (∑ e ∈ Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e)), k e*w (s e))-
      (∑ e ∈ Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e)), k e*w (s e)) := by
  classical
  let U := Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e))
  let D := Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e))
  have hup : L*w (s f) ≤ ∑ e ∈ U, k e*w (s e) := by
    apply (mul_le_mul_of_nonneg_right (hkl f) (hw f)).trans
    exact Finset.single_le_sum (fun e _ => mul_nonneg (hk e) (hw e))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩)
  have hdown : (∑ e ∈ D, k e*w (s e)) ≤ (L/2)*w (s f) := by
    calc
      (∑ e ∈ D, k e*w (s e)) ≤ ∑ e ∈ D, k e*(gap*w (s f)) := by
        apply Finset.sum_le_sum
        intro e he
        have hed := (Finset.mem_filter.mp he).2
        exact mul_le_mul_of_nonneg_left
          (horder f e (hf.1.trans_lt hed.2)) (hk e)
      _ = (gap*w (s f))*(∑ e ∈ D, k e) := by rw [← Finset.sum_mul]; ring
      _ ≤ (gap*w (s f))*(∑ e, k e) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hgap (hw f))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
          (fun e _ _ => hk e)
      _ ≤ (L/2)*w (s f) := by
        have h := mul_le_mul_of_nonneg_right hmargin (hw f)
        nlinarith only [h]
  exact quantitative_cut _ _ L (w (s f)) floor hL hup hdown (hfloor f)

/-- Subtracting one edge credit reduces quantitative work to the already
proved nonnegative threshold-cut theorem. This avoids a new integration proof. -/
theorem work_lower_of_cut_credit {E : Type*} [Fintype E]
    (s t q : E → ℝ) (m : ℝ) (e₀ : E) (he : s e₀ < t e₀)
    (hcut : ∀ c,
      0 ≤ (∑ e ∈ Finset.univ.filter (fun e => s e ≤ c ∧ c < t e), q e)-
        (∑ e ∈ Finset.univ.filter (fun e => t e ≤ c ∧ c < s e), q e))
    (hcredit : ∀ c, s e₀ ≤ c ∧ c < t e₀ →
      m ≤ (∑ e ∈ Finset.univ.filter (fun e => s e ≤ c ∧ c < t e), q e)-
        (∑ e ∈ Finset.univ.filter (fun e => t e ≤ c ∧ c < s e), q e)) :
    m*(t e₀-s e₀) ≤ ∑ e, q e*(t e-s e) := by
  classical
  let q' : E → ℝ := fun e => q e - if e = e₀ then m else 0
  have hcut' : ∀ c,
      0 ≤ (∑ e ∈ Finset.univ.filter (fun e => s e ≤ c ∧ c < t e), q' e)-
        (∑ e ∈ Finset.univ.filter (fun e => t e ≤ c ∧ c < s e), q' e) := by
    intro c
    have hdown : ¬ (t e₀ ≤ c ∧ c < s e₀) := by intro h; linarith
    simp only [q',Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_filter,
      Finset.mem_univ,true_and, hdown, ite_false,sub_zero]
    by_cases hc : s e₀ ≤ c ∧ c < t e₀
    · simp [hc]
      linarith [hcredit c hc]
    · simp only [hc,ite_false,sub_zero]
      exact hcut c
  have hwork := weighted_difference_nonneg_of_threshold_flux s t q' hcut'
  simp only [q',sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] at hwork
  linarith

/-- Positive active work with the stated monomial floor and one separated
upward edge. All zero or tied level cuts are retained in the proof. -/
theorem total_drift_of_upward_edge {V E : Type*} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (k : E → ℝ) (gap L floor H : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hL : 0 < L) (hkl : ∀ e, L ≤ k e)
    (hfloor0 : 0 ≤ floor) (hfloor : ∀ e, floor ≤ w (s e))
    (hgap : 0 ≤ gap) (hmargin : gap*(∑ e, k e) ≤ L/2)
    (horder : ∀ e f, a (s e) < a (s f) → w (s f) ≤ gap*w (s e))
    (e₀ : E) (he₀ : a (s e₀) < a (t e₀)) (hsep : 2*H ≤ a (t e₀)-a (s e₀)) :
    H*L*floor ≤ ∑ e, k e*w (s e)*(a (t e)-a (s e)) := by
  have hk : ∀ e, 0 < k e := fun e => hL.trans_le (hkl e)
  have hrate : ∀ e, gap*(∑ f, k f) < k e := by
    intro e
    have hl := hkl e
    linarith
  have hwork := work_lower_of_cut_credit (fun e => a (s e)) (fun e => a (t e))
    (fun e => k e*w (s e)) ((L/2)*floor) e₀ he₀
    (threshold_flux_nonneg_of_source_order s t a w k gap hreturn hw hk hgap horder hrate)
    (fun c hc => crossed_cut_lower s t a w k gap L floor c hL.le (fun e => (hk e).le)
      hkl (fun e => (hw (s e)).le) hfloor hgap hmargin horder e₀ hc)
  have hm : 0 ≤ (L/2)*floor := mul_nonneg (by positivity) hfloor0
  have hsep' := mul_le_mul_of_nonneg_left hsep hm
  calc
    H*L*floor = ((L/2)*floor)*(2*H) := by ring
    _ ≤ ((L/2)*floor)*(a (t e₀)-a (s e₀)) := hsep'
    _ ≤ ∑ e, k e*w (s e)*(a (t e)-a (s e)) := hwork

open OAI.Problem326

/-- Exact mass-action instance of the quantitative cut theorem. A direction
outside the stoichiometric annihilator supplies an upward edge by return paths. -/
theorem massAction_quantitative_drift {d : ℕ} (N : ReactionNetwork d)
    (k : Reaction N → ℝ) (x r : Fin d → ℝ) (gap L floor H : ℝ)
    (hweak : WeaklyReversible N) (hx : PositiveState x) (hL : 0 < L)
    (hk : ∀ e, L ≤ k e) (hfloor0 : 0 ≤ floor)
    (hfloor : ∀ e : Reaction N, floor ≤ monomial x e.val.1)
    (hgap : 0 ≤ gap) (hmargin : gap*(∑ e, k e) ≤ L/2)
    (horder : ∀ y ∈ N.complexes, ∀ z ∈ N.complexes,
      dot r (fun i => (y i:ℝ)) < dot r (fun i => (z i:ℝ)) →
        monomial x z ≤ gap*monomial x y)
    (hsep : ∀ e : Reaction N,
      dot r (fun i => (e.val.2 i:ℝ))-dot r (fun i => (e.val.1 i:ℝ)) ≠ 0 →
        2*H ≤ |dot r (fun i => (e.val.2 i:ℝ))-dot r (fun i => (e.val.1 i:ℝ))|)
    (hnonzero : ∃ e : Reaction N,
      dot r (fun i => (e.val.2 i:ℝ))-dot r (fun i => (e.val.1 i:ℝ)) ≠ 0) :
    H*L*floor ≤ dot r (massAction N k x) := by
  classical
  let s : Reaction N → (Fin d → ℕ) := fun e => e.val.1
  let t : Reaction N → (Fin d → ℕ) := fun e => e.val.2
  let a : (Fin d → ℕ) → ℝ := fun y => dot r (fun i => (y i:ℝ))
  have hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f : Reaction N, s f = u ∧ t f = v) (t e) (s e) := by
    intro e
    apply Relation.TransGen.mono (r := HasReaction N) ?_ _ _ (hweak e)
    intro y z he
    exact ⟨⟨(y,z),he⟩,rfl,rfl⟩
  have hup : ∃ e, a (s e) < a (t e) := by
    obtain ⟨e,he⟩ := hnonzero
    change a (t e)-a (s e) ≠ 0 at he
    rcases lt_or_gt_of_ne he with he | he
    · have hdown : a (t e) ≤ a (t e) ∧ a (t e) < a (s e) := ⟨le_rfl,by linarith⟩
      obtain ⟨f,hf⟩ := upward_of_downward s t a hreturn (a (t e)) e hdown
      exact ⟨f,hf.1.trans_lt hf.2⟩
    · exact ⟨e,by linarith⟩
  obtain ⟨e,he⟩ := hup
  have hsep' : 2*H ≤ a (t e)-a (s e) := by
    have h := hsep e (by change a (t e)-a (s e) ≠ 0; linarith)
    change 2*H ≤ |a (t e)-a (s e)| at h
    rwa [abs_of_pos (sub_pos.mpr he)] at h
  rw [dot_massAction_eq_flux]
  exact total_drift_of_upward_edge s t a (monomial x) k gap L floor H hreturn
    (fun y => Finset.prod_pos (fun i _ => pow_pos (hx i) (y i))) hL hk hfloor0 hfloor
    hgap hmargin
    (fun e f hef => horder e.val.1 (N.source_mem _ e.property)
      f.val.1 (N.source_mem _ f.property) hef) e he hsep'

end ReverseRateLimits

module
public import proofs.ReverseRateLimits.ScaleEntry

@[expose] public section

namespace ReverseRateLimits
open Set Filter OAI.Problem326
open scoped Topology
noncomputable section

def dyadicScale (target : ℝ) (n : ℕ) : ℝ := target^(2^n)

theorem dyadicScale_pos {target : ℝ} (ht : 0 < target) (n : ℕ) :
    0 < dyadicScale target n := pow_pos ht _

theorem dyadicScale_le {target : ℝ} (ht : 0 ≤ target) (ht1 : target ≤ 1) (n : ℕ) :
    dyadicScale target n ≤ target := by
  simpa only [dyadicScale,pow_one] using
    (pow_le_pow_of_le_one ht ht1 (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by decide : (2:ℕ) ≠ 0))))

theorem dyadicScale_sqrt {target : ℝ} (ht : 0 ≤ target) (n : ℕ) :
    (dyadicScale target (n+1))^(1/2:ℝ) = dyadicScale target n := by
  unfold dyadicScale
  rw [pow_succ,pow_mul,← Real.sqrt_eq_rpow,Real.sqrt_sq (pow_nonneg ht _)]

theorem dyadicScale_tendsto {target : ℝ} (ht : 0 < target) (ht1 : target < 1) :
    Tendsto (dyadicScale target) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨(tendsto_pow_atTop_nhds_zero_of_lt_one ht.le ht1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1:ℕ) < 2)),
    Filter.Eventually.of_forall (dyadicScale_pos ht)⟩

theorem initial_mem_of_active_zero {d : ℕ} {N : ReactionNetwork d}
    {G : NetworkGeometry N} {c : Fin d → ℝ} {h : ℝ}
    (P : ScalePlateau G c h) (x : Fin d → ℝ)
    (hzero : ∀ L, Affine.Active G.certificate.labels L h x → L.slope = 0) : x ∈ P.set := by
  obtain ⟨L,ha⟩ := Affine.exists_active G.certificate.labels G.certificate.nonempty h x
  have hz := hzero L ha
  have hLvalue : L.value h x = L.offset h := by simp [Affine.Label.value,hz]
  have hcle : P.level ≤ L.offset h := by
    have h := P.contains_c L ha.1
    simpa [ScalePlateau.level,Affine.Label.value,hz] using h
  have hupper : L.offset h ≤ P.level := by
    have h := ha.2 P.constant P.active_c.1
    simpa [ScalePlateau.level,Affine.Label.value,hz,P.zero] using h
  intro J hJ
  have hj := ha.2 J hJ
  rw [hLvalue,le_antisymm hupper hcle] at hj
  exact hj

/-- Finite descent through reciprocal boxes. Each old invariant plateau
supplies residence for the next scale; no ordering of plateaux is assumed. -/
theorem dyadic_plateau_descent {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (c : Fin d → ℝ) (target : ℝ)
    (htarget : 0 < target) (htarget1 : target < 1)
    (P : ∀ n, ScalePlateau G c (dyadicScale target n))
    (k : Reaction N → ℝ) (lower : ℝ) (D : ℕ)
    (hweak : WeaklyReversible N) (hlower : 0 < lower) (hk : ∀ e, lower ≤ k e)
    (hsmall : ∀ n, dyadicScale target n < G.hmax)
    (hmargin : ∀ n, (dyadicScale target n)^G.H*(∑ e, k e) ≤ lower/2)
    (hdegree : ∀ e : Reaction N, ∑ i, e.val.1 i ≤ D)
    (x0 : Fin d → ℝ) (hclass : SameClass N c x0)
    (x : ℝ → Fin d → ℝ) (hx : IsGlobalForwardSolution N k x0 x) :
    ∀ n, (∃ a, 0 ≤ a ∧ ∀ t, a ≤ t → x t ∈ (P n).set) →
      ∃ b, 0 ≤ b ∧ ∀ t, b ≤ t → x t ∈ (P 0).set := by
  intro n
  induction n with
  | zero => exact id
  | succ n ih =>
    rintro ⟨a,ha,hstay⟩
    have hbox : ∀ t, a ≤ t →
        x t ∈ Icc (fun _ => dyadicScale target n) (fun _ => (dyadicScale target n)⁻¹) := by
      intro t ht
      have h := (P (n+1)).inside_sqrt_box (dyadicScale_pos htarget _)
        ((dyadicScale_le htarget.le htarget1.le _).trans_lt htarget1)
        (hsmall _) (x t) (hstay t ht)
      simpa only [dyadicScale_sqrt htarget.le] using h
    obtain ⟨b,hab,_,hb⟩ := (P n).entry k lower D hweak (dyadicScale_pos htarget _)
      ((dyadicScale_le htarget.le htarget1.le _).trans_lt htarget1)
      (hsmall n) hlower hk (hmargin n) hdegree x0 hclass x hx a ha hbox
    exact ih ⟨b,ha.trans hab,hb⟩

end
end ReverseRateLimits

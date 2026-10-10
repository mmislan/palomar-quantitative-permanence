module
public import proofs.ReverseRateLimits.UniformGeometry
public import proofs.ReverseRateLimits.RateBounds

@[expose] public section

namespace ReverseRateLimits
open Set Filter OAI.Problem326
open scoped Topology BigOperators
noncomputable section

theorem exists_geometric_threshold {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (c : Fin d → ℝ) :
    ∃ q, 0 < q ∧ ∀ h, 0 < h → h ≤ q → h < G.hmax ∧ h < 1 ∧
      ∀ i, |Real.log (c i)/Real.log h| < G.H := by
  have hlogs : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i, |Real.log (c i)/Real.log h| < G.H := by
    apply Filter.eventually_all.mpr
    intro i
    have hlim : Tendsto (fun h => |Real.log (c i)/Real.log h|) (𝓝[>] 0) (𝓝 0) := by
      simpa only [abs_zero] using (tendsto_log_coordinate_div_log (c i)).abs
    exact hlim.eventually_lt_const G.H_pos
  have hmax : ∀ᶠ h : ℝ in 𝓝[>] 0, h < G.hmax :=
    nhdsWithin_le_nhds (Iio_mem_nhds G.hmax_pos)
  have hone : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  obtain ⟨q,hq,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hmax.and (hone.and hlogs))
  refine ⟨q/2,div_pos hq (by norm_num),?_⟩
  intro h hh hle
  exact hsub ⟨hh,by linarith⟩

/-- A depends on the fixed geometry, class representative and prefactor
box, before exponents or epsilon are supplied. Empty reaction sets are allowed. -/
theorem exists_rate_scale_constant {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (c : Fin d → ℝ) (lower upper : ℝ)
    (hlower : 0 < lower) :
    ∃ A, 0 < A ∧ A < 1 ∧
      (∀ h, 0 < h → h ≤ A → h < G.hmax ∧ h < 1 ∧
        ∀ i, |Real.log (c i)/Real.log h| < G.H) ∧
      A^G.H*((Fintype.card (Reaction N):ℝ)*upper) ≤ lower/2 := by
  obtain ⟨q,hq,hgeo⟩ := exists_geometric_threshold G c
  have hpow := (tendsto_positive_rpow_nhdsGT_zero G.H_pos).mul_const
    ((Fintype.card (Reaction N):ℝ)*upper)
  have hmargin : ∀ᶠ h : ℝ in 𝓝[>] 0,
      h^G.H*((Fintype.card (Reaction N):ℝ)*upper) < lower/2 := by
    have hlim : Tendsto (fun h : ℝ => h^G.H*((Fintype.card (Reaction N):ℝ)*upper))
        (𝓝[>] 0) (𝓝 0) := by simpa using hpow
    exact hlim.eventually_lt_const (by positivity)
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < q :=
    nhdsWithin_le_nhds (Iio_mem_nhds hq)
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  obtain ⟨A,hA,hAq,hAmargin⟩ := (hpositive.and (hsmall.and hmargin)).exists
  refine ⟨A,hA,(hgeo A hA hAq.le).2.1,?_,hAmargin.le⟩
  exact fun h hh hle => hgeo h hh (hle.trans hAq.le)

theorem power_rate_margin {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (A epsilon lower upper amin amax : ℝ)
    (prefactor exponent : Reaction N → ℝ)
    (hA : 0 < A) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hlower : 0 < lower) (_hupper : 0 ≤ upper) (hspread : amin ≤ amax)
    (hbox : ∀ e, lower ≤ prefactor e ∧ prefactor e ≤ upper)
    (hexponent : ∀ e, amin ≤ exponent e ∧ exponent e ≤ amax)
    (hAmargin : A^G.H*((Fintype.card (Reaction N):ℝ)*upper) ≤ lower/2) :
    let target := A*epsilon^((amax-amin)/G.H)
    let k := fun e => rate epsilon (prefactor e) (exponent e)
    (0 < target ∧ target ≤ A) ∧
      (∀ e, lower*epsilon^amax ≤ k e) ∧
      ∀ h, 0 < h → h ≤ target → h^G.H*(∑ e, k e) ≤ (lower*epsilon^amax)/2 := by
  let target := A*epsilon^((amax-amin)/G.H)
  let k := fun e => rate epsilon (prefactor e) (exponent e)
  have htarget : 0 < target := mul_pos hA (Real.rpow_pos_of_pos hepsilon _)
  have htargetA : target ≤ A := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hepsilon.le hepsilon1 (div_nonneg (sub_nonneg.mpr hspread) G.H_pos.le)) hA.le
  have hbounds := fun e => rate_bounds epsilon (prefactor e) (exponent e) amin amax lower upper
    hepsilon hepsilon1 hlower.le (hbox e).1 (hbox e).2 (hexponent e).1 (hexponent e).2
  have hsum : (∑ e, k e) ≤ (Fintype.card (Reaction N):ℝ)*upper*epsilon^amin := by
    have h := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => (hbounds e).2)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using h
  have hsum0 : 0 ≤ ∑ e, k e := Finset.sum_nonneg (fun e _ =>
    (mul_pos hlower (Real.rpow_pos_of_pos hepsilon amax)).le.trans (hbounds e).1)
  refine ⟨⟨htarget,htargetA⟩,fun e => (hbounds e).1,?_⟩
  intro h hh hle
  calc
    h^G.H*(∑ e, k e) ≤ target^G.H*(∑ e, k e) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hh.le hle G.H_pos.le) hsum0
    _ ≤ target^G.H*((Fintype.card (Reaction N):ℝ)*upper*epsilon^amin) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg htarget.le _)
    _ = (A^G.H*((Fintype.card (Reaction N):ℝ)*upper))*epsilon^amax := by
      rw [scale_power_identity A epsilon G.H (amax-amin) hA.le hepsilon.le G.H_pos.ne']
      rw [show A^G.H*epsilon^(amax-amin)*((Fintype.card (Reaction N):ℝ)*upper*epsilon^amin) =
        (A^G.H*((Fintype.card (Reaction N):ℝ)*upper))*(epsilon^(amax-amin)*epsilon^amin) by ring]
      rw [← Real.rpow_add hepsilon,sub_add_cancel]
    _ ≤ (lower/2)*epsilon^amax :=
      mul_le_mul_of_nonneg_right hAmargin (Real.rpow_nonneg hepsilon.le _)
    _ = (lower*epsilon^amax)/2 := by ring

end
end ReverseRateLimits

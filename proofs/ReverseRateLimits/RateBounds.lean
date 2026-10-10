module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

namespace ReverseRateLimits
open scoped BigOperators

/-- Actual rates, with arbitrary bounded prefactors depending on the parameter. -/
noncomputable def rate (epsilon prefactor exponent : ℝ) : ℝ :=
  prefactor * epsilon ^ exponent

theorem rate_bounds (epsilon prefactor exponent amin amax lower upper : ℝ)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hl : 0 ≤ lower) (hlp : lower ≤ prefactor) (hpu : prefactor ≤ upper)
    (hmin : amin ≤ exponent) (hmax : exponent ≤ amax) :
    lower * epsilon ^ amax ≤ rate epsilon prefactor exponent ∧
      rate epsilon prefactor exponent ≤ upper * epsilon ^ amin := by
  have hp : 0 ≤ prefactor := hl.trans hlp
  have hpowmax : epsilon ^ amax ≤ epsilon ^ exponent :=
    Real.rpow_le_rpow_of_exponent_ge he he1 hmax
  have hpowmin : epsilon ^ exponent ≤ epsilon ^ amin :=
    Real.rpow_le_rpow_of_exponent_ge he he1 hmin
  constructor
  · exact (mul_le_mul_of_nonneg_left hpowmax hl).trans
      (mul_le_mul_of_nonneg_right hlp (Real.rpow_nonneg he.le _))
  · exact (mul_le_mul_of_nonneg_right hpu (Real.rpow_nonneg he.le _)).trans
      (mul_le_mul_of_nonneg_left hpowmin (hp.trans hpu))

/-- The chosen power of epsilon cancels precisely the relative rate spread. -/
theorem scale_power_identity (A epsilon H delta : ℝ)
    (hA : 0 ≤ A) (he : 0 ≤ epsilon) (hH : H ≠ 0) :
    (A * epsilon ^ (delta / H)) ^ H = A ^ H * epsilon ^ delta := by
  rw [Real.mul_rpow hA (Real.rpow_nonneg he _), ← Real.rpow_mul he]
  congr 2
  field_simp

/-- Factor-two margin for finite sums; the rate and scale bounds are explicit. -/
theorem cut_margin_of_bounds {ι : Type*} [Fintype ι]
    (k : ι → ℝ) (gap total lower : ℝ)
    (hg : 0 ≤ gap) (hsum : (∑ e, k e) ≤ total)
    (hmargin : gap * total ≤ lower / 2) (hk : ∀ e, lower ≤ k e) :
    ∀ e, gap * (∑ f, k f) ≤ k e / 2 := by
  intro e
  have hb := mul_le_mul_of_nonneg_left hsum hg
  linarith [hk e]

/-- A selected upward edge pays all downward flux with a retained numerical margin. -/
theorem quantitative_cut (up down lower weight floor : ℝ)
    (hl : 0 ≤ lower)
    (hup : lower * weight ≤ up)
    (hdown : down ≤ (lower / 2) * weight)
    (hfloor : floor ≤ weight) :
    (lower / 2) * floor ≤ up - down := by
  have hm := mul_le_mul_of_nonneg_left hfloor (show 0 ≤ lower / 2 by positivity)
  nlinarith

end ReverseRateLimits

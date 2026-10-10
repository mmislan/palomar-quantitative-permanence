module
public import proofs.ReverseRateLimits.RecoveryCorollaries

@[expose] public section

namespace ReverseRateLimits.ExponentFamily
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem RecoveryCorollaries
noncomputable section

def hExponent (gamma : ℝ) : ℝ := (2*gamma-1)/12
def uExponent (gamma : ℝ) : ℝ := (7-2*gamma)/12
def xExponent (gamma : ℝ) : ℝ := (2*gamma+1)/4
def yExponent (gamma : ℝ) : ℝ := (gamma+1)/3
def zExponent (gamma : ℝ) : ℝ := (2*gamma+5)/12
def timeExponent (gamma : ℝ) : ℝ := (14*gamma+5)/12
def cutoff (gamma : ℝ) : ℝ :=
  (1/1000:ℝ) ^ (12/min (2*gamma-1) (7-2*gamma))
def improvedCutoff (gamma : ℝ) : ℝ :=
  min ((1/600:ℝ) ^ (12/(2*gamma-1))) ((1/20:ℝ) ^ (12/(7-2*gamma)))

theorem power_product (epsilon a b : ℝ) (n : ℕ) (he : 0 < epsilon) :
    epsilon^a*(epsilon^b)^n = epsilon^(a+b*n) := by
  rw [← Real.rpow_mul_natCast he.le,← Real.rpow_add he]

theorem identities (epsilon gamma : ℝ) (he : 0 < epsilon)
    (P : Parameters) (hh : P.h=epsilon^(hExponent gamma))
    (hu : P.u=epsilon^(uExponent gamma)) :
    P.p=epsilon^(1/2:ℝ) ∧ P.p^2=epsilon ∧ P.p*P.h^6=epsilon^gamma ∧
      sx P=epsilon^(xExponent gamma) ∧ sy P=epsilon^(yExponent gamma) ∧
      sz P=epsilon^(zExponent gamma) ∧ P.p^2*P.h^7=epsilon^(timeExponent gamma) := by
  have hp : P.p=epsilon^(1/2:ℝ) := by
    unfold Parameters.p
    rw [hu,hh,← Real.rpow_add he]
    congr 1
    unfold hExponent uExponent
    ring
  have hp2 : P.p^2=epsilon := by
    rw [hp,← Real.rpow_mul_natCast he.le]
    norm_num
  refine ⟨hp,hp2,?_,?_,?_,?_,?_⟩
  · rw [hp,hh,power_product epsilon _ _ 6 he]
    congr 1
    unfold hExponent
    ring
  · unfold sx
    rw [hp,hh,power_product epsilon _ _ 3 he]
    congr 1
    unfold hExponent xExponent
    ring
  · unfold sy
    rw [hp,hh,power_product epsilon _ _ 2 he]
    congr 1
    unfold hExponent yExponent
    ring
  · unfold sz
    rw [hp,hh,← Real.rpow_add he]
    congr 1
    unfold hExponent zExponent
    ring
  · rw [hp2,hh]
    conv_lhs => lhs; rw [← Real.rpow_one epsilon]
    rw [power_product epsilon _ _ 7 he]
    congr 1
    unfold hExponent timeExponent
    ring

theorem small_power (epsilon base exponent : ℝ) (he : 0 < epsilon)
    (hb : 0 < base) (ha : 0 < exponent)
    (hcut : epsilon ≤ base^(1/exponent)) : epsilon^exponent ≤ base := by
  have h := Real.rpow_le_rpow he.le hcut ha.le
  rw [← Real.rpow_mul hb.le] at h
  have hid : (1/exponent)*exponent=1 := by field_simp
  simpa only [hid,Real.rpow_one] using h

theorem improved_cutoff_bounds (epsilon gamma : ℝ) (he : 0 < epsilon)
    (hg : (1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ)) (hcut : epsilon ≤ improvedCutoff gamma) :
    epsilon^(hExponent gamma) ≤ (1/600:ℝ) ∧
      epsilon^(uExponent gamma) ≤ (1/20:ℝ) := by
  have hh : 0 < hExponent gamma := by unfold hExponent; linarith [hg.1]
  have hu : 0 < uExponent gamma := by unfold uExponent; linarith [hg.2]
  have hhi := hcut.trans (min_le_left _ _)
  have hui := hcut.trans (min_le_right _ _)
  have e1 : 12/(2*gamma-1)=1/hExponent gamma := by
    simp [hExponent,div_eq_mul_inv,mul_inv_rev]
  have e2 : 12/(7-2*gamma)=1/uExponent gamma := by
    simp [uExponent,div_eq_mul_inv,mul_inv_rev]
  rw [e1] at hhi
  rw [e2] at hui
  exact ⟨small_power epsilon _ _ he (by norm_num) hh hhi,
    small_power epsilon _ _ he (by norm_num) hu hui⟩

theorem original_cutoff_bounds (epsilon gamma : ℝ) (he : 0 < epsilon)
    (hg : (1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ)) (hcut : epsilon ≤ cutoff gamma) :
    epsilon^(hExponent gamma) ≤ (1/1000:ℝ) ∧
      epsilon^(uExponent gamma) ≤ (1/1000:ℝ) := by
  have hm : 0 < min (2*gamma-1) (7-2*gamma) := by
    apply lt_min <;> linarith [hg.1,hg.2]
  have h1 : 0 < 2*gamma-1 := by linarith [hg.1]
  have h2 : 0 < 7-2*gamma := by linarith [hg.2]
  have hbase : (0:ℝ)<1/1000 := by norm_num
  have e1 : 12/(2*gamma-1)=1/hExponent gamma := by
    simp [hExponent,div_eq_mul_inv,mul_inv_rev]
  have e2 : 12/(7-2*gamma)=1/uExponent gamma := by
    simp [uExponent,div_eq_mul_inv,mul_inv_rev]
  have b1 : cutoff gamma ≤ (1/1000:ℝ)^(1/hExponent gamma) := by
    unfold cutoff
    rw [← e1]
    apply Real.rpow_le_rpow_of_exponent_ge hbase (by norm_num)
    exact div_le_div_of_nonneg_left (by norm_num) hm (min_le_left _ _)
  have b2 : cutoff gamma ≤ (1/1000:ℝ)^(1/uExponent gamma) := by
    unfold cutoff
    rw [← e2]
    apply Real.rpow_le_rpow_of_exponent_ge hbase (by norm_num)
    exact div_le_div_of_nonneg_left (by norm_num) hm (min_le_right _ _)
  exact ⟨small_power epsilon _ _ he hbase (by unfold hExponent; linarith) (hcut.trans b1),
    small_power epsilon _ _ he hbase (by unfold uExponent; linarith) (hcut.trans b2)⟩

theorem cutoff_decimal (gamma : ℝ) :
    cutoff gamma = (10:ℝ)^(-36/min (2*gamma-1) (7-2*gamma)) := by
  have hb : (1/1000:ℝ)=(10:ℝ)^(-3:ℝ) := by
    rw [Real.rpow_neg (by norm_num)]
    norm_num
  unfold cutoff
  rw [hb,← Real.rpow_mul (by norm_num : (0:ℝ)≤10)]
  congr 1
  ring

def parameters (template : Parameters) (epsilon gamma : ℝ) (he : 0 < epsilon)
    (hg : (1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ)) (hcut : epsilon ≤ improvedCutoff gamma) : Parameters where
  h := epsilon^(hExponent gamma)
  u := epsilon^(uExponent gamma)
  r := template.r
  hh := ⟨Real.rpow_pos_of_pos he _,(improved_cutoff_bounds epsilon gamma he hg hcut).1⟩
  hu := ⟨Real.rpow_pos_of_pos he _,(improved_cutoff_bounds epsilon gamma he hg hcut).2⟩
  ha1 := template.ha1
  ha2 := template.ha2
  ha3 := template.ha3
  hK := template.hK
  hb1 := template.hb1
  hb2 := template.hb2
  hb3 := template.hb3
  hb4 := template.hb4

theorem family_root (epsilon gamma : ℝ) (he : 0 < epsilon)
    (P : Parameters) (hh : P.h=epsilon^(hExponent gamma))
    (hu : P.u=epsilon^(uExponent gamma)) (x0 : Fin 3 → ℝ)
    (hpos : OAI.Problem326.PositiveState x0) (hprep : Prepared P x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
      (∀ v : LiteralTrajectory P, Starts P x0 v →
        (∀ t, 0 ≤ t →
          ((3/64:ℝ)*epsilon^(xExponent gamma) ≤ v.x t ∧ v.x t ≤ 5*epsilon^(xExponent gamma)) ∧
          ((1/16:ℝ)*epsilon^(yExponent gamma) ≤ v.y t ∧ v.y t ≤ 3*epsilon^(yExponent gamma)) ∧
          ((1/8:ℝ)*epsilon^(zExponent gamma) ≤ v.z t ∧ v.z t ≤ epsilon^(zExponent gamma))) ∧
        (∀ t, 7/epsilon^(timeExponent gamma) ≤ t → Inner (A P v t) (B P v t) (Q P v t))) ∧
      (∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
        ∀ t, 0 ≤ t → Inner (A P v t) (B P v t) (Q P v t) →
          1/(28*epsilon^(timeExponent gamma)) ≤ t) := by
  have hi := identities epsilon gamma he P hh hu
  have hscaleX : P.p*P.h^3=epsilon^(xExponent gamma) := hi.2.2.2.1
  have hscaleY : P.p*P.h^2=epsilon^(yExponent gamma) := hi.2.2.2.2.1
  have hscaleZ : P.p*P.h=epsilon^(zExponent gamma) := hi.2.2.2.2.2.1
  have htime := hi.2.2.2.2.2.2
  have hp := prepared_recovery P x0 hpos hprep
  refine ⟨hp.1,?_,?_⟩
  · simpa only [mul_assoc,hscaleX,hscaleY,hscaleZ,htime] using hp.2
  · simpa only [htime,mul_assoc] using improved_witness P

end
end ReverseRateLimits.ExponentFamily

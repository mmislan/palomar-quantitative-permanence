module
public import proofs.ReverseRateLimits.GeometryActivity
public import proofs.ReverseRateLimits.QuantitativeDrift
public import proofs.ReverseRateLimits.ClassInvariant

@[expose] public section

namespace ReverseRateLimits
open OAI.Problem326
open scoped BigOperators
noncomputable section

theorem monomial_floor {d : ℕ} (h : ℝ) (x : Fin d → ℝ) (y : Fin d → ℕ)
    (D : ℕ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hx : ∀ i, h ≤ x i)
    (hdegree : ∑ i, y i ≤ D) : h^D ≤ monomial x y := by
  calc
    h^D ≤ h^(∑ i, y i) := pow_le_pow_of_le_one hh hh1 hdegree
    _ = ∏ i, h^(y i) := (Finset.prod_pow_eq_pow_sum Finset.univ y h).symm
    _ ≤ ∏ i, (x i)^(y i) := Finset.prod_le_prod₀
      (fun i _ => pow_nonneg hh _) (fun i _ => pow_le_pow_left₀ hh (hx i) _)

theorem NetworkGeometry.active_order {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : h < G.hmax) (p : Fin d → ℝ) (hp : Affine.Cube (-1) 1 p)
    (L : Affine.Label d) (ha : Affine.Active G.certificate.labels L h (Affine.powerPoint h p)) :
    ∀ y ∈ N.complexes, ∀ z ∈ N.complexes,
      dot L.slope (fun i => (y i:ℝ)) < dot L.slope (fun i => (z i:ℝ)) →
      monomial (Affine.powerPoint h p) z ≤ h^G.H * monomial (Affine.powerPoint h p) y := by
  intro y hy z hz hyz
  have hdir : 0 < dot L.slope (BarrierConstruction.complexDifference y z) := by
    rw [BarrierConstruction.dot_complexDifference]
    exact sub_pos.mpr hyz
  have hcontrol := G.sign_close L.slope p (G.active_close h hh hsmall p hp L ha)
    (BarrierConstruction.complexDifference y z)
    (BarrierConstruction.complexDifference_mem N hy hz) hdir.ne'
  have hpositive := hcontrol.1.mpr hdir
  have hgap := G.gap L ha.1 (BarrierConstruction.complexDifference y z)
    (BarrierConstruction.complexDifference_mem N hy hz) hdir.ne'
  have hpgap : G.H ≤ dot p (BarrierConstruction.complexDifference y z) := by
    rw [abs_of_pos hpositive] at hcontrol
    exact (hgap.trans_lt hcontrol.2.2).le
  exact monomial_le_rpow_mul_of_gap hh hh1 p y z hpgap

theorem NetworkGeometry.active_separation {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (L : Affine.Label d) (hL : L ∈ G.certificate.labels)
    (e : Reaction N)
    (hne : dot L.slope (fun i => (e.val.2 i:ℝ))-
      dot L.slope (fun i => (e.val.1 i:ℝ)) ≠ 0) :
    2*G.H ≤ |dot L.slope (fun i => (e.val.2 i:ℝ))-
      dot L.slope (fun i => (e.val.1 i:ℝ))| := by
  have h := G.gap L hL (BarrierConstruction.complexDifference e.val.1 e.val.2)
    (BarrierConstruction.complexDifference_mem N (N.source_mem _ e.property)
      (N.target_mem _ e.property)) (by simpa only [BarrierConstruction.dot_complexDifference] using hne)
  rw [BarrierConstruction.dot_complexDifference] at h
  linarith

/-- Full quantitative drift for every active branch outside the conservation
annihilator. The degree floor follows from the physical box, not a certificate premise. -/
theorem NetworkGeometry.active_drift {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (k : Reaction N → ℝ) (h lower : ℝ) (D : ℕ)
    (hweak : WeaklyReversible N) (hh : 0 < h) (hh1 : h < 1)
    (hsmall : h < G.hmax) (hlower : 0 < lower) (hk : ∀ e, lower ≤ k e)
    (hmargin : h^G.H*(∑ e, k e) ≤ lower/2)
    (hdegree : ∀ e : Reaction N, ∑ i, e.val.1 i ≤ D)
    (x : Fin d → ℝ) (hx : x ∈ Set.Icc (fun _ => h) (fun _ => h⁻¹))
    (L : Affine.Label d) (ha : Affine.Active G.certificate.labels L h x)
    (hnonzero : ¬ Annihilator N L.slope) :
    G.H*lower*h^D ≤ dot L.slope (massAction N k x) := by
  classical
  obtain ⟨hpositive,hcube,hrec⟩ := reciprocal_box_log_coordinates hh hh1 hx
  let p : Fin d → ℝ := fun i => Real.log (x i)/Real.log h
  have hpoint : Affine.powerPoint h p = x := funext hrec
  have hp : Affine.Cube (-1) 1 p := fun i => abs_le.mp (hcube i)
  have ha' : Affine.Active G.certificate.labels L h (Affine.powerPoint h p) := by
    rwa [hpoint]
  exact massAction_quantitative_drift N k x L.slope (h^G.H) lower (h^D) G.H
    hweak hpositive hlower hk (pow_nonneg hh.le _)
    (fun e => monomial_floor h x e.val.1 D hh.le hh1.le hx.1 (hdegree e))
    (Real.rpow_nonneg hh.le _) hmargin
    (by simpa only [hpoint] using G.active_order h hh hh1.le hsmall p hp L ha')
    (G.active_separation L ha.1)
    (by simpa only [Annihilator,not_forall] using hnonzero)

end
end ReverseRateLimits

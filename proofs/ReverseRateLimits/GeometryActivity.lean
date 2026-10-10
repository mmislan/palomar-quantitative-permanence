module
public import proofs.ReverseRateLimits.UniformGeometry
public import proofs.ReverseRateLimits.Upstream.ReciprocalBox

@[expose] public section

namespace ReverseRateLimits
open OAI.Problem326
open scoped BigOperators
noncomputable section

theorem NetworkGeometry.active_close {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (h : ℝ) (hh : 0 < h) (hsmall : h < G.hmax)
    (p : Fin d → ℝ) (hp : Affine.Cube (-1) 1 p) (L : Affine.Label d)
    (ha : Affine.Active G.certificate.labels L h (Affine.powerPoint h p)) :
    ∀ i, |p i-L.slope i| < G.E L.slope := by
  have hb := G.uniform h hh hsmall p hp L ha.1 ha
  intro i
  have hi := (pi_norm_lt_iff (G.E_pos L.slope)).mp hb i
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using hi

theorem NetworkGeometry.active_slope_zero {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (h : ℝ) (hh : 0 < h) (hsmall : h < G.hmax)
    (p : Fin d → ℝ) (hp : ∀ i, |p i| < G.H) (L : Affine.Label d)
    (ha : Affine.Active G.certificate.labels L h (Affine.powerPoint h p)) : L.slope = 0 := by
  have hpcube : Affine.Cube (-1) 1 p := fun i =>
    abs_le.mp ((hp i).le.trans G.H_one)
  have hclose := G.active_close h hh hsmall p hpcube L ha
  have hcontrol := G.sign_close L.slope p hclose
  ext i
  by_contra hn
  have hd : dot L.slope (BarrierConstruction.coordinateDirection i) ≠ 0 := by simpa using hn
  have hgap := G.gap L ha.1 (BarrierConstruction.coordinateDirection i)
    (BarrierConstruction.coordinateDirection_mem N i) hd
  have hcoord := hcontrol (BarrierConstruction.coordinateDirection i)
    (BarrierConstruction.coordinateDirection_mem N i) hd
  have hlow : G.H < |p i| := by
    simpa only [BarrierConstruction.dot_coordinateDirection] using hgap.trans_lt hcoord.2.2
  exact (not_lt_of_ge (hp i).le) hlow

theorem NetworkGeometry.active_zero_inside_half {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (h : ℝ) (hh : 0 < h) (hsmall : h < G.hmax)
    (p : Fin d → ℝ) (hp : Affine.Cube (-1) 1 p) (L : Affine.Label d)
    (ha : Affine.Active G.certificate.labels L h (Affine.powerPoint h p))
    (hzero : L.slope = 0) : ∀ i, |p i| < (1/2:ℝ) := by
  have hc := G.active_close h hh hsmall p hp L ha
  intro i
  have hi := hc i
  simp only [hzero,Pi.zero_apply,sub_zero] at hi
  exact hi.trans_le (G.E_half 0)

end
end ReverseRateLimits

module
public import proofs.ReverseRateLimits.GeometryDrift
public import proofs.ReverseRateLimits.Upstream.AffinePolytope
public import proofs.ReverseRateLimits.Upstream.AffineTrajectory
public import proofs.ReverseRateLimits.Upstream.BarrierTrapping
public import proofs.ReverseRateLimits.Upstream.CompactContinuation

@[expose] public section

namespace ReverseRateLimits
open Set OAI.Problem326
noncomputable section

def NetworkGeometry.minimum {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (h : ℝ) (x : Fin d → ℝ) : ℝ :=
  G.certificate.labels.inf' G.certificate.nonempty (fun L => L.value h x)

theorem NetworkGeometry.active_iff_minimum {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (h : ℝ) (x : Fin d → ℝ) (L : Affine.Label d) :
    Affine.Active G.certificate.labels L h x ↔
      L ∈ G.certificate.labels ∧ L.value h x = G.minimum h x := by
  constructor
  · intro ha
    exact ⟨ha.1,le_antisymm
      (Finset.le_inf' G.certificate.nonempty _ ha.2)
      (Finset.inf'_le _ ha.1)⟩
  · rintro ⟨hL,hval⟩
    exact ⟨hL,fun J hJ => hval ▸ Finset.inf'_le _ hJ⟩

/-- Geometric plateau data are constructed from the fixed affine bank.
Rates, trajectories and absorption are absent from the structure. -/
structure ScalePlateau {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (c : Fin d → ℝ) (h : ℝ) where
  constant : Affine.Label d
  active_c : Affine.Active G.certificate.labels constant h c
  zero : constant.slope = 0
  compact : IsCompact (Affine.labelPolytope G.certificate.labels h (constant.offset h))
  convex : Convex ℝ (Affine.labelPolytope G.certificate.labels h (constant.offset h))
  contains_c : c ∈ Affine.labelPolytope G.certificate.labels h (constant.offset h)
  inside : Affine.labelPolytope G.certificate.labels h (constant.offset h) ⊆
    interior (Icc (fun _ => h) (fun _ => h⁻¹))

def ScalePlateau.set {d : ℕ} {N : ReactionNetwork d} {G : NetworkGeometry N}
    {c : Fin d → ℝ} {h : ℝ} (P : ScalePlateau G c h) : Set (Fin d → ℝ) :=
  Affine.labelPolytope G.certificate.labels h (P.constant.offset h)

def ScalePlateau.level {d : ℕ} {N : ReactionNetwork d} {G : NetworkGeometry N}
    {c : Fin d → ℝ} {h : ℝ} (P : ScalePlateau G c h) : ℝ := P.constant.offset h

theorem exists_scalePlateau {d : ℕ} {N : ReactionNetwork d}
    (G : NetworkGeometry N) (c : Fin d → ℝ) (hc : PositiveState c)
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) (hsmall : h < G.hmax)
    (hlogs : ∀ i, |Real.log (c i)/Real.log h| < G.H) :
    Nonempty (ScalePlateau G c h) := by
  let B : Set (Fin d → ℝ) := Icc (fun _ => h) (fun _ => h⁻¹)
  have hcB : c ∈ interior B := mem_interior_coordinate_box_iff.mpr
    (fun i => (abs_log_coordinate_lt_one_iff hh hh1 (hc i)).mp
      ((hlogs i).trans_le G.H_one))
  have hboundary : ∀ x ∈ frontier B, ∀ L,
      Affine.Active G.certificate.labels L h x → L.slope ≠ 0 := by
    intro x hx L ha hzero
    have hxB : x ∈ B := isClosed_Icc.frontier_subset hx
    obtain ⟨_,hp,hrec⟩ := reciprocal_box_log_coordinates hh hh1 hxB
    obtain ⟨i,hi⟩ := reciprocal_box_frontier_coordinate hh hh1 hx
    have hpoint : Affine.powerPoint h (fun i => Real.log (x i)/Real.log h) = x := funext hrec
    have ha' : Affine.Active G.certificate.labels L h
        (Affine.powerPoint h (fun i => Real.log (x i)/Real.log h)) := by rwa [hpoint]
    have hl := G.active_zero_inside_half h hh hsmall _ (fun i => abs_le.mp (hp i)) L ha' hzero i
    rw [hi] at hl
    norm_num at hl
  have hinitial : ∀ L, Affine.Active G.certificate.labels L h c → L.slope = 0 := by
    intro L ha
    have hpoint : Affine.powerPoint h (fun i => Real.log (c i)/Real.log h) = c :=
      funext (fun i => rpow_log_ratio hh hh1 (hc i))
    apply G.active_slope_zero h hh hsmall _ hlogs L
    rwa [hpoint]
  obtain ⟨L,ha,hzero,hcompact,hconv,_,hcK,hinside⟩ :=
    Affine.exists_compact_labelPolytope G.certificate.labels G.certificate.nonempty h
      B c (isCompact_reciprocal_box h) hcB hinitial hboundary
  exact ⟨⟨L,ha,hzero,hcompact,hconv,hcK,hinside⟩⟩

theorem ScalePlateau.ceiling {d : ℕ} {N : ReactionNetwork d} {G : NetworkGeometry N}
    {c : Fin d → ℝ} {h : ℝ} (P : ScalePlateau G c h) (x : Fin d → ℝ) :
    G.minimum h x ≤ P.level := by
  have hle := Finset.inf'_le (fun L => L.value h x) P.active_c.1
  simpa only [NetworkGeometry.minimum,ScalePlateau.level,Affine.Label.value,P.zero,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add] using hle

theorem ScalePlateau.mem_iff {d : ℕ} {N : ReactionNetwork d} {G : NetworkGeometry N}
    {c : Fin d → ℝ} {h : ℝ} (P : ScalePlateau G c h) (x : Fin d → ℝ) :
    x ∈ P.set ↔ G.minimum h x = P.level := by
  constructor
  · intro hx
    exact le_antisymm (P.ceiling x) (Finset.le_inf' G.certificate.nonempty _ hx)
  · intro hx L hL
    have hi := Finset.inf'_le (fun J => J.value h x) hL
    change G.minimum h x ≤ L.value h x at hi
    simpa only [hx,ScalePlateau.level] using hi

theorem ScalePlateau.active_constant {d : ℕ} {N : ReactionNetwork d} {G : NetworkGeometry N}
    {c : Fin d → ℝ} {h : ℝ} (P : ScalePlateau G c h) (x : Fin d → ℝ) (hx : x ∈ P.set) :
    Affine.Active G.certificate.labels P.constant h x :=
  (Affine.labelPolytope_active_iff P.active_c.1 P.zero hx).mpr
    ⟨P.active_c.1,by simp [Affine.Label.value,P.zero]⟩

theorem ScalePlateau.nonannihilator_below {d : ℕ} {N : ReactionNetwork d}
    {G : NetworkGeometry N} {c : Fin d → ℝ} {h : ℝ}
    (P : ScalePlateau G c h) (x : Fin d → ℝ) (hclass : SameClass N c x)
    (hbelow : G.minimum h x < P.level) (L : Affine.Label d)
    (ha : Affine.Active G.certificate.labels L h x) : ¬ Annihilator N L.slope := by
  intro hann
  have heq : L.value h x = L.value h c := by
    change dot L.slope x + L.offset h = dot L.slope c + L.offset h
    rw [hclass L.slope hann]
  have hxval := ((G.active_iff_minimum h x L).mp ha).2
  have hcle : P.level ≤ L.value h c := P.contains_c L ha.1
  rw [← heq,hxval] at hcle
  exact (not_le_of_gt hbelow) hcle

theorem ScalePlateau.inside_sqrt_box {d : ℕ} {N : ReactionNetwork d}
    {G : NetworkGeometry N} {c : Fin d → ℝ} {h : ℝ}
    (P : ScalePlateau G c h) (hh : 0 < h) (hh1 : h < 1) (hsmall : h < G.hmax)
    (x : Fin d → ℝ) (hx : x ∈ P.set) :
    x ∈ Icc (fun _ => h^(1/2:ℝ)) (fun _ => (h^(1/2:ℝ))⁻¹) := by
  have hxB := interior_subset (P.inside hx)
  obtain ⟨_,hp,hrec⟩ := reciprocal_box_log_coordinates hh hh1 hxB
  let p : Fin d → ℝ := fun i => Real.log (x i)/Real.log h
  have hpoint : Affine.powerPoint h p = x := funext hrec
  have ha : Affine.Active G.certificate.labels P.constant h (Affine.powerPoint h p) := by
    rw [hpoint]
    exact P.active_constant x hx
  have hhalf := G.active_zero_inside_half h hh hsmall p (fun i => abs_le.mp (hp i))
    P.constant ha P.zero
  constructor
  · intro i
    rw [← hrec i]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1.le (abs_lt.mp (hhalf i)).2.le
  · intro i
    rw [← hrec i,← Real.rpow_neg hh.le]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1.le (abs_lt.mp (hhalf i)).1.le

/-- The quantitative cut margin supplies the actual trapping premise for the
constructed plateau. Compact continuation then supplies full invariance. -/
theorem ScalePlateau.invariant {d : ℕ} {N : ReactionNetwork d}
    {G : NetworkGeometry N} {c : Fin d → ℝ} {h : ℝ}
    (P : ScalePlateau G c h) (k : Reaction N → ℝ) (lower : ℝ) (D : ℕ)
    (hweak : WeaklyReversible N) (hh : 0 < h) (hh1 : h < 1)
    (hsmall : h < G.hmax) (hlower : 0 < lower) (hk : ∀ e, lower ≤ k e)
    (hmargin : h^G.H*(∑ e, k e) ≤ lower/2)
    (hdegree : ∀ e : Reaction N, ∑ i, e.val.1 i ≤ D) :
    IsForwardInvariant N k P.set := by
  classical
  apply massAction_isForwardInvariant_of_compact_trapping P.compact
  intro z hz T x hT hx t ht
  have hboundary : ∀ y ∈ frontier (Icc (fun _ : Fin d => h) (fun _ => h⁻¹)),
      G.minimum h y ≠ P.level := by
    intro y hy hval
    exact hy.2 (P.inside ((P.mem_iff y).mpr hval))
  have hactive : ∀ y ∈ Icc (fun _ : Fin d => h) (fun _ => h⁻¹),
      ∀ L ∈ G.certificate.labels,
      dot L.slope y + L.offset h = G.minimum h y →
      0 ≤ dot L.slope (massAction N k y) := by
    intro y hy L hL hval
    have ha : Affine.Active G.certificate.labels L h y :=
      (G.active_iff_minimum h y L).mpr ⟨hL,hval⟩
    by_cases hann : Annihilator N L.slope
    · rw [annihilator_work N k y L.slope hann]
    · exact (mul_nonneg (mul_nonneg G.H_pos.le hlower.le) (pow_nonneg hh.le D)).trans
        (G.active_drift k h lower D hweak hh hh1 hsmall hlower hk hmargin hdegree y hy L ha hann)
  have htrap := Barrier.forward_solution_trapped G.certificate.labels G.certificate.nonempty
    (fun L => L.slope) (fun L => L.offset h) hT isClosed_Icc
    (P.ceiling) hboundary hactive hx (P.inside hz) ((P.mem_iff z).mp hz)
  exact (P.mem_iff (x t)).mpr (htrap ht).2

end
end ReverseRateLimits

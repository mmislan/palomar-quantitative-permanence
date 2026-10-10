module
public import proofs.ReverseRateLimits.ExponentFamily

@[expose] public section

/-!
# Sharper recovery constants from a reciprocal comparison

The original entry and witness estimates discard the factor `Q^2` in
`Q' = (13/2) p^2 h^7 Q^2 R_Q`.  Comparing `1/Q` instead of `Q` keeps that
factor.  This file proves

* a universal prepared entry deadline `(31/10)/(p^2 h^7)` (previously `7`),
* a witness lower bound `400/(1313 p^2 h^7)` (previously `1/28`),
* the same statements along the continuous reverse-exponent family, and
* an elementary inventory-bottleneck lemma used in the paper's general
  capacity principle.

Nothing here changes the corridor certificate, the parameter rectangle or
the literal ODE; only the one-dimensional comparison coordinate changes.
-/

namespace ReverseRateLimits.SharpRecovery
open Set CoupledSource SourceBounds CorridorDynamics PhysicalConnection PhysicalBounds
  CoupledTheorem RecoveryCorollaries ExponentFamily
noncomputable section

/-! ### Elementary reciprocal inequalities -/

theorem recip_le {q c : ℝ} (hq : 0 < q) (h : 1 ≤ c*q) : q⁻¹ ≤ c := by
  rw [inv_eq_one_div, div_le_iff₀ hq]
  exact h

theorem le_recip {q c : ℝ} (hq : 0 < q) (h : c*q ≤ 1) : c ≤ q⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ hq]
  exact h

theorem of_le_recip {q c : ℝ} (hq : 0 < q) (h : c ≤ q⁻¹) : c*q ≤ 1 := by
  have := mul_le_mul_of_nonneg_right h hq.le
  rwa [inv_mul_cancel₀ hq.ne'] at this

theorem of_recip_le {q c : ℝ} (hq : 0 < q) (h : q⁻¹ ≤ c) : 1 ≤ c*q := by
  have := mul_le_mul_of_nonneg_right h hq.le
  rwa [inv_mul_cancel₀ hq.ne'] at this

/-! ### Reciprocal comparison for normalized trajectories -/

/-- Reciprocal inventory coordinate of a normalized trajectory. -/
def recipN (P : Parameters) (v : Trajectory P) (t : ℝ) : ℝ := (v.Q t)⁻¹

theorem recipN_deriv (P : Parameters) (v : Trajectory P) (s : ℝ) (hs : 0 ≤ s)
    (hQ : 0 < v.Q s) :
    HasDerivAt (recipN P v)
      (-(qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))/(v.Q s)^2) s := by
  have h := (v.dQ s hs).inv hQ.ne'
  exact h

/-- Improved sequential deadline: the `Q` phase now costs `40/(13 p^2 h^7)`
instead of `80/(13 p^2 h^7)`. -/
def tQs (P : Parameters) : ℝ := tB P + 40/(13*P.p^2*P.h^7)

theorem entry_Q_sharp (P : Parameters) (v : Trajectory P)
    (hinit : Outer (v.A 0) (v.B 0) (v.Q 0)) :
    ∀ t, tQs P ≤ t → (1/2:ℝ) ≤ v.Q t ∧ v.Q t ≤ (3/4:ℝ) := by
  intro t ht
  have hp : 0 < P.p := P.p_pos
  have hh : 0 < P.h := P.hh.1
  have hp2 : 0 < P.p^2 := pow_pos hp 2
  have hh7 : 0 < P.h^7 := pow_pos hh 7
  have hδ : 0 < (13/20:ℝ)*P.p^2*P.h^7 := by positivity
  have hTA0 : 0 ≤ tA P := by unfold tA; positivity
  have hTATB : tA P ≤ tB P := by unfold tB; exact le_add_of_nonneg_right (by positivity)
  have hTB0 := hTA0.trans hTATB
  have hTBTQ : tB P ≤ tQs P := by unfold tQs; exact le_add_of_nonneg_right (by positivity)
  have hst := hTBTQ.trans ht
  have ho := outer_invariant P v hinit
  have hQpos : ∀ s, 0 ≤ s → 0 < v.Q s :=
    fun s hs => lt_of_lt_of_le (by norm_num) (ho s hs).2.2.1
  have hf : ∀ s ∈ Icc (tB P) t, HasDerivAt (recipN P v)
      (-(qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))/(v.Q s)^2) s := by
    intro s hs
    have hs0 := hTB0.trans hs.1
    exact recipN_deriv P v s hs0 (hQpos s hs0)
  have hdeadline : (4-2:ℝ)/((13/20:ℝ)*P.p^2*P.h^7) ≤ t - tB P := by
    have heq : (4-2:ℝ)/((13/20:ℝ)*P.p^2*P.h^7) = 40/(13*P.p^2*P.h^7) := by
      field_simp
      ring
    rw [heq]
    dsimp [tQs] at ht
    linarith
  have hdeadline' : ((4/3:ℝ)-1)/((13/20:ℝ)*P.p^2*P.h^7) ≤ t - tB P :=
    (div_le_div_of_nonneg_right (by norm_num) hδ.le).trans hdeadline
  have hQt := hQpos t (hTB0.trans hst)
  constructor
  · have hft : recipN P v t ≤ 2 := by
      apply upper_entry (recipN P v)
        (fun s => -(qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))/(v.Q s)^2)
        4 2 ((13/20:ℝ)*P.p^2*P.h^7) (tB P) t hδ hst hdeadline hf
      · intro s hs
        have hs0 := hTB0.trans hs.1
        exact recip_le (hQpos s hs0) (by linarith [(ho s hs0).2.2.1])
      · intro s hs hfs
        have hs0 := hTB0.trans hs.1
        have hQs := hQpos s hs0
        have hQhalf : v.Q s ≤ 1/2 := by
          have := of_le_recip hQs hfs
          linarith
        have houter := ho s hs0
        have hsign := SourceBounds.entry_Q_lo P (v.Q s) (v.A s) (v.B s)
          ⟨houter.2.2.1,hQhalf⟩ (entry_A P v hinit s (hTATB.trans hs.1))
          (entry_B P v hinit s hs.1)
        have hc : 0 ≤ (13/2:ℝ)*P.p^2*P.h^7*(v.Q s)^2 := by positivity
        have hm := mul_le_mul_of_nonneg_left hsign hc
        show -(qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))/(v.Q s)^2 ≤
          -((13/20:ℝ)*P.p^2*P.h^7)
        rw [div_le_iff₀ (pow_pos hQs 2)]
        unfold qdot
        nlinarith only [hm]
    have := of_recip_le hQt hft
    linarith
  · have hft : (4/3:ℝ) ≤ recipN P v t := by
      apply lower_entry (recipN P v)
        (fun s => -(qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))/(v.Q s)^2)
        1 (4/3:ℝ) ((13/20:ℝ)*P.p^2*P.h^7) (tB P) t hδ hst hdeadline' hf
      · intro s hs
        have hs0 := hTB0.trans hs.1
        exact le_recip (hQpos s hs0) (by linarith [(ho s hs0).2.2.2])
      · intro s hs hfs
        have hs0 := hTB0.trans hs.1
        have hQs := hQpos s hs0
        have hQ34 : (3/4:ℝ) ≤ v.Q s := by
          have := of_recip_le hQs hfs
          linarith
        have houter := ho s hs0
        have hsign := SourceBounds.entry_Q_hi P (v.Q s) (v.A s) (v.B s)
          ⟨hQ34,houter.2.2.2⟩ (entry_A P v hinit s (hTATB.trans hs.1))
          (entry_B P v hinit s hs.1)
        have hc : 0 ≤ (13/2:ℝ)*P.p^2*P.h^7*(v.Q s)^2 := by positivity
        have hm := mul_le_mul_of_nonneg_left hsign hc
        show (13/20:ℝ)*P.p^2*P.h^7 ≤
          -(qdot P.r P.p P.h (v.Q s) (v.A s) (v.B s))/(v.Q s)^2
        rw [le_div_iff₀ (pow_pos hQs 2)]
        unfold qdot
        nlinarith only [hm]
    have := of_le_recip hQt hft
    linarith

theorem recovery_sharp (P : Parameters) (v : Trajectory P)
    (hinit : Outer (v.A 0) (v.B 0) (v.Q 0)) :
    ∀ t, tQs P ≤ t → Inner (v.A t) (v.B t) (v.Q t) := by
  intro t ht
  have hp : 0 < P.p := P.p_pos
  have hh : 0 < P.h := P.hh.1
  have hTATB : tA P ≤ tB P := by unfold tB; exact le_add_of_nonneg_right (by positivity)
  have hTBTQ : tB P ≤ tQs P := by unfold tQs; exact le_add_of_nonneg_right (by positivity)
  exact ⟨entry_A P v hinit t (hTATB.trans (hTBTQ.trans ht)),
    entry_B P v hinit t (hTBTQ.trans ht), entry_Q_sharp P v hinit t ht⟩

/-- `(2h^7 + 32h^4 + 40/13) ≤ 31/10` on the admitted rectangle. -/
theorem deadline_sharp (P : Parameters) : tQs P ≤ (31/10:ℝ)/(P.p^2*P.h^7) := by
  have hp : P.p ≠ 0 := P.p_pos.ne'
  have hh : P.h ≠ 0 := P.hh.1.ne'
  have hh0 := P.hh.1.le
  have hhsmall : P.h ≤ (1/10:ℝ) := P.hh.2.trans (by norm_num)
  have hh4 : P.h^4 ≤ (1/10000:ℝ) := by
    have h := pow_le_pow_left₀ hh0 hhsmall 4
    norm_num at h
    exact h
  have hh7 : P.h^7 ≤ (1/10000000:ℝ) := by
    have h := pow_le_pow_left₀ hh0 hhsmall 7
    norm_num at h
    exact h
  have heq : tQs P = (2*P.h^7+32*P.h^4+(40/13:ℝ))/(P.p^2*P.h^7) := by
    unfold tQs tB tA
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-! ### Literal trajectories -/

theorem literal_recovery_sharp (P : Parameters) (v : LiteralTrajectory P)
    (hinit : Outer (A P v 0) (B P v 0) (Q P v 0)) :
    ∀ t, tQs P ≤ t → Inner (A P v t) (B P v t) (Q P v t) :=
  recovery_sharp P (normalize P v) hinit

theorem prepared_recovery_sharp (P : Parameters) (x0 : Fin 3 → ℝ)
    (hpos : OAI.Problem326.PositiveState x0) (hprepared : Prepared P x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
      ∀ v : LiteralTrajectory P, Starts P x0 v →
        (∀ t, 0 ≤ t →
          ((3/64:ℝ)*P.p*P.h^3 ≤ v.x t ∧ v.x t ≤ 5*P.p*P.h^3) ∧
          ((1/16:ℝ)*P.p*P.h^2 ≤ v.y t ∧ v.y t ≤ 3*P.p*P.h^2) ∧
          ((1/8:ℝ)*P.p*P.h ≤ v.z t ∧ v.z t ≤ P.p*P.h)) ∧
        (∀ t, (31/10:ℝ)/(P.p^2*P.h^7) ≤ t → Inner (A P v t) (B P v t) (Q P v t)) := by
  refine ⟨(prepared_family P x0 hpos hprepared).1,?_⟩
  intro v hs
  have hcoords := initial_coordinates P x0 v hs
  have hinit : Outer (A P v 0) (B P v 0) (Q P v 0) := by
    rw [hcoords.1,hcoords.2.1,hcoords.2.2]
    exact hprepared
  exact ⟨all_time_coordinate_bounds P v hinit,
    fun t ht => literal_recovery_sharp P v hinit t ((deadline_sharp P).trans ht)⟩

/-- Upward inventory speed keeps the factor `Q^2`. -/
theorem qdot_upper_sharp (P : Parameters) (q a b : ℝ) (ho : Outer a b q) :
    qdot P.r P.p P.h q a b ≤ (1313/200:ℝ)*P.p^2*P.h^7*q^2 := by
  obtain ⟨hCl,hCu⟩ := C_bounds P q a b ho
  have hq0 : 0 ≤ q := by linarith [ho.2.2.1]
  have hb0 : 0 ≤ b := by linarith [ho.2.1.1]
  have hC0 : 0 ≤ C P.h q a b := by linarith
  have ha3 : 0 ≤ P.r.a3 := (by norm_num : (0:ℝ) ≤ 99/100).trans P.ha3.1
  have hb3 : 0 ≤ P.r.b3 := (by norm_num : (0:ℝ) ≤ 99/100).trans P.hb3.1
  have hforward : 0 ≤ P.r.a3*a^2*b*q^6 := by positivity
  have hreverse : P.r.b3*(C P.h q a b)^2 ≤ (101/100:ℝ) := by
    calc
      P.r.b3*(C P.h q a b)^2 ≤ (101/100:ℝ)*1^2 := by gcongr; exact P.hb3.2
      _ = (101/100:ℝ) := by norm_num
  have hR : RQ P.r P.h q a b ≤ (101/100:ℝ) := by
    unfold RQ
    linarith
  have hc : 0 ≤ (13/2:ℝ)*P.p^2*P.h^7*q^2 := by
    have hh := P.hh.1.le
    positivity
  have h1 := mul_le_mul_of_nonneg_left hR hc
  unfold qdot
  nlinarith only [h1]

/-- Reciprocal inventory coordinate of a literal trajectory. -/
def recip (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ := (Q P v t)⁻¹

theorem recip_deriv (P : Parameters) (v : LiteralTrajectory P) (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (recip P v)
      (-(qdot P.r P.p P.h (Q P v s) (A P v s) (B P v s))/(Q P v s)^2) s := by
  have h := (deriv_Q P v s hs).inv (Q_pos P v s hs).ne'
  exact h

theorem witness_time_lower_sharp (P : Parameters) (v : LiteralTrajectory P)
    (hinit : Outer (A P v 0) (B P v 0) (Q P v 0))
    (hQ0 : Q P v 0 = (1/4:ℝ)) (t : ℝ) (ht : 0 ≤ t) (hQtarget : (1/2:ℝ) ≤ Q P v t) :
    400/(1313*P.p^2*P.h^7) ≤ t := by
  have ho := (literal_recovery P v hinit).1
  have hc : ContinuousOn (recip P v) (Icc 0 t) :=
    fun s hs => (recip_deriv P v s hs.1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (recip P v) (interior (Icc 0 t)) :=
    fun s hs => (recip_deriv P v s (interior_subset hs).1).differentiableAt.differentiableWithinAt
  have hlow : ∀ s ∈ interior (Icc 0 t),
      -((1313/200:ℝ)*P.p^2*P.h^7) ≤ deriv (recip P v) s := by
    intro s hs
    have hs0 := (interior_subset hs).1
    rw [(recip_deriv P v s hs0).deriv]
    have hQs := Q_pos P v s hs0
    rw [le_div_iff₀ (pow_pos hQs 2)]
    have hup := qdot_upper_sharp P (Q P v s) (A P v s) (B P v s) (ho s hs0)
    nlinarith only [hup]
  have hdiff := (convex_Icc 0 t).mul_sub_le_image_sub_of_le_deriv hc hd hlow
    0 ⟨le_rfl,ht⟩ t ⟨ht,le_rfl⟩ ht
  have hf0 : recip P v 0 = 4 := by
    unfold recip
    rw [hQ0]
    norm_num
  have hft : recip P v t ≤ 2 := recip_le (Q_pos P v t ht) (by linarith)
  rw [hf0,sub_zero] at hdiff
  have hden : 0 < 1313*P.p^2*P.h^7 := by
    have hp := P.p_pos
    have hh := P.hh.1
    positivity
  rw [div_le_iff₀ hden]
  nlinarith only [hdiff,hft]

theorem witness_sharp (P : Parameters) :
    ∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
      ∀ t, 0 ≤ t → Inner (A P v t) (B P v t) (Q P v t) →
        400/(1313*P.p^2*P.h^7) ≤ t := by
  obtain ⟨hpos,hprep,hQ⟩ := witness_state P
  obtain ⟨v,hs⟩ := (prepared_recovery_sharp P (witnessState P) hpos hprep).1
  have hc := initial_coordinates P (witnessState P) v hs
  have hinit : Outer (A P v 0) (B P v 0) (Q P v 0) := by
    rw [hc.1,hc.2.1,hc.2.2]
    exact hprep
  exact ⟨v,hs,fun t ht hi => witness_time_lower_sharp P v hinit (hc.2.2.trans hQ) t ht hi.2.2.1⟩

/-! ### The continuous reverse-exponent family with the sharper constants -/

theorem family_root_sharp (epsilon gamma : ℝ) (he : 0 < epsilon)
    (P : Parameters) (hh : P.h=epsilon^(hExponent gamma))
    (hu : P.u=epsilon^(uExponent gamma)) (x0 : Fin 3 → ℝ)
    (hpos : OAI.Problem326.PositiveState x0) (hprep : Prepared P x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
      (∀ v : LiteralTrajectory P, Starts P x0 v →
        (∀ t, 0 ≤ t →
          ((3/64:ℝ)*epsilon^(xExponent gamma) ≤ v.x t ∧ v.x t ≤ 5*epsilon^(xExponent gamma)) ∧
          ((1/16:ℝ)*epsilon^(yExponent gamma) ≤ v.y t ∧ v.y t ≤ 3*epsilon^(yExponent gamma)) ∧
          ((1/8:ℝ)*epsilon^(zExponent gamma) ≤ v.z t ∧ v.z t ≤ epsilon^(zExponent gamma))) ∧
        (∀ t, (31/10:ℝ)/epsilon^(timeExponent gamma) ≤ t →
          Inner (A P v t) (B P v t) (Q P v t))) ∧
      (∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
        ∀ t, 0 ≤ t → Inner (A P v t) (B P v t) (Q P v t) →
          400/(1313*epsilon^(timeExponent gamma)) ≤ t) := by
  have hi := identities epsilon gamma he P hh hu
  have hscaleX : P.p*P.h^3=epsilon^(xExponent gamma) := hi.2.2.2.1
  have hscaleY : P.p*P.h^2=epsilon^(yExponent gamma) := hi.2.2.2.2.1
  have hscaleZ : P.p*P.h=epsilon^(zExponent gamma) := hi.2.2.2.2.2.1
  have htime := hi.2.2.2.2.2.2
  have hp := prepared_recovery_sharp P x0 hpos hprep
  refine ⟨hp.1,?_,?_⟩
  · simpa only [mul_assoc,hscaleX,hscaleY,hscaleZ,htime] using hp.2
  · simpa only [htime,mul_assoc] using witness_sharp P

/-! ### A general inventory-bottleneck lemma -/

/-- If an inventory has derivative at most `M > 0` on `[0,T]` and must rise by
`ΔU` by time `T`, then `T ≥ ΔU/M`.  No monotonicity of the inventory is
assumed. -/
theorem inventory_bottleneck (U : ℝ → ℝ) (M ΔU T : ℝ) (hM : 0 < M) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ M)
    (hrise : U 0 + ΔU ≤ U T) : ΔU/M ≤ T := by
  have hc : ContinuousOn U (Icc 0 T) := by
    intro t ht
    obtain ⟨d,hdt,_⟩ := hd t ht
    exact hdt.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ U (interior (Icc 0 T)) := by
    intro t ht
    obtain ⟨d,hdt,_⟩ := hd t (interior_subset ht)
    exact hdt.differentiableAt.differentiableWithinAt
  have hle : ∀ t ∈ interior (Icc (0:ℝ) T), deriv U t ≤ M := by
    intro t ht
    obtain ⟨d,hdt,hdM⟩ := hd t (interior_subset ht)
    rw [hdt.deriv]
    exact hdM
  have h := (convex_Icc 0 T).image_sub_le_mul_sub_of_deriv_le hc hdiff hle
    0 ⟨le_rfl,hT⟩ T ⟨hT,le_rfl⟩ hT
  rw [sub_zero] at h
  rw [div_le_iff₀ hM]
  linarith

/-- With zero replenishment capacity a strictly higher inventory level is unreachable. -/
theorem inventory_unreachable (U : ℝ → ℝ) (ΔU T : ℝ) (hΔ : 0 < ΔU) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ 0) :
    U T < U 0 + ΔU := by
  have hc : ContinuousOn U (Icc 0 T) := by
    intro t ht
    obtain ⟨d,hdt,_⟩ := hd t ht
    exact hdt.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ U (interior (Icc 0 T)) := by
    intro t ht
    obtain ⟨d,hdt,_⟩ := hd t (interior_subset ht)
    exact hdt.differentiableAt.differentiableWithinAt
  have hle : ∀ t ∈ interior (Icc (0:ℝ) T), deriv U t ≤ 0 := by
    intro t ht
    obtain ⟨d,hdt,hdM⟩ := hd t (interior_subset ht)
    rw [hdt.deriv]
    exact hdM
  have h := (convex_Icc 0 T).image_sub_le_mul_sub_of_deriv_le hc hdiff hle
    0 ⟨le_rfl,hT⟩ T ⟨hT,le_rfl⟩ hT
  linarith

end
end ReverseRateLimits.SharpRecovery

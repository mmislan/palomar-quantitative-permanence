module
public import proofs.ReverseRateLimits.GeneralTheorem
public import proofs.ReverseRateLimits.CommonClock
public import proofs.ReverseRateLimits.ExponentFamily
public import proofs.ReverseRateLimits.ReactionExtent
public import proofs.ReverseRateLimits.SharpRecovery
public import proofs.ReverseRateLimits.GlobalInventory

@[expose] public section

namespace ReverseRateLimits.Publication
open OAI.Problem326 CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem
  RecoveryCorollaries ExponentFamily ReactionExtent SharpRecovery GlobalInventory
noncomputable section

def GeneralConclusion (d : ℕ) (N : ReactionNetwork d) : Prop :=
  ∃ H : ℝ, 0 < H ∧
    ∀ c : Fin d → ℝ, PositiveState c → ∀ lower upper : ℝ,
      0 < lower → lower ≤ upper →
      ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧
        ∀ exponent : Reaction N → ℝ, ∀ amin amax : ℝ,
          0 ≤ amin → amin ≤ amax →
          (∀ e, amin ≤ exponent e ∧ exponent e ≤ amax) →
          ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
          ∀ prefactor : Reaction N → ℝ,
            (∀ e, lower ≤ prefactor e ∧ prefactor e ≤ upper) →
            ∀ initial : Fin d → ℝ, PositiveState initial → SameClass N c initial →
              let k := fun e => rate epsilon (prefactor e) (exponent e)
              (∃ x, IsGlobalForwardSolution N k initial x) ∧
                ∀ x, IsGlobalForwardSolution N k initial x → ∃ T, 0 ≤ T ∧
                  ∀ t, T ≤ t → ∀ i,
                    alpha^(1/2:ℝ)*epsilon^((amax-amin)/(2*H)) ≤ x t i ∧
                      x t i ≤ (alpha^(1/2:ℝ)*epsilon^((amax-amin)/(2*H)))⁻¹

def PreparedConclusion (P : Parameters) (x0 : Fin 3 → ℝ) : Prop :=
  (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
    ∀ v : LiteralTrajectory P, Starts P x0 v →
      (∀ t, 0 ≤ t →
        ((3/64:ℝ)*P.p*P.h^3 ≤ v.x t ∧ v.x t ≤ 5*P.p*P.h^3) ∧
        ((1/16:ℝ)*P.p*P.h^2 ≤ v.y t ∧ v.y t ≤ 3*P.p*P.h^2) ∧
        ((1/8:ℝ)*P.p*P.h ≤ v.z t ∧ v.z t ≤ P.p*P.h)) ∧
      (∀ t, (31/10:ℝ)/(P.p^2*P.h^7) ≤ t → Inner (A P v t) (B P v t) (Q P v t))

def ContinuousConclusion (epsilon gamma : ℝ) (P : Parameters) (x0 : Fin 3 → ℝ) : Prop :=
  (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
    (∀ v : LiteralTrajectory P, Starts P x0 v →
      (∀ t, 0 ≤ t →
        ((3/64:ℝ)*epsilon^(xExponent gamma) ≤ v.x t ∧ v.x t ≤ 5*epsilon^(xExponent gamma)) ∧
        ((1/16:ℝ)*epsilon^(yExponent gamma) ≤ v.y t ∧ v.y t ≤ 3*epsilon^(yExponent gamma)) ∧
        ((1/8:ℝ)*epsilon^(zExponent gamma) ≤ v.z t ∧ v.z t ≤ epsilon^(zExponent gamma))) ∧
      (∀ t, (31/10:ℝ)/epsilon^(timeExponent gamma) ≤ t → Inner (A P v t) (B P v t) (Q P v t))) ∧
    (∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
      ∀ t, 0 ≤ t → Inner (A P v t) (B P v t) (Q P v t) →
        400/(1313*epsilon^(timeExponent gamma)) ≤ t)

/-- End-to-end scientific consumer. Its premises are only network structure,
positive autonomous parameter data and positive initial preparation.
Recovery constants: universal prepared deadline (31/10)/(p^2 h^7) and witness
lower bound 400/(1313 p^2 h^7) (SharpRecovery); the earlier constants 7 and
1/28 remain available in RecoveryCorollaries. The final conjunct is the global
inventory clock theorem for arbitrary positive seeds (GlobalInventory). -/
theorem Main (d : ℕ) (N : ReactionNetwork d) (hd : 0 < d) (hweak : WeaklyReversible N)
    (P : Parameters) (x0 : Fin 3 → ℝ) (hpos : PositiveState x0) (hprep : Prepared P x0) :
    GeneralConclusion d N ∧
    PreparedConclusion P x0 ∧
    (∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
      ∀ T, 0 ≤ T → Inner (A P v T) (B P v T) (Q P v T) →
        400/(1313*P.p^2*P.h^7) ≤ T ∧
        P.p*P.h/26 ≤ -(∫ t in (0:ℝ)..T, current3 P v t) ∧
        P.p*P.h/26 ≤ ∫ t in (0:ℝ)..T, reverse3 P v t) ∧
    (∀ (clock : ℝ) (k : Reaction N → ℝ) (initial : Fin d → ℝ) (x : ℝ → Fin d → ℝ),
      0 < clock →
      (IsGlobalForwardSolution N (fun e => clock*k e) initial (fun t => x (clock*t)) ↔
        IsGlobalForwardSolution N k initial x)) ∧
    ((sy P)^2=sx P*sz P ∧
      1/(P.p^2*P.h^7)=sy P/(sx P)^3 ∧
      1/(P.p^2*P.h^7)=(sz P)^3/(sy P)^5) ∧
    (∀ epsilon gamma : ℝ, 0 < epsilon →
      P.h=epsilon^(hExponent gamma) → P.u=epsilon^(uExponent gamma) →
        ContinuousConclusion epsilon gamma P x0) ∧
    (∀ epsilon gamma : ℝ, 0 < epsilon → ((1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ)) →
      epsilon ≤ cutoff gamma →
        epsilon^(hExponent gamma) ≤ (1/1000:ℝ) ∧ epsilon^(uExponent gamma) ≤ (1/1000:ℝ)) ∧
    (∀ epsilon gamma : ℝ, 0 < epsilon → ((1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ)) →
      epsilon ≤ improvedCutoff gamma →
        ∃ R : Parameters, R.r=P.r ∧ R.h=epsilon^(hExponent gamma) ∧
          R.u=epsilon^(uExponent gamma)) ∧
    (∀ gamma : ℝ, cutoff gamma=(10:ℝ)^(-36/min (2*gamma-1) (7-2*gamma))) ∧
    (∀ mx my mz : ℝ, 2*mx-2*my-mz=0 → -mx+2*my-2*mz=0 → -2*mx-my+2*mz=0 →
      mx=0 ∧ my=0 ∧ mz=0) ∧
    (∀ x1 : Fin 3 → ℝ, PositiveState x1 →
      (∃ v : LiteralTrajectory P, Starts P x1 v) ∧
      ∀ v : LiteralTrajectory P, ∀ T, 0 ≤ T →
        4/(13*P.r.b3*P.p*P.h^6)*(1/inventory P v 0-1/inventory P v T) ≤ T ∧
        90/(13*P.r.a3)*(1/(inventory P v T)^2-1/(inventory P v 0)^2) ≤ T) := by
  refine ⟨general_quantitative_root d N hd hweak,
    prepared_recovery_sharp P x0 hpos hprep,?_,?_,scale_tradeoff P,?_,?_,?_,cutoff_decimal,?_,?_⟩
  · obtain ⟨v,hs,hlow⟩ := witness_sharp P
    refine ⟨v,hs,?_⟩
    intro T hT hi
    exact ⟨hlow T hT hi,restoration_extent P v hs T hT hi⟩
  · intro clock k initial x hc
    exact CommonClock.rescale_iff N k initial x clock hc
  · intro epsilon gamma he hh hu
    exact family_root_sharp epsilon gamma he P hh hu x0 hpos hprep
  · intro epsilon gamma he hg hcut
    exact original_cutoff_bounds epsilon gamma he hg hcut
  · intro epsilon gamma he hg hcut
    exact ⟨parameters P epsilon gamma he hg hcut,rfl,rfl,rfl⟩
  · exact no_linear_inventory
  · exact fun x1 h1 => global_inventory_clocks P x1 h1

end
end ReverseRateLimits.Publication

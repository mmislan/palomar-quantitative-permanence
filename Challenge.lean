module
public import Mathlib

/-!
Quantitative permanence and recovery with vanishing reverse rates.
This independent statement uses literal networks, rates, derivative equations,
initial preparation, targets and interval integrals. Every theorem hole below
is deliberate; the Solution must supply a proof using only the permitted axioms.
-/
@[expose] public section
open Set MeasureTheory
noncomputable section
attribute [local instance 10000] IsModuleTopology.toContinuousSMul

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace OAI.Problem326
attribute [local instance 20000] instContinuousSMulForall
structure ReactionNetwork (d : ℕ) where
  complexes : Finset (Fin d → ℕ)
  reactions : Finset ((Fin d → ℕ) × (Fin d → ℕ))
  source_mem : ∀ e ∈ reactions, e.1 ∈ complexes
  target_mem : ∀ e ∈ reactions, e.2 ∈ complexes
  source_ne_target : ∀ e ∈ reactions, e.1 ≠ e.2

abbrev Reaction {d : ℕ} (N : ReactionNetwork d) :=
  {e : (Fin d → ℕ) × (Fin d → ℕ) // e ∈ N.reactions}

def HasReaction {d : ℕ} (N : ReactionNetwork d)
    (y z : Fin d → ℕ) : Prop :=
  (y, z) ∈ N.reactions

def WeaklyReversible {d : ℕ} (N : ReactionNetwork d) : Prop :=
  ∀ e : Reaction N,
    Relation.TransGen (HasReaction N) e.val.2 e.val.1

def monomial {d : ℕ} (x : Fin d → ℝ) (y : Fin d → ℕ) : ℝ :=
  Finset.univ.prod (fun i => x i ^ y i)

def massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Finset.univ.sum (fun e : Reaction N =>
    κ e * monomial x e.val.1 *
      ((e.val.2 i : ℝ) - (e.val.1 i : ℝ)))

def PositiveState {d : ℕ} (x : Fin d → ℝ) : Prop :=
  ∀ i, 0 < x i

def IsGlobalForwardSolution {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x0 : Fin d → ℝ)
    (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt x (massAction N κ (x t)) t

def IsForwardSolutionOn {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x0 : Fin d → ℝ) (T : ℝ)
    (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    ContinuousOn x (Set.Icc (0 : ℝ) T) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt x (massAction N κ (x t)) t

def dot {d : ℕ} (a x : Fin d → ℝ) : ℝ :=
  Finset.univ.sum (fun i => a i * x i)

end OAI.Problem326

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits
open OAI.Problem326
def Annihilator {d : ℕ} (N : ReactionNetwork d) (r : Fin d → ℝ) : Prop :=
  ∀ e : Reaction N, dot r (fun i => (e.val.2 i:ℝ))-dot r (fun i => (e.val.1 i:ℝ)) = 0

def SameClass {d : ℕ} (N : ReactionNetwork d) (c x : Fin d → ℝ) : Prop :=
  ∀ r : Fin d → ℝ, Annihilator N r → dot r x = dot r c

end ReverseRateLimits

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits
noncomputable def rate (epsilon prefactor exponent : ℝ) : ℝ :=
  prefactor * epsilon ^ exponent

end ReverseRateLimits

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.CoupledSource
structure Rates where
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  k : ℝ
  b1 : ℝ
  b2 : ℝ
  b3 : ℝ
  b4 : ℝ

def j1 (r : Rates) (p x y z : ℝ) : ℝ := r.a1*y^2*z-r.b1*p^2*x^2

def j2 (r : Rates) (p x y z : ℝ) : ℝ := r.a2*x*z^2-r.b2*p^2*y^2

def j3 (r : Rates) (p h x y z : ℝ) : ℝ := r.a3*x^2*y-r.b3*p*h^6*z^2

def j4 (r : Rates) (p x z : ℝ) : ℝ := r.k*z^3-r.b4*p^2*x

def dx (r : Rates) (p h x y z : ℝ) : ℝ :=
  2*j1 r p x y z-j2 r p x y z-2*j3 r p h x y z+j4 r p x z

def dy (r : Rates) (p h x y z : ℝ) : ℝ :=
  -2*j1 r p x y z+2*j2 r p x y z-j3 r p h x y z

def dz (r : Rates) (p h x y z : ℝ) : ℝ :=
  -j1 r p x y z-2*j2 r p x y z+2*j3 r p h x y z-3*j4 r p x z

noncomputable def C (h Q A B : ℝ) : ℝ := 1-3*h^2*A*Q^2-(5/2:ℝ)*h*B*Q

end ReverseRateLimits.CoupledSource

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.SourceBounds
open CoupledSource
structure Parameters where
  h : ℝ
  u : ℝ
  r : Rates
  hh : 0 < h ∧ h ≤ (1/600:ℝ)
  hu : 0 < u ∧ u ≤ (1/20:ℝ)
  ha1 : (99/100:ℝ) ≤ r.a1 ∧ r.a1 ≤ (101/100:ℝ)
  ha2 : (99/100:ℝ) ≤ r.a2 ∧ r.a2 ≤ (101/100:ℝ)
  ha3 : (99/100:ℝ) ≤ r.a3 ∧ r.a3 ≤ (101/100:ℝ)
  hK : (99/25:ℝ) ≤ r.k ∧ r.k ≤ (101/25:ℝ)
  hb1 : (99/100:ℝ) ≤ r.b1 ∧ r.b1 ≤ (101/100:ℝ)
  hb2 : (99/100:ℝ) ≤ r.b2 ∧ r.b2 ≤ (101/100:ℝ)
  hb3 : (99/100:ℝ) ≤ r.b3 ∧ r.b3 ≤ (101/100:ℝ)
  hb4 : (99/100:ℝ) ≤ r.b4 ∧ r.b4 ≤ (101/100:ℝ)

end ReverseRateLimits.SourceBounds

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.SourceBounds
noncomputable def Parameters.p (P : Parameters) : ℝ := P.u * P.h

end ReverseRateLimits.SourceBounds

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.CorridorDynamics
def Outer (A B Q : ℝ) : Prop :=
  (3 ≤ A ∧ A ≤ 5) ∧ (1 ≤ B ∧ B ≤ 3) ∧ ((1/4:ℝ) ≤ Q ∧ Q ≤ 1)

def Inner (A B Q : ℝ) : Prop :=
  ((7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ)) ∧
  ((3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ)) ∧ ((1/2:ℝ) ≤ Q ∧ Q ≤ (3/4:ℝ))

end ReverseRateLimits.CorridorDynamics

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.PhysicalConnection
open CoupledSource SourceBounds CorridorDynamics
structure LiteralTrajectory (P : Parameters) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  z : ℝ → ℝ
  dx : ∀ t, 0 ≤ t → HasDerivAt x (CoupledSource.dx P.r P.p P.h (x t) (y t) (z t)) t
  dy : ∀ t, 0 ≤ t → HasDerivAt y (CoupledSource.dy P.r P.p P.h (x t) (y t) (z t)) t
  dz : ∀ t, 0 ≤ t → HasDerivAt z (CoupledSource.dz P.r P.p P.h (x t) (y t) (z t)) t
  positive : ∀ t, 0 ≤ t → 0 < x t ∧ 0 < y t ∧ 0 < z t

noncomputable def Q (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  (6*v.x t+5*v.y t+2*v.z t)/(2*P.p*P.h)

noncomputable def A (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  v.x t/(P.p*P.h^3*(Q P v t)^3)

noncomputable def B (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  v.y t/(P.p*P.h^2*(Q P v t)^2)

end ReverseRateLimits.PhysicalConnection

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.CoupledTheorem
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection
def stateQ (P : Parameters) (x : Fin 3 → ℝ) : ℝ :=
  (6*x 0+5*x 1+2*x 2)/(2*P.p*P.h)

def stateA (P : Parameters) (x : Fin 3 → ℝ) : ℝ := x 0/(P.p*P.h^3*(stateQ P x)^3)

def stateB (P : Parameters) (x : Fin 3 → ℝ) : ℝ := x 1/(P.p*P.h^2*(stateQ P x)^2)

def Prepared (P : Parameters) (x : Fin 3 → ℝ) : Prop :=
  Outer (stateA P x) (stateB P x) (stateQ P x)

def Starts (P : Parameters) (x : Fin 3 → ℝ) (v : LiteralTrajectory P) : Prop :=
  v.x 0 = x 0 ∧ v.y 0 = x 1 ∧ v.z 0 = x 2

def witnessState (P : Parameters) : Fin 3 → ℝ :=
  ![P.p*P.h^3*4*(1/4:ℝ)^3,
    P.p*P.h^2*2*(1/4:ℝ)^2,
    P.p*P.h*(1/4:ℝ)*C P.h (1/4:ℝ) 4 2]

end ReverseRateLimits.CoupledTheorem

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.RecoveryCorollaries
open SourceBounds
def sx (P : Parameters) : ℝ := P.p*P.h^3

def sy (P : Parameters) : ℝ := P.p*P.h^2

def sz (P : Parameters) : ℝ := P.p*P.h

end ReverseRateLimits.RecoveryCorollaries

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.ExponentFamily
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

end ReverseRateLimits.ExponentFamily

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.ReactionExtent
open CoupledSource SourceBounds PhysicalConnection
def inventory (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  6*v.x t+5*v.y t+2*v.z t

def current3 (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  j3 P.r P.p P.h (v.x t) (v.y t) (v.z t)

def reverse3 (P : Parameters) (v : LiteralTrajectory P) (t : ℝ) : ℝ :=
  P.r.b3*P.p*P.h^6*(v.z t)^2

end ReverseRateLimits.ReactionExtent

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits
open OAI.Problem326
theorem general_quantitative_root (d : ℕ) (N : ReactionNetwork d)
    (hd : 0 < d) (hweak : WeaklyReversible N) :
    ∃ H : ℝ, 0 < H ∧
      ∀ c : Fin d → ℝ, PositiveState c → ∀ lower upper : ℝ,
        0 < lower → lower ≤ upper →
        ∃ A : ℝ, 0 < A ∧ A < 1 ∧
          ∀ exponent : Reaction N → ℝ, ∀ amin amax : ℝ,
            0 ≤ amin → amin ≤ amax →
            (∀ e, amin ≤ exponent e ∧ exponent e ≤ amax) →
            ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
            ∀ prefactor : Reaction N → ℝ,
              (∀ e, lower ≤ prefactor e ∧ prefactor e ≤ upper) →
              ∀ x0 : Fin d → ℝ, PositiveState x0 → SameClass N c x0 →
                let k := fun e => rate epsilon (prefactor e) (exponent e)
                (∃ x, IsGlobalForwardSolution N k x0 x) ∧
                  ∀ x, IsGlobalForwardSolution N k x0 x → ∃ T, 0 ≤ T ∧
                    ∀ t, T ≤ t → ∀ i,
                      A^(1/2:ℝ)*epsilon^((amax-amin)/(2*H)) ≤ x t i ∧
                        x t i ≤ (A^(1/2:ℝ)*epsilon^((amax-amin)/(2*H)))⁻¹ := by
  sorry
end ReverseRateLimits

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.SharpRecovery
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem RecoveryCorollaries ExponentFamily
theorem prepared_recovery_sharp (P : Parameters) (x0 : Fin 3 → ℝ)
    (hpos : OAI.Problem326.PositiveState x0) (hprepared : Prepared P x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
      ∀ v : LiteralTrajectory P, Starts P x0 v →
        (∀ t, 0 ≤ t →
          ((3/64:ℝ)*P.p*P.h^3 ≤ v.x t ∧ v.x t ≤ 5*P.p*P.h^3) ∧
          ((1/16:ℝ)*P.p*P.h^2 ≤ v.y t ∧ v.y t ≤ 3*P.p*P.h^2) ∧
          ((1/8:ℝ)*P.p*P.h ≤ v.z t ∧ v.z t ≤ P.p*P.h)) ∧
        (∀ t, (31/10:ℝ)/(P.p^2*P.h^7) ≤ t → Inner (A P v t) (B P v t) (Q P v t)) := by
  sorry
end ReverseRateLimits.SharpRecovery

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.SharpRecovery
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem RecoveryCorollaries ExponentFamily
theorem witness_sharp (P : Parameters) :
    ∃ v : LiteralTrajectory P, Starts P (witnessState P) v ∧
      ∀ t, 0 ≤ t → Inner (A P v t) (B P v t) (Q P v t) →
        400/(1313*P.p^2*P.h^7) ≤ t := by
  sorry
end ReverseRateLimits.SharpRecovery

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.GlobalInventory
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem ReactionExtent
theorem global_inventory_clocks (P : Parameters) (x0 : Fin 3 → ℝ)
    (hpos : OAI.Problem326.PositiveState x0) :
    (∃ v : LiteralTrajectory P, Starts P x0 v) ∧
      ∀ v : LiteralTrajectory P, ∀ T, 0 ≤ T →
        4/(13*P.r.b3*P.p*P.h^6)*(1/inventory P v 0-1/inventory P v T) ≤ T ∧
        90/(13*P.r.a3)*(1/(inventory P v T)^2-1/(inventory P v 0)^2) ≤ T := by
  sorry
end ReverseRateLimits.GlobalInventory

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.SharpRecovery
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem RecoveryCorollaries ExponentFamily
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
  sorry
end ReverseRateLimits.SharpRecovery

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.ExponentFamily
open SourceBounds RecoveryCorollaries
theorem identities (epsilon gamma : ℝ) (he : 0 < epsilon)
    (P : Parameters) (hh : P.h=epsilon^(hExponent gamma))
    (hu : P.u=epsilon^(uExponent gamma)) :
    P.p=epsilon^(1/2:ℝ) ∧ P.p^2=epsilon ∧ P.p*P.h^6=epsilon^gamma ∧
      sx P=epsilon^(xExponent gamma) ∧ sy P=epsilon^(yExponent gamma) ∧
      sz P=epsilon^(zExponent gamma) ∧ P.p^2*P.h^7=epsilon^(timeExponent gamma) := by
  sorry
end ReverseRateLimits.ExponentFamily

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.ExponentFamily
theorem original_cutoff_bounds (epsilon gamma : ℝ) (he : 0 < epsilon)
    (hg : (1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ)) (hcut : epsilon ≤ cutoff gamma) :
    epsilon^(hExponent gamma) ≤ (1/1000:ℝ) ∧
      epsilon^(uExponent gamma) ≤ (1/1000:ℝ) := by
  sorry
end ReverseRateLimits.ExponentFamily

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.ExponentFamily
theorem cutoff_decimal (gamma : ℝ) :
    cutoff gamma = (10:ℝ)^(-36/min (2*gamma-1) (7-2*gamma)) := by
  sorry
end ReverseRateLimits.ExponentFamily

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.CommonClock
open OAI.Problem326
theorem rescale_iff {d : ℕ} (N : ReactionNetwork d) (k : Reaction N → ℝ)
    (x0 : Fin d → ℝ) (x : ℝ → Fin d → ℝ) (clock : ℝ) (hc : 0 < clock) :
    IsGlobalForwardSolution N (fun e => clock*k e) x0 (fun t => x (clock*t)) ↔
      IsGlobalForwardSolution N k x0 x := by
  sorry
end ReverseRateLimits.CommonClock

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.RecoveryCorollaries
open SourceBounds
theorem scale_tradeoff (P : Parameters) :
    (sy P)^2 = sx P*sz P ∧
      1/(P.p^2*P.h^7) = sy P/(sx P)^3 ∧
      1/(P.p^2*P.h^7) = (sz P)^3/(sy P)^5 := by
  sorry
end ReverseRateLimits.RecoveryCorollaries

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.ReactionExtent
open CoupledSource SourceBounds CorridorDynamics PhysicalConnection CoupledTheorem
theorem restoration_extent (P : Parameters) (v : LiteralTrajectory P)
    (hs : Starts P (witnessState P) v) (T : ℝ) (hT : 0 ≤ T)
    (hinner : Inner (A P v T) (B P v T) (Q P v T)) :
    P.p*P.h/26 ≤ -(∫ t in (0:ℝ)..T, current3 P v t) ∧
      P.p*P.h/26 ≤ ∫ t in (0:ℝ)..T, reverse3 P v t := by
  sorry
end ReverseRateLimits.ReactionExtent

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.SharpRecovery
attribute [local instance 10000] IsModuleTopology.toContinuousSMul
theorem inventory_bottleneck (U : ℝ → ℝ) (M ΔU T : ℝ) (hM : 0 < M) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ M)
    (hrise : U 0 + ΔU ≤ U T) : ΔU/M ≤ T := by
  sorry
end ReverseRateLimits.SharpRecovery

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.SharpRecovery
attribute [local instance 10000] IsModuleTopology.toContinuousSMul
theorem inventory_unreachable (U : ℝ → ℝ) (ΔU T : ℝ) (hΔ : 0 < ΔU) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ 0) :
    U T < U 0 + ΔU := by
  sorry
end ReverseRateLimits.SharpRecovery

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.GlobalInventory
attribute [local instance 10000] IsModuleTopology.toContinuousSMul
theorem inventory_bottleneck_scaling (U : ℝ → ℝ) (C a eps ΔU T : ℝ)
    (hC : 0 < C) (heps : 0 < eps) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ C*eps^a)
    (hrise : U 0 + ΔU ≤ U T) : ΔU/C*eps^(-a) ≤ T := by
  sorry
end ReverseRateLimits.GlobalInventory

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace ReverseRateLimits.RecoveryCorollaries
theorem no_linear_inventory (mx my mz : ℝ)
    (h1 : 2*mx-2*my-mz=0) (h2 : -mx+2*my-2*mz=0)
    (h3 : -2*mx-my+2*mz=0) : mx=0 ∧ my=0 ∧ mz=0 := by
  sorry
end ReverseRateLimits.RecoveryCorollaries

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace QuantitativeRegistry
open ReverseRateLimits.SourceBounds ReverseRateLimits.ExponentFamily
theorem family_parameters (template : Parameters) (epsilon gamma : ℝ)
    (he : 0 < epsilon) (hg : (1/2:ℝ)<gamma ∧ gamma<(7/2:ℝ))
    (hcut : epsilon ≤ improvedCutoff gamma) :
    ∃ P : Parameters, P.r=template.r ∧ P.h=epsilon^(hExponent gamma) ∧
      P.u=epsilon^(uExponent gamma) := by
  sorry

theorem admitted_parameters : Nonempty Parameters := by
  sorry
end QuantitativeRegistry

run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace QuantitativeRegistry
attribute [local instance 10000] IsModuleTopology.toContinuousSMul
theorem state_capacity_clock (U g : ℝ → ℝ) (S : Set ℝ)
    (hsopen : IsOpen S) (hsconv : Convex ℝ S)
    (hg : ContinuousOn g S) (hgpos : ∀ u ∈ S, 0 < g u)
    (target T : ℝ) (hT : 0 ≤ T)
    (hregion : ∀ t ∈ Icc (0:ℝ) T, U t ∈ S)
    (htarget : target ∈ S) (hrise : target ≤ U T)
    (hd : ∀ t ∈ Icc (0:ℝ) T, ∃ d, HasDerivAt U d t ∧ d ≤ g (U t)) :
    (∫ s in (U 0)..target, 1/g s) ≤ T := by
  sorry
end QuantitativeRegistry

end

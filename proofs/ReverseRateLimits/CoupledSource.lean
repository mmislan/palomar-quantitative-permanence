module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Data.Finset.Order
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

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

theorem neutral_pool (r : Rates) (p h x y z : ℝ) :
    6*dx r p h x y z+5*dy r p h x y z+2*dz r p h x y z =
      -13*j3 r p h x y z := by
  unfold dx dy dz
  ring

theorem stationary_currents (r : Rates) (p h x y z : ℝ) :
    (dx r p h x y z = 0 ∧ dy r p h x y z = 0 ∧ dz r p h x y z = 0) ↔
      (j3 r p h x y z = 0 ∧ j1 r p x y z = j2 r p x y z ∧
        j1 r p x y z = -j4 r p x z) := by
  unfold dx dy dz
  constructor <;> rintro ⟨hx,hy,hz⟩ <;> constructor
  all_goals try linarith
  all_goals constructor <;> linarith

noncomputable def C (h Q A B : ℝ) : ℝ := 1-3*h^2*A*Q^2-(5/2:ℝ)*h*B*Q
noncomputable def G (r : Rates) (h Q A B : ℝ) : ℝ := r.a3*A^2*B*Q^6-r.b3*(C h Q A B)^2
noncomputable def RA (r : Rates) (h u Q A B : ℝ) : ℝ :=
  r.k*(C h Q A B)^3-r.b4*A+
  h^2*Q^2*(2*r.a1*B^2*C h Q A B-r.a2*A*(C h Q A B)^2)-
  2*r.b1*u*h^4*A^2*Q^3+r.b2*u*h^2*B^2*Q-
  2*r.a3*h^5*A^2*B*Q^5+2*r.b3*h^5*(C h Q A B)^2/Q+
  (39/2:ℝ)*A*h^7*Q*G r h Q A B
noncomputable def RB (r : Rates) (h u Q A B : ℝ) : ℝ :=
  2*(r.a2*A*(C h Q A B)^2-r.a1*B^2*C h Q A B)+
  2*r.b1*u*h^2*A^2*Q-2*r.b2*u*B^2/Q-
  r.a3*h^3*A^2*B*Q^3+r.b3*h^3*(C h Q A B)^2/Q^3+
  13*B*h^4*G r h Q A B/Q^2
noncomputable def RQ (r : Rates) (h Q A B : ℝ) : ℝ := r.b3*(C h Q A B)^2-r.a3*A^2*B*Q^6
noncomputable def qdot (r : Rates) (p h Q A B : ℝ) : ℝ :=
  (13/2:ℝ)*p^2*h^7*Q^2*RQ r h Q A B

/-- Exact full-field rescaling, retaining every current and every moving weight. -/
theorem transformed_source (r : Rates) (h u Q A B : ℝ) (hQ : Q ≠ 0) :
    let p := u*h
    let x := p*h^3*A*Q^3
    let y := p*h^2*B*Q^2
    let z := p*h*Q*C h Q A B
    dx r p h x y z = p*h^3*(p^2*Q^3*RA r h u Q A B+3*A*Q^2*qdot r p h Q A B) ∧
    dy r p h x y z = p*h^2*(p^2*h^3*Q^5*RB r h u Q A B+2*B*Q*qdot r p h Q A B) ∧
    6*dx r p h x y z+5*dy r p h x y z+2*dz r p h x y z =
      2*p*h*qdot r p h Q A B := by
  dsimp
  constructor
  · unfold dx j1 j2 j3 j4 RA qdot RQ G C
    field_simp
    ring
  · constructor
    · unfold dy j1 j2 j3 RB qdot RQ G C
      field_simp
      ring
    · rw [neutral_pool]
      unfold j3 qdot RQ C
      ring

end ReverseRateLimits.CoupledSource

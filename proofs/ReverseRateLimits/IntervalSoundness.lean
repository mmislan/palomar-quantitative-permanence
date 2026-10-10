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

namespace ReverseRateLimits.IntervalCertificate

structure Bounds where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

def Bounds.contains (b : Bounds) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)
def Bounds.point (q : ℚ) : Bounds := ⟨q,q⟩
def Bounds.add (b c : Bounds) : Bounds := ⟨b.lo+c.lo,b.hi+c.hi⟩
def Bounds.neg (b : Bounds) : Bounds := ⟨-b.hi,-b.lo⟩
def Bounds.mul (b c : Bounds) : Bounds :=
  ⟨min (min (b.lo*c.lo) (b.lo*c.hi)) (min (b.hi*c.lo) (b.hi*c.hi)),
   max (max (b.lo*c.lo) (b.lo*c.hi)) (max (b.hi*c.lo) (b.hi*c.hi))⟩
def Bounds.pow (b : Bounds) (n : ℕ) : Bounds := ⟨b.lo^n,b.hi^n⟩
def Bounds.inv (b : Bounds) : Bounds := ⟨b.hi⁻¹,b.lo⁻¹⟩

private theorem linear_upper (x a b y M : ℝ) (hx : a ≤ x ∧ x ≤ b)
    (ha : a*y ≤ M) (hb : b*y ≤ M) : x*y ≤ M := by
  by_cases hy : 0 ≤ y
  · exact (mul_le_mul_of_nonneg_right hx.2 hy).trans hb
  · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_lt (lt_of_not_ge hy))).trans ha

private theorem linear_lower (x a b y m : ℝ) (hx : a ≤ x ∧ x ≤ b)
    (ha : m ≤ a*y) (hb : m ≤ b*y) : m ≤ x*y := by
  by_cases hy : 0 ≤ y
  · exact ha.trans (mul_le_mul_of_nonneg_right hx.1 hy)
  · exact hb.trans (mul_le_mul_of_nonpos_right hx.2 (le_of_lt (lt_of_not_ge hy)))

theorem Bounds.mul_sound (b c : Bounds) (x y : ℝ)
    (hx : b.contains x) (hy : c.contains y) : (b.mul c).contains (x*y) := by
  simp only [Bounds.contains, Bounds.mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] at *
  constructor
  · let m : ℝ := min (min ((b.lo:ℝ)*c.lo) ((b.lo:ℝ)*c.hi))
        (min ((b.hi:ℝ)*c.lo) ((b.hi:ℝ)*c.hi))
    have h1 : m ≤ x*(c.lo:ℝ) := linear_lower x _ _ _ m hx
      ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : m ≤ x*(c.hi:ℝ) := linear_lower x _ _ _ m hx
      ((min_le_left _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [m,mul_comm] using linear_lower y (c.lo:ℝ) (c.hi:ℝ) x m hy
      (by simpa only [mul_comm] using h1) (by simpa only [mul_comm] using h2)
  · let M : ℝ := max (max ((b.lo:ℝ)*c.lo) ((b.lo:ℝ)*c.hi))
        (max ((b.hi:ℝ)*c.lo) ((b.hi:ℝ)*c.hi))
    have h1 : x*(c.lo:ℝ) ≤ M := linear_upper x _ _ _ M hx
      ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
    have h2 : x*(c.hi:ℝ) ≤ M := linear_upper x _ _ _ M hx
      ((le_max_right _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
    simpa only [M,mul_comm] using linear_upper y (c.lo:ℝ) (c.hi:ℝ) x M hy
      (by simpa only [mul_comm] using h1) (by simpa only [mul_comm] using h2)

inductive Expr where
  | constant : ℚ → Expr
  | atom : ℕ → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → ℕ → Expr
  | inv : Expr → Expr
deriving Repr

noncomputable def Expr.eval (v : ℕ → ℝ) : Expr → ℝ
  | .constant q => q
  | .atom i => v i
  | .add a b => a.eval v+b.eval v
  | .neg a => -a.eval v
  | .mul a b => a.eval v*b.eval v
  | .pow a n => (a.eval v)^n
  | .inv a => (a.eval v)⁻¹

def Expr.bound (v : ℕ → Bounds) : Expr → Bounds
  | .constant q => .point q
  | .atom i => v i
  | .add a b => (a.bound v).add (b.bound v)
  | .neg a => (a.bound v).neg
  | .mul a b => (a.bound v).mul (b.bound v)
  | .pow a n => (a.bound v).pow n
  | .inv a => (a.bound v).inv

def Expr.valid (v : ℕ → Bounds) : Expr → Prop
  | .constant _ => True
  | .atom _ => True
  | .add a b => a.valid v ∧ b.valid v
  | .neg a => a.valid v
  | .mul a b => a.valid v ∧ b.valid v
  | .pow a _ => a.valid v ∧ 0 ≤ (a.bound v).lo
  | .inv a => a.valid v ∧ 0 < (a.bound v).lo

noncomputable instance (e : Expr) (v : ℕ → Bounds) : Decidable (e.valid v) := by
  induction e with
  | constant q => exact inferInstanceAs (Decidable True)
  | atom i => exact inferInstanceAs (Decidable True)
  | add a b ha hb =>
      letI := ha
      letI := hb
      exact inferInstanceAs (Decidable (a.valid v ∧ b.valid v))
  | neg a ha => exact ha
  | mul a b ha hb =>
      letI := ha
      letI := hb
      exact inferInstanceAs (Decidable (a.valid v ∧ b.valid v))
  | pow a n ha =>
      letI := ha
      exact inferInstanceAs (Decidable (a.valid v ∧ 0 ≤ (a.bound v).lo))
  | inv a ha =>
      letI := ha
      exact inferInstanceAs (Decidable (a.valid v ∧ 0 < (a.bound v).lo))

/-- Checked rational inclusions bound every real evaluation throughout a full box. -/
theorem Expr.sound (e : Expr) (box : ℕ → Bounds) (v : ℕ → ℝ)
    (hv : ∀ i, (box i).contains (v i)) (he : e.valid box) :
    (e.bound box).contains (e.eval v) := by
  induction e with
  | constant q => simp [Expr.bound, Expr.eval, Bounds.contains, Bounds.point]
  | atom i => exact hv i
  | add a b ha hb =>
      obtain ⟨hal,hau⟩ := ha he.1
      obtain ⟨hbl,hbu⟩ := hb he.2
      simp only [Expr.bound, Expr.eval, Bounds.add, Bounds.contains, Rat.cast_add]
      exact ⟨add_le_add hal hbl,add_le_add hau hbu⟩
  | neg a ha =>
      obtain ⟨hal,hau⟩ := ha he
      simp only [Expr.bound, Expr.eval, Bounds.neg, Bounds.contains, Rat.cast_neg]
      exact ⟨neg_le_neg hau,neg_le_neg hal⟩
  | mul a b ha hb => exact Bounds.mul_sound _ _ _ _ (ha he.1) (hb he.2)
  | pow a n ha =>
      obtain ⟨hal,hau⟩ := ha he.1
      have hl : (0 : ℝ) ≤ (a.bound box).lo := by exact_mod_cast he.2
      have hx : 0 ≤ a.eval v := hl.trans hal
      simp only [Expr.bound, Expr.eval, Bounds.pow, Bounds.contains, Rat.cast_pow]
      exact ⟨pow_le_pow_left₀ hl hal n,pow_le_pow_left₀ hx hau n⟩
  | inv a ha =>
      obtain ⟨hal,hau⟩ := ha he.1
      have hl : (0 : ℝ) < (a.bound box).lo := by exact_mod_cast he.2
      have hx : 0 < a.eval v := hl.trans_le hal
      simp only [Expr.bound, Expr.eval, Bounds.inv, Bounds.contains, Rat.cast_inv]
      exact ⟨(inv_le_inv₀ (hx.trans_le hau) hx).mpr hau, (inv_le_inv₀ hx hl).mpr hal⟩

end ReverseRateLimits.IntervalCertificate

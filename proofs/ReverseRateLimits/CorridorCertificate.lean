module
public import proofs.ReverseRateLimits.IntervalSoundness
public import proofs.ReverseRateLimits.CoupledSource

@[expose] public section

namespace ReverseRateLimits.CorridorCertificate
open IntervalCertificate
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def RAexpr : Expr := (.add (.add (.add (.add (.add (.add (.add (.mul (.atom 8) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 3)) (.mul (.mul (.constant (-1:ℚ)) (.atom 3)) (.atom 12))) (.mul (.mul (.pow (.atom 2) 2) (.pow (.atom 0) 2)) (.add (.mul (.mul (.mul (.constant (-1:ℚ)) (.atom 3)) (.atom 6)) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 2)) (.mul (.mul (.mul (.constant (2:ℚ)) (.atom 5)) (.pow (.atom 4) 2)) (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))))))) (.mul (.mul (.mul (.mul (.constant (2:ℚ)) (.atom 11)) (.inv (.pow (.atom 2) 1))) (.pow (.atom 0) 5)) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 2))) (.mul (.mul (.mul (.mul (.constant (39/2:ℚ)) (.atom 3)) (.atom 2)) (.pow (.atom 0) 7)) (.add (.mul (.mul (.constant (-1:ℚ)) (.atom 11)) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 2)) (.mul (.mul (.mul (.atom 4) (.atom 7)) (.pow (.atom 3) 2)) (.pow (.atom 2) 6))))) (.mul (.mul (.mul (.mul (.atom 2) (.atom 10)) (.atom 1)) (.pow (.atom 4) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.mul (.mul (.constant (-2:ℚ)) (.atom 4)) (.atom 7)) (.pow (.atom 3) 2)) (.pow (.atom 2) 5)) (.pow (.atom 0) 5))) (.mul (.mul (.mul (.mul (.mul (.constant (-2:ℚ)) (.atom 9)) (.atom 1)) (.pow (.atom 3) 2)) (.pow (.atom 2) 3)) (.pow (.atom 0) 4)))

def RBexpr : Expr := (.add (.add (.add (.add (.add (.add (.mul (.mul (.mul (.constant (-2:ℚ)) (.atom 5)) (.pow (.atom 4) 2)) (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0)))) (.mul (.mul (.mul (.constant (2:ℚ)) (.atom 3)) (.atom 6)) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 2))) (.mul (.mul (.mul (.atom 11) (.inv (.pow (.atom 2) 3))) (.pow (.atom 0) 3)) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 2))) (.mul (.mul (.mul (.mul (.constant (-2:ℚ)) (.atom 10)) (.atom 1)) (.pow (.atom 4) 2)) (.inv (.pow (.atom 2) 1)))) (.mul (.mul (.mul (.mul (.constant (13:ℚ)) (.atom 4)) (.inv (.pow (.atom 2) 2))) (.pow (.atom 0) 4)) (.add (.mul (.mul (.constant (-1:ℚ)) (.atom 11)) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 2)) (.mul (.mul (.mul (.atom 4) (.atom 7)) (.pow (.atom 3) 2)) (.pow (.atom 2) 6))))) (.mul (.mul (.mul (.mul (.mul (.constant (-1:ℚ)) (.atom 4)) (.atom 7)) (.pow (.atom 3) 2)) (.pow (.atom 2) 3)) (.pow (.atom 0) 3))) (.mul (.mul (.mul (.mul (.mul (.constant (2:ℚ)) (.atom 2)) (.atom 9)) (.atom 1)) (.pow (.atom 3) 2)) (.pow (.atom 0) 2)))

def RQexpr : Expr := (.add (.mul (.atom 11) (.pow (.add (.add (.constant (1:ℚ)) (.mul (.mul (.mul (.constant (-3:ℚ)) (.atom 3)) (.pow (.atom 2) 2)) (.pow (.atom 0) 2))) (.mul (.mul (.mul (.constant (-5/2:ℚ)) (.atom 4)) (.atom 2)) (.atom 0))) 2)) (.mul (.mul (.mul (.mul (.constant (-1:ℚ)) (.atom 4)) (.atom 7)) (.pow (.atom 3) 2)) (.pow (.atom 2) 6)))

def sourceRates (v : ℕ → ℝ) : CoupledSource.Rates := ⟨v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12⟩

theorem RAexpr_eq_source (v : ℕ → ℝ) :
    RAexpr.eval v = CoupledSource.RA (sourceRates v) (v 0) (v 1) (v 2) (v 3) (v 4) := by
  simp only [RAexpr,Expr.eval,CoupledSource.RA,CoupledSource.C,CoupledSource.G,sourceRates]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem RBexpr_eq_source (v : ℕ → ℝ) :
    RBexpr.eval v = CoupledSource.RB (sourceRates v) (v 0) (v 1) (v 2) (v 3) (v 4) := by
  simp only [RBexpr,Expr.eval,CoupledSource.RB,CoupledSource.C,CoupledSource.G,sourceRates]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem RQexpr_eq_source (v : ℕ → ℝ) :
    RQexpr.eval v = CoupledSource.RQ (sourceRates v) (v 0) (v 2) (v 3) (v 4) := by
  simp only [RQexpr,Expr.eval,CoupledSource.RQ,CoupledSource.C,sourceRates]
  push_cast
  simp only [div_eq_mul_inv]
  ring

def outer_A_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(3:ℚ),(3:ℚ)⟩
  | 4 => ⟨(1:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem outer_A_lo_valid : RAexpr.valid outer_A_lo_box := by decide +kernel

theorem outer_A_lo_numeric : (RAexpr.bound outer_A_lo_box).lo > 0 := by decide +kernel

theorem outer_A_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (outer_A_lo_box i).contains (v i)) : 0 < RAexpr.eval v := by
  have hb := RAexpr.sound outer_A_lo_box v hv outer_A_lo_valid
  have hn : (0 : ℝ) < ((RAexpr.bound outer_A_lo_box).lo : ℝ) := by
    exact_mod_cast outer_A_lo_numeric
  exact hn.trans_le hb.1

def outer_A_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(5:ℚ),(5:ℚ)⟩
  | 4 => ⟨(1:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem outer_A_hi_valid : RAexpr.valid outer_A_hi_box := by decide +kernel

theorem outer_A_hi_numeric : (RAexpr.bound outer_A_hi_box).hi < 0 := by decide +kernel

theorem outer_A_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (outer_A_hi_box i).contains (v i)) : RAexpr.eval v < 0 := by
  have hb := RAexpr.sound outer_A_hi_box v hv outer_A_hi_valid
  have hn : (0 : ℝ) > ((RAexpr.bound outer_A_hi_box).hi : ℝ) := by
    exact_mod_cast outer_A_hi_numeric
  exact hb.2.trans_lt hn

def outer_B_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(3:ℚ),(5:ℚ)⟩
  | 4 => ⟨(1:ℚ),(1:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem outer_B_lo_valid : RBexpr.valid outer_B_lo_box := by decide +kernel

theorem outer_B_lo_numeric : (RBexpr.bound outer_B_lo_box).lo > 0 := by decide +kernel

theorem outer_B_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (outer_B_lo_box i).contains (v i)) : 0 < RBexpr.eval v := by
  have hb := RBexpr.sound outer_B_lo_box v hv outer_B_lo_valid
  have hn : (0 : ℝ) < ((RBexpr.bound outer_B_lo_box).lo : ℝ) := by
    exact_mod_cast outer_B_lo_numeric
  exact hn.trans_le hb.1

def outer_B_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(3:ℚ),(5:ℚ)⟩
  | 4 => ⟨(3:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem outer_B_hi_valid : RBexpr.valid outer_B_hi_box := by decide +kernel

theorem outer_B_hi_numeric : (RBexpr.bound outer_B_hi_box).hi < 0 := by decide +kernel

theorem outer_B_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (outer_B_hi_box i).contains (v i)) : RBexpr.eval v < 0 := by
  have hb := RBexpr.sound outer_B_hi_box v hv outer_B_hi_valid
  have hn : (0 : ℝ) > ((RBexpr.bound outer_B_hi_box).hi : ℝ) := by
    exact_mod_cast outer_B_hi_numeric
  exact hb.2.trans_lt hn

def outer_Q_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1/4:ℚ)⟩
  | 3 => ⟨(3:ℚ),(5:ℚ)⟩
  | 4 => ⟨(1:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem outer_Q_lo_valid : RQexpr.valid outer_Q_lo_box := by decide +kernel

theorem outer_Q_lo_numeric : (RQexpr.bound outer_Q_lo_box).lo > 0 := by decide +kernel

theorem outer_Q_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (outer_Q_lo_box i).contains (v i)) : 0 < RQexpr.eval v := by
  have hb := RQexpr.sound outer_Q_lo_box v hv outer_Q_lo_valid
  have hn : (0 : ℝ) < ((RQexpr.bound outer_Q_lo_box).lo : ℝ) := by
    exact_mod_cast outer_Q_lo_numeric
  exact hn.trans_le hb.1

def outer_Q_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1:ℚ),(1:ℚ)⟩
  | 3 => ⟨(3:ℚ),(5:ℚ)⟩
  | 4 => ⟨(1:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem outer_Q_hi_valid : RQexpr.valid outer_Q_hi_box := by decide +kernel

theorem outer_Q_hi_numeric : (RQexpr.bound outer_Q_hi_box).hi < 0 := by decide +kernel

theorem outer_Q_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (outer_Q_hi_box i).contains (v i)) : RQexpr.eval v < 0 := by
  have hb := RQexpr.sound outer_Q_hi_box v hv outer_Q_hi_valid
  have hn : (0 : ℝ) > ((RQexpr.bound outer_Q_hi_box).hi : ℝ) := by
    exact_mod_cast outer_Q_hi_numeric
  exact hb.2.trans_lt hn

def inner_A_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/2:ℚ),(3/4:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(7/2:ℚ)⟩
  | 4 => ⟨(3/2:ℚ),(5/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem inner_A_lo_valid : RAexpr.valid inner_A_lo_box := by decide +kernel

theorem inner_A_lo_numeric : (RAexpr.bound inner_A_lo_box).lo > 0 := by decide +kernel

theorem inner_A_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (inner_A_lo_box i).contains (v i)) : 0 < RAexpr.eval v := by
  have hb := RAexpr.sound inner_A_lo_box v hv inner_A_lo_valid
  have hn : (0 : ℝ) < ((RAexpr.bound inner_A_lo_box).lo : ℝ) := by
    exact_mod_cast inner_A_lo_numeric
  exact hn.trans_le hb.1

def inner_A_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/2:ℚ),(3/4:ℚ)⟩
  | 3 => ⟨(9/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(3/2:ℚ),(5/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem inner_A_hi_valid : RAexpr.valid inner_A_hi_box := by decide +kernel

theorem inner_A_hi_numeric : (RAexpr.bound inner_A_hi_box).hi < 0 := by decide +kernel

theorem inner_A_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (inner_A_hi_box i).contains (v i)) : RAexpr.eval v < 0 := by
  have hb := RAexpr.sound inner_A_hi_box v hv inner_A_hi_valid
  have hn : (0 : ℝ) > ((RAexpr.bound inner_A_hi_box).hi : ℝ) := by
    exact_mod_cast inner_A_hi_numeric
  exact hb.2.trans_lt hn

def inner_B_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/2:ℚ),(3/4:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(3/2:ℚ),(3/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem inner_B_lo_valid : RBexpr.valid inner_B_lo_box := by decide +kernel

theorem inner_B_lo_numeric : (RBexpr.bound inner_B_lo_box).lo > 0 := by decide +kernel

theorem inner_B_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (inner_B_lo_box i).contains (v i)) : 0 < RBexpr.eval v := by
  have hb := RBexpr.sound inner_B_lo_box v hv inner_B_lo_valid
  have hn : (0 : ℝ) < ((RBexpr.bound inner_B_lo_box).lo : ℝ) := by
    exact_mod_cast inner_B_lo_numeric
  exact hn.trans_le hb.1

def inner_B_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/2:ℚ),(3/4:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(5/2:ℚ),(5/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem inner_B_hi_valid : RBexpr.valid inner_B_hi_box := by decide +kernel

theorem inner_B_hi_numeric : (RBexpr.bound inner_B_hi_box).hi < 0 := by decide +kernel

theorem inner_B_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (inner_B_hi_box i).contains (v i)) : RBexpr.eval v < 0 := by
  have hb := RBexpr.sound inner_B_hi_box v hv inner_B_hi_valid
  have hn : (0 : ℝ) > ((RBexpr.bound inner_B_hi_box).hi : ℝ) := by
    exact_mod_cast inner_B_hi_numeric
  exact hb.2.trans_lt hn

def inner_Q_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/2:ℚ),(1/2:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(3/2:ℚ),(5/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem inner_Q_lo_valid : RQexpr.valid inner_Q_lo_box := by decide +kernel

theorem inner_Q_lo_numeric : (RQexpr.bound inner_Q_lo_box).lo > 0 := by decide +kernel

theorem inner_Q_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (inner_Q_lo_box i).contains (v i)) : 0 < RQexpr.eval v := by
  have hb := RQexpr.sound inner_Q_lo_box v hv inner_Q_lo_valid
  have hn : (0 : ℝ) < ((RQexpr.bound inner_Q_lo_box).lo : ℝ) := by
    exact_mod_cast inner_Q_lo_numeric
  exact hn.trans_le hb.1

def inner_Q_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(3/4:ℚ),(3/4:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(3/2:ℚ),(5/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem inner_Q_hi_valid : RQexpr.valid inner_Q_hi_box := by decide +kernel

theorem inner_Q_hi_numeric : (RQexpr.bound inner_Q_hi_box).hi < 0 := by decide +kernel

theorem inner_Q_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (inner_Q_hi_box i).contains (v i)) : RQexpr.eval v < 0 := by
  have hb := RQexpr.sound inner_Q_hi_box v hv inner_Q_hi_valid
  have hn : (0 : ℝ) > ((RQexpr.bound inner_Q_hi_box).hi : ℝ) := by
    exact_mod_cast inner_Q_hi_numeric
  exact hb.2.trans_lt hn

def entry_A_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(3:ℚ),(7/2:ℚ)⟩
  | 4 => ⟨(1:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem entry_A_lo_valid : RAexpr.valid entry_A_lo_box := by decide +kernel

theorem entry_A_lo_numeric : (1/4:ℚ) ≤ (RAexpr.bound entry_A_lo_box).lo := by decide +kernel

theorem entry_A_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (entry_A_lo_box i).contains (v i)) : (1/4:ℝ) ≤ RAexpr.eval v := by
  have hb := RAexpr.sound entry_A_lo_box v hv entry_A_lo_valid
  have hn : (((1/4:ℚ) : ℚ) : ℝ) ≤ ((RAexpr.bound entry_A_lo_box).lo : ℝ) := by
    exact_mod_cast entry_A_lo_numeric
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hn
  exact hn.trans hb.1

def entry_A_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(9/2:ℚ),(5:ℚ)⟩
  | 4 => ⟨(1:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem entry_A_hi_valid : RAexpr.valid entry_A_hi_box := by decide +kernel

theorem entry_A_hi_numeric : (RAexpr.bound entry_A_hi_box).hi ≤ -(1/4:ℚ) := by decide +kernel

theorem entry_A_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (entry_A_hi_box i).contains (v i)) : RAexpr.eval v ≤ -(1/4:ℝ) := by
  have hb := RAexpr.sound entry_A_hi_box v hv entry_A_hi_valid
  have hn : ((-(1/4:ℚ) : ℚ) : ℝ) ≥ ((RAexpr.bound entry_A_hi_box).hi : ℝ) := by
    exact_mod_cast entry_A_hi_numeric
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hn
  exact hb.2.trans hn

def entry_B_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(1:ℚ),(3/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem entry_B_lo_valid : RBexpr.valid entry_B_lo_box := by decide +kernel

theorem entry_B_lo_numeric : (1:ℚ) ≤ (RBexpr.bound entry_B_lo_box).lo := by decide +kernel

theorem entry_B_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (entry_B_lo_box i).contains (v i)) : (1:ℝ) ≤ RBexpr.eval v := by
  have hb := RBexpr.sound entry_B_lo_box v hv entry_B_lo_valid
  have hn : (((1:ℚ) : ℚ) : ℝ) ≤ ((RBexpr.bound entry_B_lo_box).lo : ℝ) := by
    exact_mod_cast entry_B_lo_numeric
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hn
  exact hn.trans hb.1

def entry_B_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(5/2:ℚ),(3:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem entry_B_hi_valid : RBexpr.valid entry_B_hi_box := by decide +kernel

theorem entry_B_hi_numeric : (RBexpr.bound entry_B_hi_box).hi ≤ -(1:ℚ) := by decide +kernel

theorem entry_B_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (entry_B_hi_box i).contains (v i)) : RBexpr.eval v ≤ -(1:ℝ) := by
  have hb := RBexpr.sound entry_B_hi_box v hv entry_B_hi_valid
  have hn : ((-(1:ℚ) : ℚ) : ℝ) ≥ ((RBexpr.bound entry_B_hi_box).hi : ℝ) := by
    exact_mod_cast entry_B_hi_numeric
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hn
  exact hb.2.trans hn

def entry_Q_lo_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(1/4:ℚ),(1/2:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(3/2:ℚ),(5/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem entry_Q_lo_valid : RQexpr.valid entry_Q_lo_box := by decide +kernel

theorem entry_Q_lo_numeric : (1/10:ℚ) ≤ (RQexpr.bound entry_Q_lo_box).lo := by decide +kernel

theorem entry_Q_lo_sound (v : ℕ → ℝ)
    (hv : ∀ i, (entry_Q_lo_box i).contains (v i)) : (1/10:ℝ) ≤ RQexpr.eval v := by
  have hb := RQexpr.sound entry_Q_lo_box v hv entry_Q_lo_valid
  have hn : (((1/10:ℚ) : ℚ) : ℝ) ≤ ((RQexpr.bound entry_Q_lo_box).lo : ℝ) := by
    exact_mod_cast entry_Q_lo_numeric
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hn
  exact hn.trans hb.1

def entry_Q_hi_box : ℕ → Bounds := fun i => match i with
  | 0 => ⟨(0:ℚ),(1/600:ℚ)⟩
  | 1 => ⟨(0:ℚ),(1/20:ℚ)⟩
  | 2 => ⟨(3/4:ℚ),(1:ℚ)⟩
  | 3 => ⟨(7/2:ℚ),(9/2:ℚ)⟩
  | 4 => ⟨(3/2:ℚ),(5/2:ℚ)⟩
  | 5 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 6 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 7 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 8 => ⟨(99/25:ℚ),(101/25:ℚ)⟩
  | 9 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 10 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 11 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | 12 => ⟨(99/100:ℚ),(101/100:ℚ)⟩
  | _ => ⟨0,0⟩

theorem entry_Q_hi_valid : RQexpr.valid entry_Q_hi_box := by decide +kernel

theorem entry_Q_hi_numeric : (RQexpr.bound entry_Q_hi_box).hi ≤ -(1/10:ℚ) := by decide +kernel

theorem entry_Q_hi_sound (v : ℕ → ℝ)
    (hv : ∀ i, (entry_Q_hi_box i).contains (v i)) : RQexpr.eval v ≤ -(1/10:ℝ) := by
  have hb := RQexpr.sound entry_Q_hi_box v hv entry_Q_hi_valid
  have hn : ((-(1/10:ℚ) : ℚ) : ℝ) ≥ ((RQexpr.bound entry_Q_hi_box).hi : ℝ) := by
    exact_mod_cast entry_Q_hi_numeric
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hn
  exact hb.2.trans hn

end ReverseRateLimits.CorridorCertificate

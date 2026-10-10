module
public import proofs.ReverseRateLimits.CorridorCertificate

@[expose] public section

namespace ReverseRateLimits.SourceBounds
open CoupledSource CorridorCertificate IntervalCertificate

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

def env (P : Parameters) (Q A B : ℝ) : ℕ → ℝ := fun i => match i with
  | 0 => P.h
  | 1 => P.u
  | 2 => Q
  | 3 => A
  | 4 => B
  | 5 => P.r.a1
  | 6 => P.r.a2
  | 7 => P.r.a3
  | 8 => P.r.k
  | 9 => P.r.b1
  | 10 => P.r.b2
  | 11 => P.r.b3
  | 12 => P.r.b4
  | _ => 0

theorem sourceRates_env (P : Parameters) (Q A B : ℝ) :
    sourceRates (env P Q A B) = P.r := by rfl

theorem outer_A_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (3:ℝ) ≤ A ∧ A ≤ (3:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : 0 < RA P.r P.h P.u Q A B := by
  have hv : ∀ i, (outer_A_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,outer_A_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,outer_A_lo_box,Bounds.contains]
  have hs := outer_A_lo_sound (env P Q A B) hv
  rw [RAexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem outer_A_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (5:ℝ) ≤ A ∧ A ≤ (5:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : RA P.r P.h P.u Q A B < 0 := by
  have hv : ∀ i, (outer_A_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,outer_A_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,outer_A_hi_box,Bounds.contains]
  have hs := outer_A_hi_sound (env P Q A B) hv
  rw [RAexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem outer_B_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (3:ℝ) ≤ A ∧ A ≤ (5:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (1:ℝ))
    : 0 < RB P.r P.h P.u Q A B := by
  have hv : ∀ i, (outer_B_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,outer_B_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,outer_B_lo_box,Bounds.contains]
  have hs := outer_B_lo_sound (env P Q A B) hv
  rw [RBexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem outer_B_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (3:ℝ) ≤ A ∧ A ≤ (5:ℝ))
    (hB : (3:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : RB P.r P.h P.u Q A B < 0 := by
  have hv : ∀ i, (outer_B_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,outer_B_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,outer_B_hi_box,Bounds.contains]
  have hs := outer_B_hi_sound (env P Q A B) hv
  rw [RBexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem outer_Q_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1/4:ℝ))
    (hA : (3:ℝ) ≤ A ∧ A ≤ (5:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : 0 < RQ P.r P.h Q A B := by
  have hv : ∀ i, (outer_Q_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,outer_Q_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,outer_Q_lo_box,Bounds.contains]
  have hs := outer_Q_lo_sound (env P Q A B) hv
  rw [RQexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem outer_Q_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (1:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (3:ℝ) ≤ A ∧ A ≤ (5:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : RQ P.r P.h Q A B < 0 := by
  have hv : ∀ i, (outer_Q_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,outer_Q_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,outer_Q_hi_box,Bounds.contains]
  have hs := outer_Q_hi_sound (env P Q A B) hv
  rw [RQexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem inner_A_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/2:ℝ) ≤ Q ∧ Q ≤ (3/4:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (7/2:ℝ))
    (hB : (3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ))
    : 0 < RA P.r P.h P.u Q A B := by
  have hv : ∀ i, (inner_A_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,inner_A_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,inner_A_lo_box,Bounds.contains]
  have hs := inner_A_lo_sound (env P Q A B) hv
  rw [RAexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem inner_A_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (1/2:ℝ) ≤ Q ∧ Q ≤ (3/4:ℝ))
    (hA : (9/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ))
    : RA P.r P.h P.u Q A B < 0 := by
  have hv : ∀ i, (inner_A_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,inner_A_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,inner_A_hi_box,Bounds.contains]
  have hs := inner_A_hi_sound (env P Q A B) hv
  rw [RAexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem inner_B_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/2:ℝ) ≤ Q ∧ Q ≤ (3/4:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (3/2:ℝ) ≤ B ∧ B ≤ (3/2:ℝ))
    : 0 < RB P.r P.h P.u Q A B := by
  have hv : ∀ i, (inner_B_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,inner_B_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,inner_B_lo_box,Bounds.contains]
  have hs := inner_B_lo_sound (env P Q A B) hv
  rw [RBexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem inner_B_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (1/2:ℝ) ≤ Q ∧ Q ≤ (3/4:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (5/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ))
    : RB P.r P.h P.u Q A B < 0 := by
  have hv : ∀ i, (inner_B_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,inner_B_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,inner_B_hi_box,Bounds.contains]
  have hs := inner_B_hi_sound (env P Q A B) hv
  rw [RBexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem inner_Q_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/2:ℝ) ≤ Q ∧ Q ≤ (1/2:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ))
    : 0 < RQ P.r P.h Q A B := by
  have hv : ∀ i, (inner_Q_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,inner_Q_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,inner_Q_lo_box,Bounds.contains]
  have hs := inner_Q_lo_sound (env P Q A B) hv
  rw [RQexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem inner_Q_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (3/4:ℝ) ≤ Q ∧ Q ≤ (3/4:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ))
    : RQ P.r P.h Q A B < 0 := by
  have hv : ∀ i, (inner_Q_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,inner_Q_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,inner_Q_hi_box,Bounds.contains]
  have hs := inner_Q_hi_sound (env P Q A B) hv
  rw [RQexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem entry_A_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (3:ℝ) ≤ A ∧ A ≤ (7/2:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : (1/4:ℝ) ≤ RA P.r P.h P.u Q A B := by
  have hv : ∀ i, (entry_A_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,entry_A_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,entry_A_lo_box,Bounds.contains]
  have hs := entry_A_lo_sound (env P Q A B) hv
  rw [RAexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem entry_A_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (9/2:ℝ) ≤ A ∧ A ≤ (5:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : RA P.r P.h P.u Q A B ≤ -(1/4:ℝ) := by
  have hv : ∀ i, (entry_A_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,entry_A_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,entry_A_hi_box,Bounds.contains]
  have hs := entry_A_hi_sound (env P Q A B) hv
  rw [RAexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem entry_B_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (1:ℝ) ≤ B ∧ B ≤ (3/2:ℝ))
    : (1:ℝ) ≤ RB P.r P.h P.u Q A B := by
  have hv : ∀ i, (entry_B_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,entry_B_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,entry_B_lo_box,Bounds.contains]
  have hs := entry_B_lo_sound (env P Q A B) hv
  rw [RBexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem entry_B_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (5/2:ℝ) ≤ B ∧ B ≤ (3:ℝ))
    : RB P.r P.h P.u Q A B ≤ -(1:ℝ) := by
  have hv : ∀ i, (entry_B_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,entry_B_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,entry_B_hi_box,Bounds.contains]
  have hs := entry_B_hi_sound (env P Q A B) hv
  rw [RBexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem entry_Q_lo (P : Parameters) (Q A B : ℝ)
    (hQ : (1/4:ℝ) ≤ Q ∧ Q ≤ (1/2:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ))
    : (1/10:ℝ) ≤ RQ P.r P.h Q A B := by
  have hv : ∀ i, (entry_Q_lo_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,entry_Q_lo_box,Bounds.contains]; exact P.hb4
    · simp [env,entry_Q_lo_box,Bounds.contains]
  have hs := entry_Q_lo_sound (env P Q A B) hv
  rw [RQexpr_eq_source, sourceRates_env] at hs
  exact hs

theorem entry_Q_hi (P : Parameters) (Q A B : ℝ)
    (hQ : (3/4:ℝ) ≤ Q ∧ Q ≤ (1:ℝ))
    (hA : (7/2:ℝ) ≤ A ∧ A ≤ (9/2:ℝ))
    (hB : (3/2:ℝ) ≤ B ∧ B ≤ (5/2:ℝ))
    : RQ P.r P.h Q A B ≤ -(1/10:ℝ) := by
  have hv : ∀ i, (entry_Q_hi_box i).contains (env P Q A B i) := by
    intro i
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact ⟨P.hh.1.le, P.hh.2⟩
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact ⟨P.hu.1.le, P.hu.2⟩
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact hQ
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact hA
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact hB
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.ha1
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.ha2
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.ha3
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.hK
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.hb1
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.hb2
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.hb3
    rcases i with _ | i
    · norm_num [env,entry_Q_hi_box,Bounds.contains]; exact P.hb4
    · simp [env,entry_Q_hi_box,Bounds.contains]
  have hs := entry_Q_hi_sound (env P Q A B) hv
  rw [RQexpr_eq_source, sourceRates_env] at hs
  exact hs

end ReverseRateLimits.SourceBounds

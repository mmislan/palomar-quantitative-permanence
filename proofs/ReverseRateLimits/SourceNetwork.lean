module
public import proofs.ReverseRateLimits.CorridorDynamics
public import proofs.ReverseRateLimits.Upstream.Model

@[expose] public section

namespace ReverseRateLimits.SourceNetwork
open CoupledSource SourceBounds OAI.Problem326
open scoped BigOperators
noncomputable section

def c0 : Fin 3 → ℕ := ![0,2,1]
def c1 : Fin 3 → ℕ := ![2,0,0]
def c2 : Fin 3 → ℕ := ![1,0,2]
def c3 : Fin 3 → ℕ := ![0,2,0]
def c4 : Fin 3 → ℕ := ![2,1,0]
def c5 : Fin 3 → ℕ := ![0,0,2]
def c6 : Fin 3 → ℕ := ![0,0,3]
def c7 : Fin 3 → ℕ := ![1,0,0]

def complexes : Finset (Fin 3 → ℕ) := {c0,c1,c2,c3,c4,c5,c6,c7}
def reactions : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) :=
  {(c0,c1),(c1,c0),(c2,c3),(c3,c2),(c4,c5),(c5,c4),(c6,c7),(c7,c6)}

def network : ReactionNetwork 3 where
  complexes := complexes
  reactions := reactions
  source_mem := by
    intro e he
    simp only [reactions,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [complexes]
  target_mem := by
    intro e he
    simp only [reactions,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [complexes]
  source_ne_target := by
    intro e he
    simp only [reactions,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals intro h; have h0 := congrFun h 0; norm_num [c0,c1,c2,c3,c4,c5,c6,c7] at h0

theorem weakly_reversible : WeaklyReversible network := by
  rintro ⟨e,he⟩
  apply Relation.TransGen.single
  simp only [network,reactions,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [HasReaction,network,reactions]

def rawRate (P : Parameters) (e : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : ℝ :=
  if e = (c0,c1) then P.r.a1 else
  if e = (c1,c0) then P.r.b1*P.p^2 else
  if e = (c2,c3) then P.r.a2 else
  if e = (c3,c2) then P.r.b2*P.p^2 else
  if e = (c4,c5) then P.r.a3 else
  if e = (c5,c4) then P.r.b3*P.p*P.h^6 else
  if e = (c6,c7) then P.r.k else P.r.b4*P.p^2

def rate (P : Parameters) (e : Reaction network) : ℝ := rawRate P e.val

theorem rates_positive (P : Parameters) : ∀ e, 0 < rate P e := by
  intro e
  have ha1 : 0 < P.r.a1 := (by norm_num : (0:ℝ) < 99/100).trans_le P.ha1.1
  have ha2 : 0 < P.r.a2 := (by norm_num : (0:ℝ) < 99/100).trans_le P.ha2.1
  have ha3 : 0 < P.r.a3 := (by norm_num : (0:ℝ) < 99/100).trans_le P.ha3.1
  have hk : 0 < P.r.k := (by norm_num : (0:ℝ) < 99/25).trans_le P.hK.1
  have hb1 : 0 < P.r.b1 := (by norm_num : (0:ℝ) < 99/100).trans_le P.hb1.1
  have hb2 : 0 < P.r.b2 := (by norm_num : (0:ℝ) < 99/100).trans_le P.hb2.1
  have hb3 : 0 < P.r.b3 := (by norm_num : (0:ℝ) < 99/100).trans_le P.hb3.1
  have hb4 : 0 < P.r.b4 := (by norm_num : (0:ℝ) < 99/100).trans_le P.hb4.1
  have hp := P.p_pos
  have hh := P.hh.1
  unfold rate rawRate
  split_ifs <;> positivity

/-- The public reaction-network field is exactly the original four currents. -/
theorem field_identity (P : Parameters) (x : Fin 3 → ℝ) :
    massAction network (rate P) x =
      ![dx P.r P.p P.h (x 0) (x 1) (x 2),
        dy P.r P.p P.h (x 0) (x 1) (x 2),
        dz P.r P.p P.h (x 0) (x 1) (x 2)] := by
  ext i
  unfold massAction rate
  change (∑ e : network.reactions,
    (fun q : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      rawRate P q * monomial x q.1 * ((q.2 i:ℝ)-(q.1 i:ℝ))) e) = _
  rw [Finset.sum_coe_sort network.reactions
    (fun q => rawRate P q * monomial x q.1 * ((q.2 i:ℝ)-(q.1 i:ℝ)))]
  fin_cases i <;>
    norm_num [network,reactions,rawRate,monomial,c0,c1,c2,c3,c4,c5,c6,c7,
      Fin.prod_univ_succ,Matrix.cons_val_succ,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,dx,dy,dz,j1,j2,j3,j4] <;> ring

end
end ReverseRateLimits.SourceNetwork

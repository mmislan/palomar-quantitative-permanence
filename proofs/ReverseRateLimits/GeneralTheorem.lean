module
public import proofs.ReverseRateLimits.ClasswiseAbsorption
public import proofs.ReverseRateLimits.RateScale

@[expose] public section

namespace ReverseRateLimits
open OAI.Problem326
open scoped BigOperators
noncomputable section

/-- Parameter-uniform general quantitative root. H is chosen from the network
alone; A precedes the exponent interval, epsilon and arbitrary bounded prefactors.
All global literal solutions in the fixed positive compatibility class are absorbed. -/
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
  classical
  obtain ⟨G⟩ := exists_network_geometry N
  refine ⟨G.H,G.H_pos,?_⟩
  intro c hc lower upper hlower hupper
  obtain ⟨A,hA,hA1,hgeo,hAmargin⟩ := exists_rate_scale_constant G c lower upper hlower
  refine ⟨A,hA,hA1,?_⟩
  intro exponent amin amax _hmin hspread hexponent epsilon hepsilon hepsilon1 prefactor hbox x0 hx0 hclass
  let target := A*epsilon^((amax-amin)/G.H)
  let k := fun e => rate epsilon (prefactor e) (exponent e)
  have hmargin := power_rate_margin G A epsilon lower upper amin amax prefactor exponent
    hA hepsilon hepsilon1 hlower (hlower.le.trans hupper) hspread hbox hexponent hAmargin
  let D : ℕ := ∑ e : Reaction N, ∑ i, e.val.1 i
  have hdegree : ∀ e : Reaction N, ∑ i, e.val.1 i ≤ D := by
    intro e
    exact Finset.single_le_sum (f := fun f : Reaction N => ∑ i, f.val.1 i)
      (fun f _ => Nat.zero_le _) (Finset.mem_univ e)
  have hroot := classwise_absorption hd N G c hc k (lower*epsilon^amax) target D hweak
    (mul_pos hlower (Real.rpow_pos_of_pos hepsilon _)) hmargin.2.1
    hmargin.1.1 (hmargin.1.2.trans_lt hA1)
    (fun h hh hle => hgeo h hh (hle.trans hmargin.1.2)) hmargin.2.2 hdegree x0 hx0 hclass
  have hsqrt : target^(1/2:ℝ) = A^(1/2:ℝ)*epsilon^((amax-amin)/(2*G.H)) := by
    dsimp only [target]
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hepsilon.le _),← Real.rpow_mul hepsilon.le]
    congr 2
    field_simp
  simpa only [hsqrt] using hroot

end
end ReverseRateLimits

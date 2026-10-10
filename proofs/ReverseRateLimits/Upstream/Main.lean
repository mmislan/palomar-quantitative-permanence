module
/- Upstream: openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a.
   Imports restricted to the actual root dependencies; theorem bodies unchanged. -/
public import proofs.ReverseRateLimits.Upstream.AffineExistence
public import proofs.ReverseRateLimits.Upstream.UniformAffineData
public import proofs.ReverseRateLimits.Upstream.BarrierInvariance
public import proofs.ReverseRateLimits.Upstream.CompactInvariance

@[expose] public section

namespace OAI

noncomputable section

namespace Problem326

theorem compact_convex_invariant_polytope :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ K : Set (Fin d → ℝ),
        IsCompact K ∧ Convex ℝ K ∧ IsFinitePolyhedron K ∧
        x0 ∈ K ∧ K ⊆ {x | PositiveState x} ∧ IsForwardInvariant N κ K := by
  intro d N κ _ hweak hκ x0 hx0
  apply BarrierConstruction.compact_convex_invariant_polytope_of_uniform ?_
    N κ hweak hκ x0 hx0
  exact Affine.uniform_affine_data_of_full_certificates
    (fun E hE => Affine.exists_fullCertificate d (-1) 1 E (by norm_num)
      (fun r _ => hE r))

theorem global_bounded_persistent_solution :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
        ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  intro d N κ hd hweak hκ x0 hx0
  obtain ⟨K, hK, _, _, hxK, hpos, hinv⟩ :=
    compact_convex_invariant_polytope d N κ hd hweak hκ x0 hx0
  exact global_bounds_of_compact_invariant N κ x0 hK hxK hpos hinv

end Problem326

end

end OAI


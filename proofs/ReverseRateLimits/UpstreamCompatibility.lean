module
public import proofs.ReverseRateLimits.Upstream.Main

@[expose] public section

namespace ReverseRateLimits
open OAI.Problem326

/-- The attributed published endpoint, compiled against this repository's
frozen environment. It supplies existence, not the new classwise absorption. -/
theorem published_global_solution (d : ℕ) (N : ReactionNetwork d) (k : Reaction N → ℝ)
    (hd : 0 < d) (hweak : WeaklyReversible N) (hk : ∀ e, 0 < k e)
    (x0 : Fin d → ℝ) (hx0 : PositiveState x0) :
    ∃ x : ℝ → Fin d → ℝ, IsGlobalForwardSolution N k x0 x ∧
      ∀ t, 0 ≤ t → PositiveState (x t) := by
  obtain ⟨ε, hε, _, ⟨x,hx⟩, hbounds⟩ :=
    global_bounded_persistent_solution d N k hd hweak hk x0 hx0
  exact ⟨x,hx,fun t ht i => hε.trans_le (hbounds x hx t ht i).1⟩

end ReverseRateLimits

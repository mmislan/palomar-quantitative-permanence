module
public import proofs.ReverseRateLimits.Upstream.AffineExistence
public import proofs.ReverseRateLimits.Upstream.UniformAffineData
public import proofs.ReverseRateLimits.Upstream.NetworkBarrier

@[expose] public section

namespace ReverseRateLimits
open OAI.Problem326

/-- The attributed affine existence input, retained with its slope cube fields. -/
theorem published_full_certificate (d : ℕ) (E : (Fin d → ℝ) → ℝ)
    (hE : ∀ r, Affine.Cube (-1) 1 r → 0 < E r) :
    Nonempty (Affine.FullCertificate d (-1) 1 E) :=
  Affine.exists_fullCertificate d (-1) 1 E (by norm_num) hE

/-- Exact locally compiled published geometry; no rate or absorption assumption. -/
theorem published_uniform_geometry (d : ℕ) :
    BarrierConstruction.UniformAffineApproximation d := by
  exact Affine.uniform_affine_data_of_full_certificates
    (fun E hE => Affine.exists_fullCertificate d (-1) 1 E (by norm_num)
      (fun r _ => hE r))

end ReverseRateLimits

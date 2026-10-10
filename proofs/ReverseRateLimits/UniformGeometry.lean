module
public import proofs.ReverseRateLimits.GeometryBridge

@[expose] public section

namespace ReverseRateLimits
open OAI.Problem326
open scoped BigOperators
noncomputable section

/-- Geometry retains the fixed label bank and its slope cube. Every field
is constructed before any reaction rate or small parameter is specified. -/
structure NetworkGeometry {d : ℕ} (N : ReactionNetwork d) where
  E : (Fin d → ℝ) → ℝ
  E_pos : ∀ r, 0 < E r
  E_half : ∀ r, E r ≤ 1/2
  sign_close : ∀ r p : Fin d → ℝ, (∀ i, |p i-r i| < E r) →
    ∀ v ∈ BarrierConstruction.comparisonDirections N, dot r v ≠ 0 →
      (0 < dot p v ↔ 0 < dot r v) ∧ (dot p v < 0 ↔ dot r v < 0) ∧
        |dot r v|/2 < |dot p v|
  certificate : Affine.FullCertificate d (-1) 1 E
  hmax : ℝ
  hmax_pos : 0 < hmax
  uniform : ∀ h, 0 < h → h < hmax → ∀ p : Fin d → ℝ,
    Affine.Cube (-1) 1 p → ∀ L ∈ certificate.labels,
    Affine.Active certificate.labels L h (Affine.powerPoint h p) →
      ‖p-L.slope‖ < E L.slope
  H : ℝ
  H_pos : 0 < H
  H_one : H ≤ 1
  gap : ∀ L ∈ certificate.labels, ∀ v ∈ BarrierConstruction.comparisonDirections N,
    dot L.slope v ≠ 0 → H ≤ |dot L.slope v|/2

theorem exists_network_geometry {d : ℕ} (N : ReactionNetwork d) : Nonempty (NetworkGeometry N) := by
  classical
  obtain ⟨E,hE,hclose⟩ := exists_sign_tolerance_function (BarrierConstruction.comparisonDirections N)
  obtain ⟨C⟩ := published_full_certificate d E (fun r _ => (hE r).1)
  obtain ⟨hmax,hmaxp,huniform⟩ := C.uniform_activity
  obtain ⟨H,hHp,hH1,hgap⟩ := exists_uniform_dot_gap
    (C.labels.image Affine.Label.slope) (BarrierConstruction.comparisonDirections N)
  exact ⟨{
    E := E
    E_pos := fun r => (hE r).1
    E_half := fun r => (hE r).2
    sign_close := hclose
    certificate := C
    hmax := hmax
    hmax_pos := hmaxp
    uniform := huniform
    H := H
    H_pos := hHp
    H_one := hH1
    gap := fun L hL v hv hn => hgap L.slope (Finset.mem_image_of_mem _ hL) v hv hn }⟩

end
end ReverseRateLimits

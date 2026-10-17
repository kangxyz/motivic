module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.ZeroNeighborhoodBoundary
/-! # Actual affine refinement of a zero-section neighborhood

The defining polynomial is not assumed monic. Its value at zero determines
the permitted base shrinking, so the entire zero section on that base remains.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]

/-- A principal affine neighborhood containing zero after an explicit principal base shrink. -/
theorem exists_principal_zero_neighborhood
    (V : (Spec (.of (Polynomial R))).Opens)
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ f : Polynomial R, s ∈ PrimeSpectrum.basicOpen (f.eval 0) ∧
      PrimeSpectrum.basicOpen f ≤ V ∧
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen f = PrimeSpectrum.basicOpen (f.eval 0) := by
  let z := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
  obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp V.isOpen _ (hV ⟨s, rfl⟩)
  refine ⟨f, ?_, hsub, ?_⟩
  · exact hf
  · exact SpecMap_preimage_basicOpen _ f
end AlgebraicGeometry.RelativeProjectiveLine

module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.SimultaneousBoundaryFrames
/-! # Same-base constructed graph and all-degree full boundary frames -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable (R : Type u) [CommRing R] (ι : Type u)
  {X Z D : Scheme.{u}} [IsAffine X]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (z : Z ⟶ X) [IsFinite (z ≫ q)]
  (g : D ⟶ ProjectiveSpace R ι) [IsFinite (g ≫ toSpec R ι)] (x : X)
example : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ V : (Spec (.of R)).Opens, IsAffineOpen V ∧ q x ∈ V ∧
    ∃ h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U,
      IsAffineOpen (boundaryBaseSourceOpen q U V) ∧
      Nonempty (SheafOfModules.unit
        (pullback (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V)).ringCatSheaf ≅
        idealModule (boundaryGraphTarget (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h))) ∧
      Nonempty ((n : ℕ) →
        (Scheme.Modules.pullback (((g ≫ toSpec R ι) ⁻¹ᵁ V).ι ≫ g)).obj
          (twistingSheaf R ι (n : ℤ)) ≅
            SheafOfModules.unit ((g ≫ toSpec R ι) ⁻¹ᵁ V).toScheme.ringCatSheaf) :=
  exists_simultaneous_boundary_frames R ι q z g x
#print axioms exists_simultaneous_boundary_frames
end AlgebraicGeometry.Scheme.Hom

module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.SimultaneousNativeFrames
/-! # Constructed native frames on one actual affine base neighborhood -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
example
    (R : Type u) [CommRing R] (ι : Type u)
    {X Z C D : Scheme.{u}} [IsAffine X]
    (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (z : Z ⟶ X) [IsFinite (z ≫ q)]
    (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C)
    [IsFinite ((d ≫ f) ≫ toSpec R ι)] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      q x ∈ V ∧
      ∃ h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U,
        IsAffineOpen (boundaryBaseSourceOpen q U V) ∧
        Nonempty (SheafOfModules.unit
          (pullback (boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom)
            (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V ≫
              V.toScheme.isoSpec.hom)).ringCatSheaf ≅
          idealModule (boundaryGraphTarget
            (boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom)
            (boundaryBaseLift q z U V h))) ∧
        Nonempty ((n : ℕ) →
          (Modules.pullback (boundaryBaseWholeMap (f ≫ toSpec R ι) d V ≫
            boundaryBaseProjectiveMap R ι f V)).obj
              (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≅
          SheafOfModules.unit ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf) :=
  exists_simultaneous_native_boundary_frames R ι q z f d x
#print axioms exists_simultaneous_native_boundary_frames
end AlgebraicGeometry.Scheme.Hom

module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseWholeTarget
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PrescribedBoundaryTwistTransport
/-! # The same whole-boundary frame in the native projective coordinates of the smaller base -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable (R : Type u) [CommRing R] (ι : Type u) {C D : Scheme.{u}}
  (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C)
  (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]

/-- The actual whole-boundary map has the literal coefficient-change square. -/
@[reassoc]
theorem boundaryBaseWholeMap_projective_map :
    (boundaryBaseWholeMap (f ≫ toSpec R ι) d V ≫ boundaryBaseProjectiveMap R ι f V) ≫
      ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι) ι =
    ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).ι ≫ d ≫ f := by
  simp only [boundaryBaseProjectiveMap, Category.assoc,
    ConstantCurve.affineSourceToProjectiveSpace_map]
  rw [boundaryBaseWholeMap_snd_assoc]

/-- No further shrink and no replacement frame: the originally constructed frame is
transported to the native relative twisting sheaf by its actual coefficient-change iso. -/
def boundaryBaseWholeTwistFrame (n : ℕ)
    (e : (Modules.pullback (((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).ι ≫ d ≫ f)).obj
      (twistingSheaf R ι (n : ℤ)) ≅
        SheafOfModules.unit ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf) :
    (Modules.pullback (boundaryBaseWholeMap (f ≫ toSpec R ι) d V ≫
      boundaryBaseProjectiveMap R ι f V)).obj
      (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf :=
  CoherentGraph.prescribedBoundaryRelativeTwistIso R Γ(V.toScheme, ⊤)
    (ConstantCurve.affineSourceCoefficientMap R V.ι) ι
    (((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).ι ≫ d ≫ f) (𝟙 _)
    (boundaryBaseWholeMap (f ≫ toSpec R ι) d V ≫ boundaryBaseProjectiveMap R ι f V)
    (by simpa using boundaryBaseWholeMap_projective_map R ι f d V) n e
end AlgebraicGeometry.Scheme.Hom

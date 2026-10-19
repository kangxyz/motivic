module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.TwistFrame
/-! # The same prescribed whole-boundary frame in native relative projective coordinates -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory AlgebraicGeometry ProjectiveSpace
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable (R : Type u) [CommRing R] (ι : Type u) {C D : Scheme.{u}}
  (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C)
  (V : (Spec (.of R)).Opens) [IsAffine V.toScheme] (n : ℕ)
  (e : (Modules.pullback (((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).ι ≫ d ≫ f)).obj
    (twistingSheaf R ι (n : ℤ)) ≅
      SheafOfModules.unit ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf)
example : (Modules.pullback
    (boundaryBaseWholeMap (f ≫ toSpec R ι) d V ≫ boundaryBaseProjectiveMap R ι f V)).obj
      (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf :=
  boundaryBaseWholeTwistFrame R ι f d V n e
#print axioms boundaryBaseWholeTwistFrame
#print axioms boundaryBaseWholeMap_projective_map
end AlgebraicGeometry.Scheme.Hom

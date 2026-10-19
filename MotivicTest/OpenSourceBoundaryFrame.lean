module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.OpenSourceBoundaryFrame
/-! # The frame uses the original open restriction and literal canonical inclusion -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (U : X.Opens) (z : Z ⟶ X)
  (s : Z ⟶ U.toScheme) (hs : s ≫ U.ι = z)
  (e : (idealModule (boundaryGraphTarget q z)).restrict
    ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
    SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf)
example : SheafOfModules.unit (pullback (U.ι ≫ q) (s ≫ (U.ι ≫ q))).ringCatSheaf ≅
    idealModule (boundaryGraphTarget (U.ι ≫ q) s) :=
  openCanonicalBoundaryFrame q U z s hs e
#print axioms openCanonicalBoundaryFrame
#print axioms openCanonicalBoundaryFrame_inclusion
#print axioms exists_affine_restrictedBoundaryGraphFrame
end AlgebraicGeometry.Scheme.Hom

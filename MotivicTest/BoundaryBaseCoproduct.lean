module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseCoproduct
/-! # The original full boundary frame, without replacing either component by its reduction -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C D Z : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C) (z : Z ⟶ C) (V : S.Opens)
example : boundaryBaseCoproductMap π d z V ≫
    boundaryBaseWholeMap π (coprod.desc d z) V =
      coprod.desc (boundaryBaseWholeMap π d V) (boundaryBaseWholeMap π z V) :=
  boundaryBaseCoproductMap_boundary π d z V
example (M : (boundaryBaseCompactification π V).Modules)
    (e : (Modules.pullback (boundaryBaseWholeMap π (coprod.desc d z) V)).obj M ≅
      SheafOfModules.unit ((coprod.desc d z ≫ π) ⁻¹ᵁ V).toScheme.ringCatSheaf) :
    (Modules.pullback (coprod.desc (boundaryBaseWholeMap π d V)
      (boundaryBaseWholeMap π z V))).obj M ≅
      SheafOfModules.unit
        (((d ≫ π) ⁻¹ᵁ V).toScheme ⨿ ((z ≫ π) ⁻¹ᵁ V).toScheme).ringCatSheaf :=
  boundaryBaseCoproductFrame π d z V M e
#print axioms boundaryBaseCoproductMap_boundary
#print axioms boundaryBaseCoproductFrame
end AlgebraicGeometry.Scheme.Hom

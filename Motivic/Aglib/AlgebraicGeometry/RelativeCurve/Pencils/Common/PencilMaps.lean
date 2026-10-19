module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.PencilBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.PencilUnit
/-! # The literal global relative correcting pencil, before restricting its zero family -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B C : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a ≫ q) π))

abbrev commonPencilBundle := tensorLineBundle (commonAmbient π j α)
  (pullbackLineBundle (commonToLambda π j α)
    (dualLineBundle _ (tensorLineBundle _ T
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))))
  (pullbackLineBundle (commonToPsi q π j p hq a α β h) (dualLineBundle _ N))

def commonPencilStart
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val) :
    (commonPencilBundle q π j p hq a α β h T N).val ⟶
      SheafOfModules.unit (commonAmbient π j α).ringCatSheaf :=
  mixedProductFunctional (commonToLambda π j α) (commonToPsi q π j p hq a α β h)
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) N
    (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
      (Hom.idealInclusion (Hom.compactificationGraph π j)) bS) dS

def commonPencilEnd
    (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (nS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val) :
    (commonPencilBundle q π j p hq a α β h T N).val ⟶
      SheafOfModules.unit (commonAmbient π j α).ringCatSheaf :=
  mixedProductFunctional (commonToLambda π j α) (commonToPsi q π j p hq a α β h)
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) N aS nS
end AlgebraicGeometry.Scheme.RelativeCurvePencil

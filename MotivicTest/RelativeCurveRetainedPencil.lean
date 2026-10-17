module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedPencilCompactIso
/-! # Literal compact-pencil endpoint transport on the original retained graph domain -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B C V : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a₀ : A ⟶ X)
  (α : B ⟶ Y) [Flat α] (β : B ⟶ A) (h : α ≫ p = β ≫ a₀)
  (v : V ⟶ C) [IsOpenImmersion v] (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
  (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a₀ ≫ q) π))

example
    (b : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf ⟶ N.val) :
    (retainedPencilCompactIso q π j p hq a₀ α β h v φ hφ T N).hom ≫
      Hom.pullbackToUnit
        (mixedProductFunctional (commonToLambda π j α) (commonToPsi q π j p hq a₀ α β h)
          (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) N
          (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
            (Hom.idealInclusion
              (Hom.compactificationGraph π j)) b) d)
        (retainedProductInclusion (commonProjection π j α) π v) =
    Hom.productSection (Hom.idealInclusion (relativeRetainedGraph π j α v φ hφ))
      (Hom.productSection
        (retainedLambdaFunctional π j α v (sectionDualFunctional _ T b))
        (retainedPsiFunctional q π j p hq a₀ α β h v (sectionDualFunctional _ N d))) :=
  retainedPencilCompactIso_start q π j p hq a₀ α β h v φ hφ T N b d

example
    (a : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (n : SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf ⟶ N.val) :
    (retainedPencilCompactIso q π j p hq a₀ α β h v φ hφ T N).hom ≫
      Hom.pullbackToUnit
        (mixedProductFunctional (commonToLambda π j α) (commonToPsi q π j p hq a₀ α β h)
          (tensorLineBundle _ T (dualLineBundle _
            (Hom.relativeCompactificationGraphLine π j))) N a n)
        (retainedProductInclusion (commonProjection π j α) π v) =
    (retainedPencilLineIso q π j p hq a₀ α β h v φ hφ T N).hom ≫
      Hom.productSection
        (retainedLambdaFunctional π j α v
          (sectionDualFunctional _ (tensorLineBundle _ T (dualLineBundle _
            (Hom.relativeCompactificationGraphLine π j))) a))
        (retainedPsiFunctional q π j p hq a₀ α β h v (sectionDualFunctional _ N n)) :=
  retainedPencilCompactIso_end q π j p hq a₀ α β h v φ hφ T N a n

#print axioms retainedPencilCompactIso_start
#print axioms retainedPencilCompactIso_end
end AlgebraicGeometry.Scheme.RelativeCurvePencil

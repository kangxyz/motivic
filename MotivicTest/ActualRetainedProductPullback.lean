module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Retained.ProductPullback
/-! # Direct compact-product restriction consumer -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
open Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (v : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (U : (Spec (.of (Polynomial k))).Opens)

omit [IsSeparated p] [IsOpenImmersion r] in
example
    (L : LineBundle (diagonalAmbient k p r)) (M : LineBundle (fixedAmbient k p v))
    (a : L.val ⟶ SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf) :
    (retainedProductPullbackIso k p r v α β h U L M).hom ≫
      Hom.pullbackToUnit
        (Hom.productSection (Hom.pullbackToUnit a (commonToDiagonal k p r α))
          (Hom.pullbackToUnit b (commonToFixed k p r v α β h)))
        (constantRetainedInclusion k p U (commonSourceProjection k p r α)) =
    Hom.productSection (retainedDiagonalFunctional k p r α U a)
      (retainedFixedFunctional k p r v α β h U b) :=
  retainedProductPullbackIso_functional k p r v α β h U L M a b

open Lean in
run_cmd do
  for name in #[``retainedProductPullbackIso, ``retainedProductPullbackIso_functional,
      ``retainedPencilCompactIso_start, ``retainedPencilCompactIso_end] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on unsupported assumption {axiomName}"
  logInfo "Original compact and twice-retained product functionals agree under the canonical iso."

module
import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualRetainedPencilComparison
/-! # Direct retained endpoint comparison and foundational audit -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.AffineLineEtaleCompactification
universe u
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (v : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (U : (Spec (.of (Polynomial k))).Opens)
  (φ : X ⟶ Limits.pullback U.ι p)
  (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p)
  [Flat α] (T : LineBundle (diagonalAmbient k p r))
  (N : LineBundle (fixedAmbient k p v))

omit [IsOpenImmersion r] in
example
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val) :
    (retainedPencilLineIso k p r v α β h U φ hφ T N).hom ≫
      Hom.productSection
        (retainedDiagonalFunctional k p r α U
          (sectionDualFunctional _ (tensorLineBundle _ T (actualDivisorLineBundle k p r))
            (twistedIdealSection _ (actualIdealLineBundle k p r) T
              (Scheme.Hom.idealInclusion
                (Scheme.Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) b)))
        (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N d)) =
    Hom.productSection (Scheme.Hom.idealInclusion (commonRetainedGraph k p r α U φ hφ))
      (Hom.productSection
        (retainedDiagonalFunctional k p r α U (sectionDualFunctional _ T b))
        (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N d))) :=
  retainedPencilLineIso_start k p r v α β h U φ hφ T N b d

open Lean in
run_cmd do
  for name in #[``retainedPencilLineIso_start, ``retainedPencilLineIso,
      ``retainedToDiagonal_isPullback, ``retainedToFixed_isPullback,
      ``commonRetainedGraph_locallyRankOne] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on unsupported assumption {axiomName}"
  logInfo "Retained source changes and graph-product comparison use standard foundations."

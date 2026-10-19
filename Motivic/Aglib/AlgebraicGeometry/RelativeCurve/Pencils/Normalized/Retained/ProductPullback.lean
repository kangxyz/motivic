module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Retained.PencilComparison
/-! # The original retained factor product and the compact pencil restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
private theorem pullbackToUnit_comp {W C Z : Scheme.{u}}
    (f : W ⟶ C) (g : C ⟶ Z) {L : Z.Modules}
    (a : L ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    Hom.pullbackToUnit (Hom.pullbackToUnit a g) f =
      (Modules.pullbackComp f g).hom.app L ≫ Hom.pullbackToUnit a (f ≫ g) :=
  GlobalBoundaryPencil.pullback_map_comp f g a

variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (v : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (U : (Spec (.of (Polynomial k))).Opens)

/-- The two genuine routes to the compact lambda line. -/
def retainedDiagonalToCompactPullbackIso (L : LineBundle (diagonalAmbient k p r)) :
    (retainedDiagonalLine k p r α U L).val ≅
    (Modules.pullback (constantRetainedInclusion k p U
      (commonSourceProjection k p r α))).obj
      ((Modules.pullback (commonToDiagonal k p r α)).obj L.val) :=
  (retainedDiagonalPullbackIso k p r α U).app L.val ≪≫
    ((Modules.pullbackComp
      (constantRetainedInclusion k p U (commonSourceProjection k p r α))
      (commonToDiagonal k p r α)).app L.val).symm

/-- The two genuine routes to the compact fixed-U line. -/
def retainedFixedToCompactPullbackIso (L : LineBundle (fixedAmbient k p v)) :
    (retainedFixedLine k p r v α β h U L).val ≅
    (Modules.pullback (constantRetainedInclusion k p U
      (commonSourceProjection k p r α))).obj
      ((Modules.pullback (commonToFixed k p r v α β h)).obj L.val) :=
  (retainedFixedPullbackIso k p r v α β h U).app L.val ≪≫
    ((Modules.pullbackComp
      (constantRetainedInclusion k p U (commonSourceProjection k p r α))
      (commonToFixed k p r v α β h)).app L.val).symm

omit [IsSeparated p] [IsOpenImmersion r] in
theorem retainedDiagonalToCompactPullbackIso_functional
    (L : LineBundle (diagonalAmbient k p r))
    (a : L.val ⟶ SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf) :
    (retainedDiagonalToCompactPullbackIso k p r α U L).hom ≫
      Hom.pullbackToUnit (Hom.pullbackToUnit a (commonToDiagonal k p r α))
        (constantRetainedInclusion k p U (commonSourceProjection k p r α)) =
    retainedDiagonalFunctional k p r α U a := by
  rw [pullbackToUnit_comp]
  simp only [retainedDiagonalToCompactPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact (retainedDiagonalFunctional_eq k p r α U a).symm

omit [IsSeparated p] [IsOpenImmersion r] in
theorem retainedFixedToCompactPullbackIso_functional
    (L : LineBundle (fixedAmbient k p v))
    (a : L.val ⟶ SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf) :
    (retainedFixedToCompactPullbackIso k p r v α β h U L).hom ≫
      Hom.pullbackToUnit (Hom.pullbackToUnit a (commonToFixed k p r v α β h))
        (constantRetainedInclusion k p U (commonSourceProjection k p r α)) =
    retainedFixedFunctional k p r v α β h U a := by
  rw [pullbackToUnit_comp]
  simp only [retainedFixedToCompactPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact (retainedFixedFunctional_eq k p r v α β h U a).symm

/-- The original twice-retained factor domain is the pullback of the compact product. -/
def retainedProductPullbackIso
    (L : LineBundle (diagonalAmbient k p r)) (M : LineBundle (fixedAmbient k p v)) :
    tensorSheaf _ (retainedDiagonalLine k p r α U L).val
      (retainedFixedLine k p r v α β h U M).val ≅
    (Modules.pullback (constantRetainedInclusion k p U (commonSourceProjection k p r α))).obj
      (tensorLineBundle _ (pullbackLineBundle (commonToDiagonal k p r α) L)
        (pullbackLineBundle (commonToFixed k p r v α β h) M)).val :=
  tensorSheafIso _ (retainedDiagonalToCompactPullbackIso k p r α U L)
    (retainedFixedToCompactPullbackIso k p r v α β h U M) ≪≫
  (PullbackTensor.Local.pullbackLineBundleTensorIso
    (constantRetainedInclusion k p U (commonSourceProjection k p r α))
    (pullbackLineBundle (commonToDiagonal k p r α) L)
    (pullbackLineBundle (commonToFixed k p r v α β h) M)).symm

omit [IsSeparated p] [IsOpenImmersion r] in
/-- The comparison preserves the literal product of the original functionals. -/
theorem retainedProductPullbackIso_functional
    (L : LineBundle (diagonalAmbient k p r)) (M : LineBundle (fixedAmbient k p v))
    (a : L.val ⟶ SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf) :
    (retainedProductPullbackIso k p r v α β h U L M).hom ≫
      Hom.pullbackToUnit
        (Hom.productSection (Hom.pullbackToUnit a (commonToDiagonal k p r α))
          (Hom.pullbackToUnit b (commonToFixed k p r v α β h)))
        (constantRetainedInclusion k p U (commonSourceProjection k p r α)) =
    Hom.productSection (retainedDiagonalFunctional k p r α U a)
      (retainedFixedFunctional k p r v α β h U b) := by
  rw [Hom.pullbackToUnit_productSection_lineBundle _
    (pullbackLineBundle (commonToDiagonal k p r α) L)
    (pullbackLineBundle (commonToFixed k p r v α β h) M)]
  simp only [retainedProductPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorSheafIso_productSection, retainedDiagonalToCompactPullbackIso_functional,
    retainedFixedToCompactPullbackIso_functional]

variable (φ : X ⟶ pullback U.ι p)
  (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p)
  [Flat α] (T : LineBundle (diagonalAmbient k p r))
  (N : LineBundle (fixedAmbient k p v))

/-- The original graph-domain line is compared to the literal compact pencil domain. -/
def retainedPencilCompactIso :=
  retainedPencilLineIso k p r v α β h U φ hφ T N ≪≫
    retainedProductPullbackIso k p r v α β h U
      (dualLineBundle _ (tensorLineBundle _ T (actualDivisorLineBundle k p r)))
      (dualLineBundle _ N)

omit [IsOpenImmersion r] in
/-- The compact start is the actual retained graph times the original pole product. -/
theorem retainedPencilCompactIso_start
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val) :
    (retainedPencilCompactIso k p r v α β h U φ hφ T N).hom ≫
      Hom.pullbackToUnit
        (mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h)
          (tensorLineBundle _ T (actualDivisorLineBundle k p r)) N
          (twistedIdealSection _ (actualIdealLineBundle k p r) T
            (Hom.idealInclusion
              (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) b) d)
        (constantRetainedInclusion k p U (commonSourceProjection k p r α)) =
    Hom.productSection (Hom.idealInclusion (commonRetainedGraph k p r α U φ hφ))
      (Hom.productSection
        (retainedDiagonalFunctional k p r α U (sectionDualFunctional _ T b))
        (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N d))) := by
  simp only [retainedPencilCompactIso, Iso.trans_hom, Category.assoc, mixedProductFunctional]
  rw [retainedProductPullbackIso_functional]
  exact retainedPencilLineIso_start k p r v α β h U φ hφ T N b d

omit [IsOpenImmersion r] in
/-- The compact end is the original numerator product through the unchanged Data line iso. -/
theorem retainedPencilCompactIso_end
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
    (n : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val) :
    (retainedPencilCompactIso k p r v α β h U φ hφ T N).hom ≫
      Hom.pullbackToUnit
        (mixedProductFunctional (commonToDiagonal k p r α) (commonToFixed k p r v α β h)
          (tensorLineBundle _ T (actualDivisorLineBundle k p r)) N a n)
        (constantRetainedInclusion k p U (commonSourceProjection k p r α)) =
    (retainedPencilLineIso k p r v α β h U φ hφ T N).hom ≫
      Hom.productSection
        (retainedDiagonalFunctional k p r α U
          (sectionDualFunctional _ (tensorLineBundle _ T (actualDivisorLineBundle k p r)) a))
        (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N n)) := by
  simp only [retainedPencilCompactIso, Iso.trans_hom, Category.assoc, mixedProductFunctional]
  rw [retainedProductPullbackIso_functional]

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

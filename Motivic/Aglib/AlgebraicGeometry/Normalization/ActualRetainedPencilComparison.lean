module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualCommonGraphIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.MixedProductBoundaryPullback
/-! # Original retained curves and their canonical pencil line comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible
/-- Tensoring actual line comparisons preserves the original product functional. -/
theorem tensorSheafIso_productSection {W : Scheme.{u}} {L L' M M' : W.Modules}
    (e : L ≅ L') (f : M ≅ M')
    (a : L' ⟶ SheafOfModules.unit W.ringCatSheaf)
    (b : M' ⟶ SheafOfModules.unit W.ringCatSheaf) :
    (tensorSheafIso W e f).hom ≫ Hom.productSection a b =
      Hom.productSection (e.hom ≫ a) (f.hom ≫ b) :=
  Hom.productSection_naturality e.hom f.hom a b

/-- Composition and equality transport preserve the original functional. -/
theorem pullbackToUnit_comp_congr {W C Z : Scheme.{u}}
    (f : W ⟶ C) (g : C ⟶ Z) (t : W ⟶ Z) (h : f ≫ g = t)
    {L : Z.Modules} (a : L ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    Hom.pullbackToUnit (Hom.pullbackToUnit a g) f =
      ((Modules.pullbackComp f g ≪≫ Modules.pullbackCongr h).hom.app L) ≫
        Hom.pullbackToUnit a t := by
  subst t
  exact GlobalBoundaryPencil.pullback_map_comp f g a
end AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (v : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (U : (Spec (.of (Polynomial k))).Opens)

/-- The lambda source change keeps the entire original overlap as target. -/
abbrev retainedToDiagonal :=
  constantSourceMapOfEq α ((r ≫ inclusion k p) ≫ projection k p)
    (retainedProjection k p U) (commonSourceProjection k p r α) rfl

/-- The psi source change uses the same fixed open and the same original overlap. -/
abbrev retainedToFixed :=
  constantSourceMapOfEq β (v ≫ Hom.boundaryLineProjection k)
    (retainedProjection k p U) (commonSourceProjection k p r α)
    (commonSourceProjection_fixed k p r v α β h)

omit [IsSeparated p] [IsOpenImmersion r] in
theorem retainedToDiagonal_isPullback :
    IsPullback (retainedToDiagonal k p r α U) (pullback.fst _ _)
      (pullback.fst _ _) α := constantSourceMapOfEq_isPullback _ _ _ _ _

omit [IsSeparated p] [IsOpenImmersion r] in
theorem retainedToFixed_isPullback :
    IsPullback (retainedToFixed k p r v α β h U) (pullback.fst _ _)
      (pullback.fst _ _) β := constantSourceMapOfEq_isPullback _ _ _ _ _

omit [IsSeparated p] [IsOpenImmersion r] in
@[reassoc (attr := simp)]
theorem retainedToDiagonal_target :
    retainedToDiagonal k p r α U ≫ pullback.snd _ _ = pullback.snd _ _ :=
  constantSourceMapOfEq_snd _ _ _ _ _

omit [IsSeparated p] [IsOpenImmersion r] in
@[reassoc (attr := simp)]
theorem retainedToFixed_target :
    retainedToFixed k p r v α β h U ≫ pullback.snd _ _ = pullback.snd _ _ :=
  constantSourceMapOfEq_snd _ _ _ _ _

omit [IsSeparated p] [IsOpenImmersion r] in
/-- The retained square commutes with the original compact lambda source change. -/
theorem retainedToDiagonal_inclusion :
    retainedToDiagonal k p r α U ≫
      constantRetainedInclusion k p U ((r ≫ inclusion k p) ≫ projection k p) =
    constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
      commonToDiagonal k p r α := by
  apply pullback.hom_ext <;>
    simp [retainedToDiagonal, commonToDiagonal, Category.assoc]

omit [IsSeparated p] [IsOpenImmersion r] in
/-- The retained square commutes with the original compact fixed-U source change. -/
theorem retainedToFixed_inclusion :
    retainedToFixed k p r v α β h U ≫
      constantRetainedInclusion k p U (v ≫ Hom.boundaryLineProjection k) =
    constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
      commonToFixed k p r v α β h := by
  apply pullback.hom_ext <;>
    simp [retainedToFixed, commonToFixed, Category.assoc]

/-- Native pullback composition through the lambda retained curve. -/
def retainedDiagonalPullbackIso :
    Modules.pullback (constantRetainedInclusion k p U
      ((r ≫ inclusion k p) ≫ projection k p)) ⋙
      Modules.pullback (retainedToDiagonal k p r α U) ≅
    Modules.pullback (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
      commonToDiagonal k p r α) :=
  Modules.pullbackComp _ _ ≪≫
    Modules.pullbackCongr (retainedToDiagonal_inclusion k p r α U)

/-- Native pullback composition through the unchanged fixed-U retained curve. -/
def retainedFixedPullbackIso :
    Modules.pullback (constantRetainedInclusion k p U (v ≫ Hom.boundaryLineProjection k)) ⋙
      Modules.pullback (retainedToFixed k p r v α β h U) ≅
    Modules.pullback (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
      commonToFixed k p r v α β h) :=
  Modules.pullbackComp _ _ ≪≫
    Modules.pullbackCongr (retainedToFixed_inclusion k p r v α β h U)

/-- Actual twice-pulled lambda line on the retained common curve. -/
abbrev retainedDiagonalLine (L : LineBundle (diagonalAmbient k p r)) :=
  pullbackLineBundle (retainedToDiagonal k p r α U)
    (pullbackLineBundle (constantRetainedInclusion k p U
      ((r ≫ inclusion k p) ≫ projection k p)) L)

/-- Actual twice-pulled psi line on the retained common curve. -/
abbrev retainedFixedLine (L : LineBundle (fixedAmbient k p v)) :=
  pullbackLineBundle (retainedToFixed k p r v α β h U)
    (pullbackLineBundle (constantRetainedInclusion k p U
      (v ≫ Hom.boundaryLineProjection k)) L)

abbrev retainedDiagonalFunctional {L : (diagonalAmbient k p r).Modules}
    (a : L ⟶ SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf) :=
  Hom.pullbackToUnit (Hom.pullbackToUnit a
    (constantRetainedInclusion k p U ((r ≫ inclusion k p) ≫ projection k p)))
    (retainedToDiagonal k p r α U)

abbrev retainedFixedFunctional {L : (fixedAmbient k p v).Modules}
    (a : L ⟶ SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf) :=
  Hom.pullbackToUnit (Hom.pullbackToUnit a
    (constantRetainedInclusion k p U (v ≫ Hom.boundaryLineProjection k)))
    (retainedToFixed k p r v α β h U)

omit [IsSeparated p] [IsOpenImmersion r] in
theorem retainedDiagonalFunctional_eq {L : (diagonalAmbient k p r).Modules}
    (a : L ⟶ SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf) :
    retainedDiagonalFunctional k p r α U a =
      (retainedDiagonalPullbackIso k p r α U).hom.app L ≫
        Hom.pullbackToUnit a
          (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
            commonToDiagonal k p r α) :=
  pullbackToUnit_comp_congr _ _ _ _ _

omit [IsSeparated p] [IsOpenImmersion r] in
theorem retainedFixedFunctional_eq {L : (fixedAmbient k p v).Modules}
    (a : L ⟶ SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf) :
    retainedFixedFunctional k p r v α β h U a =
      (retainedFixedPullbackIso k p r v α β h U).hom.app L ≫
        Hom.pullbackToUnit a
          (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
            commonToFixed k p r v α β h) :=
  pullbackToUnit_comp_congr _ _ _ _ _

variable (φ : X ⟶ pullback U.ι p)
  (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p)
  [Flat α] (T : LineBundle (diagonalAmbient k p r))
  (N : LineBundle (fixedAmbient k p v))

omit [IsOpenImmersion r] in
/-- Local rank one is inherited from the original lambda ideal, not assumed. -/
theorem commonRetainedGraph_locallyRankOne :
    IsLocallyRankOne _ (Hom.idealModule (commonRetainedGraph k p r α U φ hφ)) :=
  isLocallyRankOne_of_iso _ (commonRetainedGraphIdealIso k p r α U φ hφ)
    (pullbackLineBundle
      (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
        commonToDiagonal k p r α) (actualIdealLineBundle k p r)).property

/-- The original mixed dual comparison, conjugated only by native pullback composition
and the canonical ideal of the actual retained graph. -/
def retainedPencilLineIso :
    tensorSheaf _ (Hom.idealModule (commonRetainedGraph k p r α U φ hφ))
      (tensorSheaf _
        (retainedDiagonalLine k p r α U (dualLineBundle _ T)).val
        (retainedFixedLine k p r v α β h U (dualLineBundle _ N)).val) ≅
    tensorSheaf _
      (retainedDiagonalLine k p r α U
        (dualLineBundle _ (tensorLineBundle _ T (actualDivisorLineBundle k p r)))).val
      (retainedFixedLine k p r v α β h U (dualLineBundle _ N)).val :=
  tensorSheafIso _ (commonRetainedGraphIdealIso k p r α U φ hφ).symm
    (tensorSheafIso _
      ((retainedDiagonalPullbackIso k p r α U).app (dualLineBundle _ T).val)
      ((retainedFixedPullbackIso k p r v α β h U).app (dualLineBundle _ N).val)) ≪≫
  mixedPulledDualTwistedIdealProductIso
    (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
      commonToDiagonal k p r α)
    (constantRetainedInclusion k p U (commonSourceProjection k p r α) ≫
      commonToFixed k p r v α β h) (actualIdealLineBundle k p r) T N ≪≫
  tensorSheafIso _
    ((retainedDiagonalPullbackIso k p r α U).app
      (dualLineBundle _ (tensorLineBundle _ T (actualDivisorLineBundle k p r))).val).symm
    ((retainedFixedPullbackIso k p r v α β h U).app (dualLineBundle _ N).val).symm

omit [IsOpenImmersion r] in
/-- Endpoint zero is the literal retained graph times the original two pole maps. -/
theorem retainedPencilLineIso_start
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val) :
    (retainedPencilLineIso k p r v α β h U φ hφ T N).hom ≫
      Hom.productSection
        (retainedDiagonalFunctional k p r α U
          (sectionDualFunctional _ (tensorLineBundle _ T (actualDivisorLineBundle k p r))
            (twistedIdealSection _ (actualIdealLineBundle k p r) T
              (Hom.idealInclusion
                (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) b)))
        (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N d)) =
    Hom.productSection (Hom.idealInclusion (commonRetainedGraph k p r α U φ hφ))
      (Hom.productSection
        (retainedDiagonalFunctional k p r α U (sectionDualFunctional _ T b))
        (retainedFixedFunctional k p r v α β h U (sectionDualFunctional _ N d))) := by
  simp only [retainedDiagonalFunctional_eq, retainedFixedFunctional_eq]
  simp only [retainedPencilLineIso, Iso.trans_hom, Category.assoc]
  rw [tensorSheafIso_productSection]
  simp only [Iso.symm_hom, Iso.app_inv,
    Iso.inv_hom_id_app_assoc]
  dsimp only [actualDivisorLineBundle]
  rw [mixedPulledDualTwistedIdealProductIso_section]
  rw [tensorSheafIso_productSection, tensorSheafIso_productSection]
  congr 1
  rw [← commonRetainedGraphIdealIso_inclusion k p r α U φ hφ]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

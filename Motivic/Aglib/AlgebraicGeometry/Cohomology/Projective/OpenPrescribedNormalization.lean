module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.OpenTensorSectionTransport
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OpenBoundaryFrame
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.OpenRightNormalization
/-! # Actual prescribed open pairs in normalized local coefficients -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Pullback.OpenRestriction
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Postcomposition preserves the literal tensor of unit-domain sections. -/
@[reassoc] theorem tensorUnitSection_map {W : Scheme.{u}} {M N P Q : W.Modules}
    (s : SheafOfModules.unit W.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit W.ringCatSheaf ⟶ N) (a : M ⟶ P) (b : N ⟶ Q) :
    tensorUnitSection s t ≫ tensorSheafMap W a b = tensorUnitSection (s ≫ a) (t ≫ b) := by
  simp only [tensorUnitSection, Category.assoc, tensorSheafMap_comp]

/-- The transported frame cancels the inverse native coefficient transport literally. -/
theorem openBoundaryFrame_inv_transport {Z C : Scheme.{u}} (z : Z ⟶ C) (U : C.Opens)
    (M : C.Modules) {N : U.toScheme.Modules}
    (q : (Modules.restrictFunctor U.ι).obj M ≅ N)
    (E : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (openBoundaryFrame z U M q E).inv ≫
      (Modules.pullback (z ∣_ U)).map q.inv ≫ (localPullbackIso z U).inv.app M =
    (restrictUnitIso (z ⁻¹ᵁ U).ι).inv ≫
      (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map E.inv := by
  simp only [openBoundaryFrame, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Category.assoc]
  have hq := ((Modules.pullback (z ∣_ U)).mapIso q).hom_inv_id_assoc
    ((localPullbackIso z U).inv.app M)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv] at hq
  rw [hq, Iso.hom_inv_id_app, Category.comp_id]

/-- Normalize an original open prescribed relation without changing its boundary frame. -/
theorem open_prescribed_normalized {Z C : Scheme.{u}} (z : Z ⟶ C) (U : C.Opens)
    (T M : C.Modules) {N : U.toScheme.Modules}
    (q : (Modules.restrictFunctor U.ι).obj M ≅ N)
    (E : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (a : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Modules.restrictFunctor U.ι).obj (tensorSheaf C T M))
    (b : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Modules.restrictFunctor U.ι).obj
        (tensorSheaf C T (SheafOfModules.unit C.ringCatSheaf)))
    (h : pullbackSectionMap (z ∣_ U) a ≫ openBoundaryTensorComparison z U T M =
      pullbackSectionMap (z ∣_ U) b ≫
        openBoundaryTensorComparison z U T (SheafOfModules.unit C.ringCatSheaf) ≫
        (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map
          (tensorSheafMap Z (𝟙 ((Modules.pullback z).obj T))
            ((pullbackUnitIso z).hom ≫ E.inv))) :
    pullbackSectionMap (z ∣_ U) (normalizeOpenTensorSection U T M q a) ≫
      pullbackTensorMap (z ∣_ U) ((Modules.restrictFunctor U.ι).obj T) N =
    tensorUnitSection (pullbackSectionMap (z ∣_ U) (b ≫ openRightNormalization U T))
      (openBoundaryFrame z U M q E).inv := by
  let K := ((localPullbackIso z U).app T).symm
  let J := ((Modules.pullback (z ∣_ U)).mapIso q).symm ≪≫
    ((localPullbackIso z U).app M).symm
  let A := tensorSheafIso (z ⁻¹ᵁ U).toScheme K J ≪≫
    tensorRestrictionIso (z ⁻¹ᵁ U).ι ((Modules.pullback z).obj T) ((Modules.pullback z).obj M)
  apply (cancel_mono A.hom).mp
  have hA : A.hom = tensorSheafMap (z ⁻¹ᵁ U).toScheme
      ((localPullbackIso z U).inv.app T)
      ((Modules.pullback (z ∣_ U)).map q.inv ≫ (localPullbackIso z U).inv.app M) ≫
      (tensorRestrictionIso (z ⁻¹ᵁ U).ι ((Modules.pullback z).obj T)
        ((Modules.pullback z).obj M)).hom := rfl
  rw [hA]
  simp only [Category.assoc]
  rw [tensorUnitSection_map_assoc]
  rw [openBoundaryFrame_inv_transport]
  rw [pullbackSectionMap_openRightNormalization]
  let EO := (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso z) ≪≫
    restrictUnitIso (z ⁻¹ᵁ U).ι
  have hn := tensorUnitSection_normalized
    (pullbackSectionMap (z ∣_ U) b ≫
      openBoundaryTensorComparison z U T (SheafOfModules.unit C.ringCatSheaf) ≫
      (tensorRestrictionIso (z ⁻¹ᵁ U).ι ((Modules.pullback z).obj T)
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))).inv)
    EO ((restrictUnitIso (z ⁻¹ᵁ U).ι).inv ≫
      (Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map E.inv)
  simp only [EO, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] at hn
  erw [hn]
  simp only [Iso.hom_inv_id_assoc]
  erw [normalizeOpenTensorSection_pullback z U T M q a]
  rw [h]
  simp only [Category.assoc]
  have ht := restrictTensorMap_naturality Z (z ⁻¹ᵁ U)
    (𝟙 ((Modules.pullback z).obj T)) ((pullbackUnitIso z).hom ≫ E.inv)
  simp only [CategoryTheory.Functor.map_id, Functor.map_comp, restrictTensorMap] at ht
  erw [ht]
  simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.CoherentGraph

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.CanonicalEvaluation
public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit

/-! # Literal canonical divisor-section coordinates on the prescribed boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The actual unit-to-dual morphism represents the original canonical divisor section. -/
theorem canonicalDualHom_sectionDivisorCanonicalSection {S X : Scheme.{u}}
    (p : X ⟶ S) (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 S)
    (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    unitHomGlobalSectionsEquiv X (sectionDivisorLineBundle p s hs U hU).val
        (canonicalDualHom X (idealModule s) (idealInclusion s)) =
      sectionDivisorCanonicalSection p s hs U hU := by
  exact (unitHomGlobalSectionsEquiv X (sectionDivisorLineBundle p s hs U hU).val).apply_symm_apply _

/-- Pull back the unchanged unit-to-dual canonical section. -/
def pullbackCanonicalDualHom {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SheafOfModules.unit W.ringCatSheaf ⟶
      (Scheme.Modules.pullback f).obj (dualLineBundle X L).val :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (canonicalDualHom X L.val φ)

/-- Normalized pullback evaluation is exactly the original pulled functional. -/
theorem pullbackCanonicalDualHom_pairing {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap W (pullbackCanonicalDualHom f L φ)
        (𝟙 ((Scheme.Modules.pullback f).obj L.val)) ≫
      (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
      (Scheme.Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom =
      (tensorSheafLeftUnit W ((Scheme.Modules.pullback f).obj L.val)).hom ≫
        Modules.Hom.pullbackToUnit φ f := by
  unfold pullbackCanonicalDualHom
  rw [← Category.id_comp (𝟙 ((Scheme.Modules.pullback f).obj L.val)), ← tensorSheafMap_comp]
  simp only [Category.assoc]
  rw [pullback_canonicalDualHom_evaluation]
  rw [tensorSheafMap_comp_assoc]
  simp only [Iso.inv_hom_id, Category.id_comp]
  change tensorSheafMap W (𝟙 _) (𝟙 _) ≫ _ = _
  have hi : tensorSheafMap W (𝟙 (SheafOfModules.unit W.ringCatSheaf))
      (𝟙 ((Scheme.Modules.pullback f).obj L.val)) = 𝟙 _ := by
    change (SheafOfModulesOfCommRing.associatedSheaf W.sheaf).map
      (CategoryTheory.MonoidalCategory.tensorHom (𝟙 _) (𝟙 _)) = _
    simp
    rfl
  rw [hi, Category.id_comp]
  rfl

/-- The right unit comparison specialized to the native scheme module category. -/
def boundaryRightUnitIso (W : Scheme.{u}) (N : W.Modules) :
    tensorSheaf W N (SheafOfModules.unit W.ringCatSheaf) ≅ N :=
  (SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).app N

/-- Contraction with a specified generator retains its exact functional coordinate. -/
theorem canonicalPairing_coordinate {W : Scheme.{u}} {N P : W.Modules}
    (a : SheafOfModules.unit W.ringCatSheaf ⟶ N)
    (t : tensorSheaf W N P ⟶ SheafOfModules.unit W.ringCatSheaf)
    (v : P ⟶ SheafOfModules.unit W.ringCatSheaf)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ P)
    (h : tensorSheafMap W a (𝟙 P) ≫ t = (tensorSheafLeftUnit W P).hom ≫ v) :
    a ≫ (boundaryRightUnitIso W N).inv ≫
      tensorSheafMap W (𝟙 N) e.hom ≫ t = e.hom ≫ v := by
  let O : W.Modules := SheafOfModules.unit W.ringCatSheaf
  have hr := (SheafOfModulesOfCommRing.tensorRightUnitIso W.sheaf).inv.naturality a
  change a ≫ (boundaryRightUnitIso W N).inv =
    (boundaryRightUnitIso W O).inv ≫
      tensorSheafMap W a (𝟙 O) at hr
  have hx : tensorSheafMap W a (𝟙 O) ≫ tensorSheafMap W (𝟙 N) e.hom =
      tensorSheafMap W (𝟙 O) e.hom ≫ tensorSheafMap W a (𝟙 P) := by
    rw [tensorSheafMap_comp, tensorSheafMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  have hl := (SheafOfModulesOfCommRing.tensorLeftUnitIso W.sheaf).hom.naturality e.hom
  change tensorSheafMap W (𝟙 O) e.hom ≫ (tensorSheafLeftUnit W P).hom =
    (tensorSheafLeftUnit W O).hom ≫ e.hom at hl
  rw [← Category.assoc, hr]
  simp only [Category.assoc]
  rw [← Category.assoc (tensorSheafMap W a (𝟙 O)), hx]
  simp only [Category.assoc]
  rw [h, ← Category.assoc (tensorSheafMap W (𝟙 O) e.hom), hl]
  simp only [Category.assoc]
  change (boundaryRightUnitIso W O).inv ≫
    (SheafOfModulesOfCommRing.tensorLeftUnitIso W.sheaf).hom.app O ≫ _ = _
  rw [tensorUnitors_eq]
  exact (boundaryRightUnitIso W O).inv_hom_id_assoc _

/-- Under the prescribed dual trivialization, the canonical section is the literal
ideal functional evaluated on the prescribed coordinate. -/
theorem dualBoundaryTrivialization_canonical {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : SheafOfModules.unit W.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj L.val) :
    pullbackCanonicalDualHom f L φ ≫ (dualBoundaryTrivialization f L e).hom =
      e.hom ≫ Modules.Hom.pullbackToUnit φ f := by
  exact canonicalPairing_coordinate (pullbackCanonicalDualHom f L φ)
    ((PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
      (Scheme.Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom)
    (Modules.Hom.pullbackToUnit φ f) e (pullbackCanonicalDualHom_pairing f L φ)

/-- The canonical graph section has literal value one in the canonical infinity coordinate. -/
theorem infinityBoundaryDivisorIso_canonical {S C Y D : Scheme.{u}}
    (q : C ⟶ S) [IsSeparated q] (j : Y ⟶ C) [IsOpenImmersion j]
    (d : D ⟶ C) (h : Disjoint (Set.range j) (Set.range d))
    (hI : IsLocallyRankOne (pullback (j ≫ q) q) (idealModule (compactificationGraph q j))) :
    pullbackCanonicalDualHom (infinityProductMap q j d)
        ⟨idealModule (compactificationGraph q j), hI⟩
        (idealInclusion (compactificationGraph q j)) ≫
      (infinityBoundaryDivisorIso q j d h hI).hom = 𝟙 _ := by
  rw [infinityBoundaryDivisorIso, dualBoundaryTrivialization_canonical]
  have := infinity_pullbackIdealInclusion_isIso q j d h
  exact (asIso (Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph q j))
    (infinityProductMap q j d))).inv_hom_id

end AlgebraicGeometry.Scheme.Hom

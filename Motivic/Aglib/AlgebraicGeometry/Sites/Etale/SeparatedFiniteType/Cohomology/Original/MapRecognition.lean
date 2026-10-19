/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.EdgeMap
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologyComparison
public import Motivic.Aglib.CategoryTheory.Sites.RestrictionSourceNaturality
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.AdjunctionEdgeMapNaturality

/-! # Recognition of the original ordinary-cohomology restriction map

The coefficient morphism is the literal restriction to a base-changed neighborhood.
Its inverse-image mate need not be an isomorphism. No homotopy-invariance hypothesis
is used anywhere in the map identity.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)

/-- Naturality in the original big coefficient sheaf of literal geometric restriction. -/
def restrictionToDirectImageNat : restrict X AddCommGrpCat.{u + 1} ⟶
    restrict Y AddCommGrpCat.{u + 1} ⋙ directImage h.left where
  app F := restrictionToDirectImage F h
  naturality F G f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact (f.hom.naturality ((restrictionProjection h).app V.unop).op).symm

/-- The genuine inverse-image mate of restriction, with no invertibility assertion. -/
def restrictionInverseImageMap : restrict X AddCommGrpCat.{u + 1} ⋙ inverseImage h.left ⟶
    restrict Y AddCommGrpCat.{u + 1} where
  app F := ((imageAdjunction h.left).homEquiv _ _).symm (restrictionToDirectImage F h)
  naturality F G f := by
    apply ((imageAdjunction h.left).homEquiv _ _).injective
    simp only [Functor.comp_map]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    exact (restrictionToDirectImageNat h).naturality f

/-- Actual free-source naturality for the geometric projection of a neighborhood. -/
theorem restrictionInverseImageMap_source (V : EtaleSeparatedFiniteType X.left) :
    (inverseImage h.left).map
        (Hypercohomology.restrictionSourceHom.{u + 1, u, u + 1, u + 1} _ _ (toSmoothSite X) V) ≫
      (restrictionInverseImageMap h).app
        (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} _ ((toSmoothSite X).obj V)) =
    (inverseImageSourceIso h.left V).hom ≫
      Hypercohomology.restrictionSourceHom.{u + 1, u, u + 1, u + 1}
        _ _ (toSmoothSite Y) ((baseChange h.left).obj V) ≫
      (restrict Y AddCommGrpCat).map
        ((Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1} _).map
          ((restrictionProjection h).app V)) := by
  apply ((imageAdjunction h.left).homEquiv _ _).injective
  apply (Hypercohomology.sectionsEquiv.{u + 1, u, u + 1} _ V _).injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [restrictionInverseImageMap, restrict, Equiv.apply_symm_apply]
  rw [Hypercohomology.sectionsEquiv_naturality]
  rw [Hypercohomology.restrictionSourceHom_sections]
  change _ = Hypercohomology.sectionsEquiv.{u + 1, u, u + 1} _ V _
    (((baseChange h.left).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} _ _).homEquiv _ _
      ((Hypercohomology.restrictionSourceIso.{u + 1, u, u + 1, u + 1}
          _ _ (baseChange h.left) V).hom ≫
        Hypercohomology.restrictionSourceHom.{u + 1, u, u + 1, u + 1}
        _ _ (toSmoothSite Y) ((baseChange h.left).obj V) ≫
        (restrict Y AddCommGrpCat.{u + 1}).map
          ((Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1} _).map
          ((restrictionProjection h).app V))))
  rw [Hypercohomology.restrictionSourceIso_sections,
    Hypercohomology.sectionsEquiv_naturality,
    Hypercohomology.restrictionSourceHom_sections]
  change _ = ((Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1} _).map
      ((restrictionProjection h).app V)).hom.app _
    (Hypercohomology.sectionsEquiv.{u + 1, u, u + 1} _ _ _ (𝟙 _))
  rw [← Hypercohomology.sectionsEquiv_naturality, Category.id_comp]
  rw [← Category.comp_id ((Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1} _).map
    ((restrictionProjection h).app V)), Hypercohomology.sectionsEquiv_restriction]
  rfl

variable [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]

/-- The comparison uses the original exact restriction and its canonical source map. -/
theorem cohomologyRestrictionEquiv_apply_source
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (V : EtaleSeparatedFiniteType X.left)
    (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n ((toSmoothSite X).obj V)) :
    cohomologyRestrictionEquiv X F n V x =
      (Ext.mk₀ (Hypercohomology.restrictionSourceHom.{u + 1, u, u + 1, u + 1}
        _ _ (toSmoothSite X) V)).comp
        (x.mapExactFunctor (restrict X AddCommGrpCat)) (zero_add n) := by
  change (extendRestrictAdjunction X).extEquiv
    ((Ext.mk₀ (extendSourceIso X V).hom).comp x (zero_add n)) = _
  rw [Adjunction.extEquiv_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀]
  rfl

/-- The edge-source formula before rewriting the ordinary-cohomology comparison. -/
theorem ordinaryEdgeMap_coefficient_source
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (V : EtaleSeparatedFiniteType X.left)
    (x : Ext (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) ((toSmoothSite X).obj V)) F n) :
    ordinaryEdgeMap h.left V ((restrict Y AddCommGrpCat).obj F) n
      (((Ext.mk₀ (Hypercohomology.restrictionSourceHom.{u + 1, u, u + 1, u + 1}
        _ _ (toSmoothSite X) V)).comp (x.mapExactFunctor (restrict X AddCommGrpCat))
          (zero_add n)).comp (Ext.mk₀ (restrictionToDirectImage F h)) (add_zero n)) =
      (Ext.mk₀
        (Hypercohomology.restrictionSourceHom.{u + 1, u, u + 1, u + 1}
          _ _ (toSmoothSite Y) ((baseChange h.left).obj V) ≫
          (restrict Y AddCommGrpCat).map
            ((Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1} _).map
              ((restrictionProjection h).app V)))).comp
        (x.mapExactFunctor (restrict Y AddCommGrpCat)) (zero_add n) := by
  apply (imageAdjunction h.left).extEdge_mapExactFunctor_source
    (restrictionToDirectImageNat h) (restrictionInverseImageMap h) (fun _ => rfl)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun f => (inverseImageSourceIso h.left V).inv ≫ f)
      (restrictionInverseImageMap_source h V)

/-- The edge after literal coefficient restriction is the original neighborhood map. -/
theorem ordinaryEdgeMap_restrictionToDirectImage
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (V : EtaleSeparatedFiniteType X.left)
    (x : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n ((toSmoothSite X).obj V)) :
    ordinaryEdgeMap h.left V ((restrict Y AddCommGrpCat).obj F) n
      (((LargeCohomology.presheafFunctor (nisnevichTopology X.left) n).map
        (restrictionToDirectImage F h)).app (op V)
          (cohomologyRestrictionEquiv X F n V x)) =
    cohomologyRestrictionEquiv Y F n ((baseChange h.left).obj V)
      ((LargeCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map
        ((restrictionProjection h).app V).op x) := by
  rw [cohomologyRestrictionEquiv_apply_source]
  change ordinaryEdgeMap h.left V ((restrict Y AddCommGrpCat).obj F) n
    (((Ext.mk₀ (Hypercohomology.restrictionSourceHom.{u + 1, u, u + 1, u + 1}
      _ _ (toSmoothSite X) V)).comp (x.mapExactFunctor (restrict X AddCommGrpCat))
        (zero_add n)).comp (Ext.mk₀ (restrictionToDirectImage F h)) (add_zero n)) = _
  rw [ordinaryEdgeMap_coefficient_source]
  rw [cohomologyRestrictionEquiv_apply_source, LargeCohomology.restriction_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

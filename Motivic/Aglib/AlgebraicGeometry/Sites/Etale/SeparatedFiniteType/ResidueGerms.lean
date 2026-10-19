/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Neighborhood
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteBranchLift

/-! # Original small-Nis residue-point germs and actual zero neighborhoods -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- The literal identity étale object over an arbitrary scheme. -/
def baseObject (U : Scheme.{u}) : EtaleSeparatedFiniteType U :=
  MorphismProperty.Over.mk ⊤ (𝟙 U) (etaleSeparatedFiniteType.id_mem U)

/-- The original structural map to the identity object. -/
def toBaseObject {U : Scheme.{u}} (V : EtaleSeparatedFiniteType U) : V ⟶ baseObject U :=
  MorphismProperty.Over.homMk V.hom (by simp [baseObject])

/-- The existing comapped field point, using the actual residue-field morphism. -/
def residuePoint (U : Scheme.{u}) (z : U) : (nisnevichTopology U).Point.{u + 1} :=
  relativeFieldPoint (U.fromSpecResidueField z) (U.residueField z) (𝟙 _)

/-- The canonical marking of the identity neighborhood by the residue field. -/
def residuePointElement (U : Scheme.{u}) (z : U) :
    (residuePoint U z).fiber.obj (baseObject U) :=
  (relativeFieldPointFiberEquiv (U.fromSpecResidueField z) (U.residueField z)
    (𝟙 _) (baseObject U)).symm (Over.homMk (U.fromSpecResidueField z) (by simp [baseObject]))

/-- The actual native point-fiber map, not a replacement stalk group. -/
def sectionResidueGerm {U : Scheme.{u}}
    (P : (EtaleSeparatedFiniteType U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (z : U) :
    P.obj (op (baseObject U)) ⟶ (residuePoint U z).presheafFiber.obj P :=
  (residuePoint U z).toPresheafFiber (baseObject U) (residuePointElement U z) P

/-- A zero native residue-point germ has an actual residue-splitting étale zero
neighborhood. No sheaf condition, inverse-image comparison, or big-site extension is used. -/
theorem exists_residue_splitting_zero_neighborhood {U : Scheme.{u}}
    (P : (EtaleSeparatedFiniteType U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (z : U)
    (s : P.obj (op (baseObject U))) (hs : sectionResidueGerm P z s = 0) :
    ∃ (V : EtaleSeparatedFiniteType U) (y : V.left), V.hom y = z ∧
      IsIso (V.hom.residueFieldMap y) ∧ P.map (toBaseObject V).op s = 0 := by
  let Φ := residuePoint U z
  have hs' : Φ.toPresheafFiber (baseObject U) (residuePointElement U z) P s =
      Φ.toPresheafFiber (baseObject U) (residuePointElement U z) P 0 := by
    rw [map_zero]
    exact hs
  obtain ⟨V, f, v, _, hv⟩ := (Φ.toPresheafFiber_eq_iff' _ _ s 0).mp hs'
  have hfv : f = toBaseObject V := by
    apply MorphismProperty.Over.Hom.ext
    change f.left = V.hom
    have hf := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 U = V.hom at hf
    exact (Category.comp_id (show V.left ⟶ U from f.left)).symm.trans hf
  have hvzero : P.map (toBaseObject V).op s = 0 := by
    rw [hfv, map_zero] at hv
    exact hv
  let a := relativeFieldPointFiberEquiv (U.fromSpecResidueField z) (U.residueField z)
    (𝟙 _) V v
  have ha : a.left ≫ V.hom = U.fromSpecResidueField z := by
    exact (Over.w a).trans (Category.id_comp _)
  let c := IsLocalRing.closedPoint (U.residueField z)
  have hres : IsIso ((a.left ≫ V.hom).residueFieldMap c) := by
    rw [ha]
    let : SurjectiveOnStalks (U.fromSpecResidueField z) :=
      inferInstanceAs (SurjectiveOnStalks (U.fromSpecResidueField z))
    exact Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks _ _
  have hi : IsIso (V.hom.residueFieldMap (a.left c)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨(V.hom.residueFieldMap _).hom.injective, ?_⟩
    have ht := (ConcreteCategory.bijective_of_isIso
      ((a.left ≫ V.hom).residueFieldMap c)).surjective
    rw [Scheme.residueFieldMap_comp] at ht
    change Function.Surjective ((a.left.residueFieldMap c) ∘
      (V.hom.residueFieldMap (a.left c))) at ht
    exact ht.of_comp_left (a.left.residueFieldMap c).hom.injective
  refine ⟨V, a.left c, ?_, hi, hvzero⟩
  have h := congrArg (fun b => b c) ha
  exact h.trans (U.fromSpecResidueField_apply z c)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

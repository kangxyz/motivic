/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ProjectionPointFiberHI

/-! # Whole-cylinder effacement by an original marked base refinement

The witness is an arrow of the unchanged native point category. In the
degree-induction application, this result is used only in a previously proved
positive degree for the contraction coefficient. It does not supply homotopy
invariance in the degree currently being proved.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

/-- An actual small-site zero restriction on the literal projection base
change kills the original big-site cylinder germ. The existing natural
comparison transports through `a1BaseChangeIso`; the two test objects are not
treated as definitionally equal. -/
theorem pointedCylinder_germ_eq_zero_of_ordinary_base_refinement
    (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
    (Φ : (nisnevichTopology X.left).Point.{u + 1})
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.a1Cylinder R X).left) AddCommGrpCat.{u + 1})]
    (n : ℕ) {V W : Φ.fiber.Elements} (a : W ⟶ V)
    (s : (pointedCylinderValues R Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n)
      (pointedBase R Φ)).obj (op V))
    (hz : (ordinaryPointCohomologyDiagram (SmoothSite.a1Projection R X).left Φ
      (F := (restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat).obj F) n).map a.op
        ((pointedCylinderOrdinaryIso R X Φ F n).hom.app (op V) s) = 0) :
    colimit.ι (pointedCylinderValues R Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n)
      (pointedBase R Φ)) (op V) s = 0 := by
  let D := pointedCylinderValues R Φ
    (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec R)) F n) (pointedBase R Φ)
  let e := pointedCylinderOrdinaryIso R X Φ F n
  have hzero : D.map a.op s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (op W))).1
    rw [map_zero, NatTrans.naturality_apply]
    exact hz
  have h := ConcreteCategory.congr_hom (colimit.w D a.op) s
  simpa only [ConcreteCategory.comp_apply, hzero, map_zero] using h.symm

/-- A zero original cylinder germ is witnessed by a genuine refinement of the
marked BASE, not by an arbitrary etale neighborhood of its cylinder. -/
theorem exists_pointed_cylinder_restriction_zero_of_colimit_isZero
    (R : CommRingCat.{u}) {X : SmoothSite (Spec R)}
    (Φ : (nisnevichTopology X.left).Point.{u + 1})
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hzero : IsZero (colimit
      (pointedCylinderValues R Φ P (pointedBase R Φ))))
    (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues R Φ P (pointedBase R Φ)).obj (op V)) :
    ∃ (W : Φ.fiber.Elements) (a : W ⟶ V),
      P.map (SmoothSite.a1Map R ((pointedBase R Φ).map a)).op s = 0 := by
  let D := pointedCylinderValues R Φ P (pointedBase R Φ)
  have hsub : Subsingleton ↑(colimit D) := AddCommGrpCat.subsingleton_of_isZero hzero
  have he : colimit.ι D (op V) s = colimit.ι D (op V) 0 :=
    @Subsingleton.elim ↑(colimit D) hsub _ _
  obtain ⟨W, a, ha⟩ := ((colimit.isColimit D).eq_iff' s 0).mp he
  refine ⟨W.unop, a.unop, ?_⟩
  change D.map a s = 0
  simpa only [map_zero] using ha

/-- Previously proved positive-degree homotopy invariance gives an actual
whole-cylinder zero restriction along the same full-marked base index. The
ordinary cohomology presheaf and its original restriction maps are retained. -/
theorem exists_pointed_cylinder_restriction_zero_of_cohomology_HI
    (k : Type u) [Field k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (X : SmoothSite (Spec (.of k)))
    (Φ : (nisnevichTopology X.left).Point.{u + 1})
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (h : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left) AddCommGrpCat.{u + 1})]
    (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues (.of k) Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) Φ)).obj (op V)) :
    ∃ (W : Φ.fiber.Elements) (a : W ⟶ V),
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1)).map
        (SmoothSite.a1Map (.of k) ((pointedBase (.of k) Φ).map a)).op s = 0 := by
  apply exists_pointed_cylinder_restriction_zero_of_colimit_isZero
  exact (projectionPointFiber_isZero_of_cohomology_HI k X Φ F n h).of_iso
    (pointedCylinderColimitFiberIso (.of k) X Φ
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1))

end Motivic.FiniteEtaleSite

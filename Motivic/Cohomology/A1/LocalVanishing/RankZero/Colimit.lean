/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.RankZeroPointRefinement
public import Motivic.Cohomology.A1.LocalVanishing.Cylinder.OrdinaryComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Rank-zero cylinder germs on the original field-point index

This bounded consumer retains an explicit whole-cylinder generic-open vanishing
input. It does not prove that input or replace the original neighborhood index.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = 0)
  (hgen : ∀ (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left] [IsIntegral Y.left]
    (s : P.obj (op (SmoothSite.a1Cylinder (.of k) Y))),
    ∃ O : Y.left.Opens, genericPoint Y.left ∈ O ∧
      P.map (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion Y O)).op s = 0)

include hd hgen in
/-- Every original representative dies after two actual open refinements:
first an integral affine neighborhood of its marker, then the supplied generic
base open. Both arrows belong to the unchanged point category of elements. -/
theorem exists_rank_zero_cylinder_restriction_zero
    (V : (relativeFieldPoint b K (𝟙 _)).fiber.Elements)
    (s : (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _)))).obj (op V)) :
    ∃ (W : (relativeFieldPoint b K (𝟙 _)).fiber.Elements) (f : W ⟶ V),
      (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
        (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _)))).map f.op s = 0 := by
  let Φ := relativeFieldPoint b K (𝟙 _)
  let D := pointedCylinderValues (.of k) Φ P (pointedBase (.of k) Φ)
  let : IsNoetherian V.obj.left := Scheme.isNoetherian_of_finiteType
    (show V.obj.left ⟶ X.left from V.obj.hom)
  obtain ⟨O, hO, hI, a, ha⟩ :=
    exists_integral_affine_point_open_refinement X K b p V.obj V.val
  let W := testOpenObject V.obj O
  let M : Φ.fiber.Elements := Functor.elementsMk _ W a
  let f : M ⟶ V := Functor.Elements.homMk (testOpenInclusion V.obj O) ha
  let Y := (toSmoothSite X).obj W
  let : IsAffine Y.left := hO
  let : IsIntegral Y.left := hI
  let : IsIntegral W.left := hI
  let : IsNoetherian W.left := Scheme.isNoetherian_of_finiteType
    (show W.left ⟶ X.left from W.hom)
  let s' : P.obj (op (SmoothSite.a1Cylinder (.of k) Y)) := D.map f.op s
  obtain ⟨U, hU, hz⟩ := hgen Y s'
  have htU : (relativeFieldPointFiberEquiv b K (𝟙 _) W a).left p ∈ U := by
    rw [fieldPoint_eq_genericPoint_of_rank_zero X K b p hd W a]
    exact hU
  obtain ⟨a', ha'⟩ := exists_point_open_refinement_of_mem K b W a p U htU
  let M' : Φ.fiber.Elements := Functor.elementsMk _ (testOpenObject W U) a'
  let g : M' ⟶ M := Functor.Elements.homMk (testOpenInclusion W U) ha'
  let c : (toSmoothSite X).obj (testOpenObject W U) ⟶ (SmoothSite.opensFunctor Y).obj U :=
    SmoothSite.homMk (𝟙 U.toScheme) (by
      change (𝟙 U.toScheme) ≫ (U.ι ≫ (W.hom ≫ X.hom)) =
        (U.ι ≫ W.hom) ≫ X.hom
      simp only [Category.id_comp, Category.assoc])
  have hc : c ≫ SmoothSite.openInclusion Y U =
      (toSmoothSite X).map (testOpenInclusion W U) := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp U.ι
  have hg : D.map g.op s' = 0 := by
    change P.map (SmoothSite.a1Map (.of k)
      ((toSmoothSite X).map (testOpenInclusion W U))).op s' = 0
    rw [← hc, SmoothSite.a1Map_comp, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, hz, map_zero]
  refine ⟨M', g ≫ f, ?_⟩
  change D.map (g ≫ f).op s = 0
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hg

include hd hgen in
/-- Classwise generic-open vanishing kills the whole original cylinder colimit
at any field-valued rank-zero center, not just a distinguished basepoint. -/
theorem pointedCylinderColimit_isZero_of_rank_zero_generic_open_zero :
    IsZero (colimit (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))))) := by
  let D := pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
    (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _)))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro V
  rw [Category.comp_id, Limits.comp_zero]
  ext s
  obtain ⟨W, f, hf⟩ := exists_rank_zero_cylinder_restriction_zero
    X K b p P hd hgen V.unop s
  have h := ConcreteCategory.congr_hom (colimit.w D f.op) s
  change (colimit.ι D (op W)) (D.map f.op s) = (colimit.ι D V) s at h
  rw [hf, map_zero] at h
  exact h.symm

variable
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left)
      AddCommGrpCat.{u + 1})]

include hd in
/-- The same original-index vanishing kills the actual higher-image point fiber
through the proved cylinder comparison. Generic vanishing remains an explicit input. -/
theorem projectionPointFiber_isZero_of_rank_zero_generic_open_zero (n : ℕ)
    (hzero : ∀ (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left] [IsIntegral Y.left]
      (s : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) F n
          (SmoothSite.a1Cylinder (.of k) Y)),
      ∃ O : Y.left.Opens, genericPoint Y.left ∈ O ∧
        (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) F n).map
            (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion Y O)).op s = 0) :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj
      (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived n).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat).obj F))) :=
  (pointedCylinderColimit_isZero_of_rank_zero_generic_open_zero X K b p
    (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) F n) hd hzero).of_iso
        (pointedCylinderColimitFiberIso (.of k) X (relativeFieldPoint b K (𝟙 _)) F n).symm

end Motivic.FiniteEtaleSite

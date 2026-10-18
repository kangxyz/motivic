/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteCartierCylinderComparison
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSmoothNeighborhood
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedRefinement
public import Motivic.Cohomology.A1.PointedOpenCylinderComparison
public import Motivic.Aglib.AlgebraicGeometry.NisnevichDistinguishedSquare

/-! # Cartier charts as refinements of the original marked base

The Cartier coordinate and the cohomological homotopy parameter are separate.
Charts and closed-neighborhood extensions are chosen on the original base
index. Only afterwards is the entire homotopy cylinder taken. The resulting
maps are arrows in the unchanged native point category, and their action on
original cylinder representatives is the original presheaf restriction.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.FiniteEtaleSite

section MarkedRefinement
variable {R : CommRingCat.{u}} (X : SmoothSite (Spec R))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left)
  (N : (relativeFieldPoint b K (𝟙 _)).fiber.Elements)
  (V : FiniteEtaleSite N.obj.left) (c : Spec (.of K) ⟶ V.left)
  (hc : c ≫ V.hom = (relativeFieldPointFiberEquiv b K (𝟙 _) N.obj N.val).left)

/-- A genuine marked refinement of a test object's base is an object of the
original native point index, without changing the marking field. -/
def fieldPointBaseRefinement : (relativeFieldPoint b K (𝟙 _)).fiber.Elements :=
  Functor.elementsMk _ (composeObject N.obj V)
    ((relativeFieldPointFiberEquiv b K (𝟙 _) (composeObject N.obj V)).symm
      (Over.homMk c (by
        change c ≫ (V.hom ≫ N.obj.hom) = 𝟙 _ ≫ b
        rw [← Category.assoc, hc]
        exact Over.w (relativeFieldPointFiberEquiv b K (𝟙 _) N.obj N.val))))

/-- The refined native point has exactly the supplied full field-valued mark. -/
theorem fieldPointBaseRefinement_mark :
    (relativeFieldPointFiberEquiv b K (𝟙 _)
      (fieldPointBaseRefinement X K b N V c hc).obj
      (fieldPointBaseRefinement X K b N V c hc).val).left = c := by
  change ((relativeFieldPointFiberEquiv b K (𝟙 _) (composeObject N.obj V))
    ((relativeFieldPointFiberEquiv b K (𝟙 _) (composeObject N.obj V)).symm _)).left = c
  rw [Equiv.apply_symm_apply]

/-- The allowed refinement arrow in the unchanged original point category. -/
def fieldPointBaseRefinementMap : fieldPointBaseRefinement X K b N V c hc ⟶ N :=
  Functor.Elements.homMk (composeObjectProjection N.obj V) (by
    apply (relativeFieldPointFiberEquiv b K (𝟙 _) N.obj).injective
    rw [relativeFieldPointFiberEquiv_naturality]
    apply Over.OverMorphism.ext
    change (relativeFieldPointFiberEquiv b K (𝟙 _)
      (fieldPointBaseRefinement X K b N V c hc).obj
      (fieldPointBaseRefinement X K b N V c hc).val).left ≫ V.hom = _
    rw [fieldPointBaseRefinement_mark]
    exact hc)

/-- The original cylinder class is restricted along the actual base refinement
times the whole affine line, and represents the same original pointed germ. -/
@[reassoc]
theorem fieldPointBaseRefinement_cylinder_ι
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    P.map (SmoothSite.a1Map R ((pointedBase R (relativeFieldPoint b K (𝟙 _))).map
        (fieldPointBaseRefinementMap X K b N V c hc))).op ≫
      colimit.ι (pointedCylinderValues R (relativeFieldPoint b K (𝟙 _)) P
        (pointedBase R (relativeFieldPoint b K (𝟙 _))))
          (op (fieldPointBaseRefinement X K b N V c hc)) =
      colimit.ι (pointedCylinderValues R (relativeFieldPoint b K (𝟙 _)) P
        (pointedBase R (relativeFieldPoint b K (𝟙 _)))) (op N) :=
  colimit.w _ (fieldPointBaseRefinementMap X K b N V c hc).op

end MarkedRefinement

section CylinderRepresentatives
variable {R : CommRingCat.{u}} {X : SmoothSite (Spec R)}
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {M N : Φ.fiber.Elements} (f : M ⟶ N)
  {E : SmoothSite (Spec R)} (e : E ≅ (pointedBase R Φ).obj M)
  (a : E ⟶ (pointedBase R Φ).obj N)
  (ha : e.hom ≫ (pointedBase R Φ).map f = a)

/-- The actual chart map, followed by its original-object comparison, is the
literal refinement map on the original cylinder colimit. -/
@[reassoc]
theorem cylinder_colimit_ι_of_base_refinement_iso :
    P.map (SmoothSite.a1Map R a).op ≫
        P.map (SmoothSite.a1Map R e.inv).op ≫
      colimit.ι (pointedCylinderValues R Φ P (pointedBase R Φ)) (op M) =
      colimit.ι (pointedCylinderValues R Φ P (pointedBase R Φ)) (op N) := by
  have hmap : e.inv ≫ a = (pointedBase R Φ).map f := by
    rw [← ha, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, ← SmoothSite.a1Map_comp, hmap]
  exact colimit.w _ f.op

/-- Vanishing after an actual marked BASE chart kills the original cylinder
germ. The hypothesis concerns the original restriction along the entire
cylinder of that chart, not a class on an arbitrary cylinder open. -/
theorem cylinder_germ_eq_zero_of_base_refinement_iso
    (s : P.obj (op (SmoothSite.a1Cylinder R ((pointedBase R Φ).obj N))))
    (hs : P.map (SmoothSite.a1Map R a).op s = 0) :
    colimit.ι (pointedCylinderValues R Φ P (pointedBase R Φ)) (op N) s = 0 := by
  have h := ConcreteCategory.congr_hom
    (cylinder_colimit_ι_of_base_refinement_iso Φ P f e a ha) s
  simp only [ConcreteCategory.comp_apply, hs, map_zero] at h
  exact h.symm

end CylinderRepresentatives

section SplitClosedRefinement
variable {R : CommRingCat.{u}} (X : SmoothSite (Spec R))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left)
  (N : (relativeFieldPoint b K (𝟙 _)).fiber.Elements)
  {Z : Scheme.{u}} (i : Z ⟶ N.obj.left) (p : N.obj.left ⟶ Z)
  (hip : i ≫ p = 𝟙 Z) (c : Spec (.of K) ⟶ Z)
  (hc : c ≫ i = (relativeFieldPointFiberEquiv b K (𝟙 _) N.obj N.val).left)
  (W : FieldValuedNeighborhood c K (𝟙 _))

/-- A closed marked neighborhood is extended along the actual retraction and
then inserted in the original base index. Its underlying refinement is the
literal scheme pullback `pullback W.obj.hom p`. -/
def splitClosedPointBaseRefinement : (relativeFieldPoint b K (𝟙 _)).fiber.Elements :=
  fieldPointBaseRefinement X K b N ((baseChange p).obj W.obj)
    (splitClosedFieldRefinement i p hip K c W).val.left
    ((Over.w (splitClosedFieldRefinement i p hip K c W).val).trans
      ((Category.id_comp (c ≫ i)).trans hc))

/-- Closed-side local effacement gives a genuine ambient BASE refinement map,
before taking any homotopy cylinder. -/
def splitClosedPointBaseRefinementMap :
    splitClosedPointBaseRefinement X K b N i p hip c hc W ⟶ N :=
  fieldPointBaseRefinementMap X K b N ((baseChange p).obj W.obj)
    (splitClosedFieldRefinement i p hip K c W).val.left
    ((Over.w (splitClosedFieldRefinement i p hip K c W).val).trans
      ((Category.id_comp (c ≫ i)).trans hc))

/-- The resulting base mark still factors through the actual full closed fiber
of the literal pullback refinement. -/
theorem splitClosedPointBaseRefinement_mark :
    (relativeFieldPointFiberEquiv b K (𝟙 _)
      (splitClosedPointBaseRefinement X K b N i p hip c hc W).obj
      (splitClosedPointBaseRefinement X K b N i p hip c hc W).val).left =
      W.val.left ≫ splitClosedRefinementSection i p hip W.obj := by
  exact (fieldPointBaseRefinement_mark X K b N ((baseChange p).obj W.obj)
    (splitClosedFieldRefinement i p hip K c W).val.left
    ((Over.w (splitClosedFieldRefinement i p hip K c W).val).trans
      ((Category.id_comp (c ≫ i)).trans hc))).trans
      (splitClosedFieldRefinement_mark i p hip K c W)

end SplitClosedRefinement

section CartierChart
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left)
  (N : (relativeFieldPoint b K (𝟙 _)).fiber.Elements)
  {Z : Scheme.{u}} (i : Z ⟶ N.obj.left) [IsClosedImmersion i]
  [Smooth (i ≫ N.obj.hom ≫ X.hom)]

/-- An actual Cartier cylinder chart at a full field-valued mark is an allowed
refinement of the original BASE index. It retains both entire closed-fiber
squares, the full mark and a specified retraction. The normal cylinder is
chosen before any independent homotopy parameter is introduced. -/
theorem exists_pointed_cartier_base_refinement
    (hI : IsLocallyRankOne N.obj.left (Scheme.Hom.idealModule i))
    (s : Spec (.of K))
    (hs : (relativeFieldPointFiberEquiv b K (𝟙 _) N.obj N.val).left s ∈ Set.range i) :
    ∃ O : Z.Opens,
      ∃ (E : SmoothSite (Spec (.of k)))
        (a : E ⟶ (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))).obj N)
        (q : E ⟶ SmoothSite.a1Cylinder (.of k)
          (SmoothSite.closedOpenSite (Y := (toSmoothSite X).obj N.obj) i O))
        (d : SmoothSite.closedOpenSite (Y := (toSmoothSite X).obj N.obj) i O ⟶ E)
        (c : Spec (.of K) ⟶ O.toScheme)
        (M : (relativeFieldPoint b K (𝟙 _)).fiber.Elements) (f : M ⟶ N)
        (e : E ≅ (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))).obj M),
        Etale a.left ∧ Etale q.left ∧ IsClosedImmersion d.left ∧
        IsPullback d.left O.ι a.left i ∧
        IsPullback d.left (𝟙 O.toScheme) q.left
          (SmoothSite.a1Section (.of k)
            (SmoothSite.closedOpenSite (Y := (toSmoothSite X).obj N.obj) i O) 0).left ∧
        d.left ≫ q.left ≫ (SmoothSite.a1Projection (.of k)
          (SmoothSite.closedOpenSite (Y := (toSmoothSite X).obj N.obj) i O)).left =
            𝟙 O.toScheme ∧
        c ≫ O.ι ≫ i = (relativeFieldPointFiberEquiv b K (𝟙 _) N.obj N.val).left ∧
        e.hom ≫ (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))).map f = a ∧
        (relativeFieldPointFiberEquiv b K (𝟙 _) M.obj M.val).left =
          c ≫ d.left ≫ e.hom.left := by
  let Y := (toSmoothSite X).obj N.obj
  let n := (relativeFieldPointFiberEquiv b K (𝟙 _) N.obj N.val).left
  have hp : (IsLocalRing.closedPoint K : PrimeSpectrum K) = s := Subsingleton.elim _ _
  obtain ⟨cZ, hcZ⟩ := Scheme.exists_field_lift_of_mem_range i n
    (by simpa only [hp] using hs)
  obtain ⟨O, hO, E, a, q, d, ha, hq, hpa, hpq⟩ :=
    SmoothSite.exists_cartier_cylinder_comparison Y i hI (cZ s)
  let c := openFieldPointLift K cZ s O hO
  have hcO : c ≫ O.ι = cZ := openFieldPointLift_ι K cZ s O hO
  let : Etale a.left := ha
  let V := ofSmoothMap Y E a
  have hm : (c ≫ d.left) ≫ V.hom = n := by
    change (c ≫ d.left) ≫ a.left = n
    rw [Category.assoc, hpa.w, ← Category.assoc, hcO]
    exact hcZ
  let M := fieldPointBaseRefinement X K b N V (c ≫ d.left) hm
  let f := fieldPointBaseRefinementMap X K b N V (c ≫ d.left) hm
  let e : E ≅ (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))).obj M :=
    ofSmoothMapIso Y E a ≪≫ ((composeObjectToSmoothIso X N.obj).app V).symm
  have hd : IsClosedImmersion d.left :=
    MorphismProperty.of_isPullback hpa.flip inferInstance
  refine ⟨O, E, a, q, d, c, M, f, e, ha, hq, hd, hpa, hpq, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hpq.w, Category.id_comp]
    exact congrArg (fun t => t.left)
      (SmoothSite.a1Section_projection (.of k)
        (SmoothSite.closedOpenSite (Y := Y) i O) 0)
  · rw [← Category.assoc, hcO]
    exact hcZ
  · apply MorphismProperty.Over.Hom.ext
    change (𝟙 E.left ≫ 𝟙 E.left) ≫ a.left = a.left
    simp only [Category.id_comp]
  · change (relativeFieldPointFiberEquiv b K (𝟙 _) M.obj M.val).left =
      c ≫ d.left ≫ (𝟙 E.left ≫ 𝟙 E.left)
    rw [Category.id_comp, Category.comp_id]
    exact fieldPointBaseRefinement_mark X K b N V (c ≫ d.left) hm

end CartierChart
end Motivic.FiniteEtaleSite

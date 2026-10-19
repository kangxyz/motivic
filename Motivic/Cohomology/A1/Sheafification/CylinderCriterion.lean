/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.DenseDetection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products.ParameterProducts
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso


/-!
# A whole-cylinder criterion for homotopy invariance of sheafification

The hypothesis below is a genuine geometric input: every section of the actual
Nisnevich sheafification on an integral affine cylinder lifts to the actual unit
image after shrinking in the base, while retaining the whole affine line.
Dense detection and the zero section then imply homotopy invariance. This file
does not construct that lifting input or assert unconditional sheafification HI.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Whole-cylinder lifting in the original smooth models. The open immersion is
in the base, not merely an arbitrary dense open of the cylinder. No generic-field
coefficient functor or homotopy invariance of the target is assumed. -/
def ModelWholeCylinderLifting (P : PresheafWithTransfers.{u + 1} k) : Prop :=
  ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (g : ((nisnevichSheafify k).obj P).obj.sections
      (Cor.mk (SmoothSite.a1Cylinder (.of k) X))),
    ∃ (U : SmoothSite (Spec (.of k))) (j : U ⟶ X),
      IsOpenImmersion j.left ∧ Nonempty U.left ∧
      ∃ t : (nisnevichImage P).sections (Cor.mk (SmoothSite.a1Cylinder (.of k) U)),
        (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.a1Cylinder (.of k) U))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) j)) g

private theorem cylinder_isPullback {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) :
    IsPullback (SmoothSite.a1Map (.of k) j).left
      (SmoothSite.a1Projection (.of k) U).left
      (SmoothSite.a1Projection (.of k) X).left j.left := by
  apply IsPullback.of_right
    (h₁₂ := (SmoothSite.productSnd X (SmoothSite.affineLine (.of k))).left)
    (h₂₂ := X.hom) (v₁₃ := (SmoothSite.affineLine (.of k)).hom)
  · have h := congrArg (fun f => f.left)
      (SmoothSite.productMap_snd j (𝟙 (SmoothSite.affineLine (.of k))))
    change (SmoothSite.a1Map (.of k) j).left ≫
      pullback.snd X.hom (SmoothSite.affineLine (.of k)).hom =
        pullback.snd U.hom (SmoothSite.affineLine (.of k)).hom ≫ 𝟙 _ at h
    change IsPullback
      ((SmoothSite.a1Map (.of k) j).left ≫
        pullback.snd X.hom (SmoothSite.affineLine (.of k)).hom)
      (pullback.fst U.hom (SmoothSite.affineLine (.of k)).hom)
      (SmoothSite.affineLine (.of k)).hom (j.left ≫ X.hom)
    rw [h, Category.comp_id, MorphismProperty.Over.w j]
    exact (IsPullback.of_hasPullback _ _).flip
  · exact congrArg (fun f => f.left) (SmoothSite.a1Map_projection (.of k) j)
  · exact (IsPullback.of_hasPullback _ _).flip

private theorem cylinder_denseRange {U X : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) (hj : DenseRange j.left) :
    DenseRange (SmoothSite.a1Map (.of k) j).left := by
  let H := cylinder_isPullback j
  have hr : Set.range (SmoothSite.a1Map (.of k) j).left =
      (SmoothSite.a1Projection (.of k) X).left ⁻¹' Set.range j.left := by
    rw [← H.isoPullback_hom_fst]
    change Set.range ((pullback.fst
      (SmoothSite.a1Projection (.of k) X).left j.left) ∘ H.isoPullback.hom) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr H.isoPullback.hom.surjective,
      Set.image_univ, Scheme.Pullback.range_fst]
  change Dense (Set.range (SmoothSite.a1Map (.of k) j).left)
  rw [hr]
  let : Smooth (SmoothSite.a1Projection (.of k) X).left :=
    inferInstanceAs (Smooth (pullback.fst X.hom
      (Scheme.PolynomialLaurent.polynomialProjection (.of k))))
  exact hj.preimage (SmoothSite.a1Projection (.of k) X).left.isOpenMap

/-- On an integral affine base, whole-cylinder lifting makes the original zero
section injective. The dense-detection theorem applies to the actual target
without assuming that target is HI. -/
theorem nisnevichSheafify_sectionPullback_injective_of_modelWholeCylinderLifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    Function.Injective (A1.sectionPullback (.of k)
      ((toPresheaf k).obj ((nisnevichSheafify k).obj P).obj) X 0) := by
  let F := (toPresheaf k).obj ((nisnevichSheafify k).obj P).obj
  let S := (toPresheaf k).obj (nisnevichImage P)
  let η : S ⟶ F := (toPresheaf k).map (nisnevichImageι P)
  apply (injective_iff_map_eq_zero _).mpr
  intro g hg
  obtain ⟨U, j, hj, hU, t, ht⟩ := hL X g
  let : IsOpenImmersion j.left := hj
  let : Nonempty U.left := hU
  have hjd : DenseRange j.left :=
    j.left.isOpenMap.denseRange_of_isPreirreducibleSpace j.left
  let c := SmoothSite.a1Map (.of k) j
  let : IsOpenImmersion c.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion) (cylinder_isPullback j).flip inferInstance
  have ht' : η.app (op (SmoothSite.a1Cylinder (.of k) U)) t = F.map c.op g := ht
  have hz : S.map (SmoothSite.a1Section (.of k) U 0).op t = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (η.app (op U))).mp inferInstance
    rw [map_zero, η.naturality_apply, ht']
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
      SmoothSite.a1Section_naturality, op_comp, F.map_comp,
      ConcreteCategory.comp_apply]
    change F.map j.op (A1.sectionPullback (.of k) F X 0 g) = 0
    rw [hg, map_zero]
  have htzero : t = 0 := by
    have hS := nisnevichImage_isA1Invariant P hP
    have he : A1.sectionPullback (.of k) S U 0 ≫
        A1.projectionPullback (.of k) S U = 𝟙 _ := by
      rw [← A1.projectionIso_inv (.of k) S hS U 0]
      exact (A1.projectionIso (.of k) S hS U).inv_hom_id
    have he' := congrArg (fun f => f t) he
    change S.map (SmoothSite.a1Projection (.of k) U).op
      (S.map (SmoothSite.a1Section (.of k) U 0).op t) = t at he'
    rw [hz, map_zero] at he'
    exact he'.symm
  apply nisnevichSheafify_section_eq_zero_of_dense_open P hP c
    (cylinder_denseRange j hjd) g
  change F.map c.op g = 0
  rw [← ht', htzero, map_zero]

/-- The geometric whole-cylinder input implies HI of the actual sheafification.
The input remains explicit; no generic-field spreading theorem is assumed. -/
theorem nisnevichSheafify_isA1Invariant_of_modelWholeCylinderLifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P) :
    ((nisnevichSheafify k).obj P).obj.IsA1Invariant := by
  let F := (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)
  let C : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
    ⟨(SmoothSite.parameterProduct (SmoothSite.affineLine (.of k))).op ⋙ F.obj,
      SmoothSite.parameterProduct_op_comp_isSheaf _ F.obj F.property⟩
  let φ : F ⟶ C := ⟨{
    app X := A1.projectionPullback (.of k) F.obj X.unop
    naturality := fun _ _ f => A1.projectionPullback_naturality (.of k) F.obj f.unop }⟩
  have hφ : IsIso φ := by
    apply SmoothSite.isIso_of_integral_affine_app k
    intro X _ _
    let p := A1.projectionPullback (.of k) F.obj X
    let s := A1.sectionPullback (.of k) F.obj X 0
    have hs : Function.Injective s :=
      nisnevichSheafify_sectionPullback_injective_of_modelWholeCylinderLifting P hP hL X
    have hp : p ≫ s = 𝟙 _ := A1.projectionPullback_sectionPullback (.of k) F.obj X 0
    have hsp : s ≫ p = 𝟙 _ := by
      ext g
      apply hs
      have hp' := congrArg (fun f => f (s g)) hp
      exact hp'
    exact ⟨⟨s, hp, hsp⟩⟩
  let : IsIso φ := hφ
  have : IsIso φ.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map φ))
  intro X
  change IsIso (φ.hom.app (op X))
  exact NatIso.isIso_app_of_isIso φ.hom (op X)

end Motivic.PresheafWithTransfers

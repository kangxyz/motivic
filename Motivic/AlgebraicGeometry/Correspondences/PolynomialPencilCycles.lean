/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.GlobalBoundaryPencil
public import Motivic.Aglib.AlgebraicGeometry.PolynomialBoundaryPencil

/-! # Whole polynomial pencil endpoint cycles -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u
namespace Motivic.PolynomialPencilCycles

/-- Transport a whole endpoint span along its actual scheme isomorphism. -/
theorem span_eq_of_iso {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {D E : Scheme.{u}} (e : E ≅ D)
    (f : D ⟶ X.left) [IsFinite f] [Flat f] (g : D ⟶ Y.left)
    (h : f ≫ X.hom = g ≫ Y.hom)
    (f' : E ⟶ X.left) [IsFinite f'] [Flat f'] (g' : E ⟶ Y.left)
    (h' : f' ≫ X.hom = g' ≫ Y.hom)
    (hf : e.hom ≫ f = f') (hg : e.hom ≫ g = g') :
    Cor.ofFiniteFlatSpan f' g' h' = Cor.ofFiniteFlatSpan f g h := by
  subst f'
  subst g'
  exact GlobalBoundaryPencil.ofFiniteFlatSpan_precompIso e f g h




/-- Finiteness and flatness of the original zero section follow from the actual pencil. -/
theorem zero_finite_flat {k : Type u} [Field k]
    {X : Scheme.{u}} (b : X ⟶ Spec (.of k)) {D : Scheme.{u}} (f : D ⟶ X)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf)
    [IsFinite (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f)]
    [Flat (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f)] :
    IsFinite (Hom.zeroInclusion a ≫ f) ∧ Flat (Hom.zeroInclusion a ≫ f) := by
  let e := zeroFibreOverBaseIso b f L a c
  have he : Hom.zeroInclusion a ≫ f = e.inv ≫
      pullback.fst (endpoint b 0)
        (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) := by
    rw [← zeroFibreOverBaseIso_hom_base b f L a c]
    simp [e]
  rw [he]
  exact ⟨inferInstance, inferInstance⟩

/-- Finiteness and flatness of the original one section follow from the actual pencil. -/
theorem one_finite_flat {k : Type u} [Field k]
    {X : Scheme.{u}} (b : X ⟶ Spec (.of k)) {D : Scheme.{u}} (f : D ⟶ X)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf)
    [IsFinite (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f)]
    [Flat (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f)] :
    IsFinite (Hom.zeroInclusion c ≫ f) ∧ Flat (Hom.zeroInclusion c ≫ f) := by
  let e := oneFibreOverBaseIso b f L a c
  have he : Hom.zeroInclusion c ≫ f = e.inv ≫
      pullback.fst (endpoint b 1)
        (Hom.zeroInclusion (familyMap (f ≫ b) L a c) ≫ parameterMap b f) := by
    rw [← oneFibreOverBaseIso_hom_base b f L a c]
    simp [e]
  rw [he]
  exact ⟨inferInstance, inferInstance⟩




/-- The whole zero endpoint span is the original section's cycle, not its reduction. -/
theorem zero_endpoint_cycle {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {D : Scheme.{u}} (f : D ⟶ X.left)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf)
    (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom)
    [IsFinite (Hom.zeroInclusion a ≫ f)] [Flat (Hom.zeroInclusion a ≫ f)]
    [IsFinite (Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ parameterMap X.hom f)]
    [Flat (Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ parameterMap X.hom f)] :
    let F := Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ parameterMap X.hom f
    let G := Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ projection (f ≫ X.hom) ≫ g
    ∀ hb : pullback.fst (endpoint X.hom 0) F ≫ X.hom =
      (pullback.snd (endpoint X.hom 0) F ≫ G) ≫ Y.hom,
    Cor.ofFiniteFlatSpan (X := X) (Y := Y) (pullback.fst (endpoint X.hom 0) F)
      (pullback.snd (endpoint X.hom 0) F ≫ G) hb =
    Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ f) (Hom.zeroInclusion a ≫ g)
      (by simp only [Category.assoc, h]) := by
  intro F G hb
  apply span_eq_of_iso (zeroFibreOverBaseIso X.hom f L a c)
  · exact zeroFibreOverBaseIso_hom_base X.hom f L a c
  · simpa only [Category.assoc] using
      congrArg (fun z ↦ z ≫ g) (zeroFibreOverBaseIso_hom_original X.hom f L a c)

/-- The whole one endpoint span is the original section's cycle, not its reduction. -/
theorem one_endpoint_cycle {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {D : Scheme.{u}} (f : D ⟶ X.left)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf)
    (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom)
    [IsFinite (Hom.zeroInclusion c ≫ f)] [Flat (Hom.zeroInclusion c ≫ f)]
    [IsFinite (Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ parameterMap X.hom f)]
    [Flat (Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ parameterMap X.hom f)] :
    let F := Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ parameterMap X.hom f
    let G := Hom.zeroInclusion (familyMap (f ≫ X.hom) L a c) ≫ projection (f ≫ X.hom) ≫ g
    ∀ hb : pullback.fst (endpoint X.hom 1) F ≫ X.hom =
      (pullback.snd (endpoint X.hom 1) F ≫ G) ≫ Y.hom,
    Cor.ofFiniteFlatSpan (X := X) (Y := Y) (pullback.fst (endpoint X.hom 1) F)
      (pullback.snd (endpoint X.hom 1) F ≫ G) hb =
    Cor.ofFiniteFlatSpan (Hom.zeroInclusion c ≫ f) (Hom.zeroInclusion c ≫ g)
      (by simp only [Category.assoc, h]) := by
  intro F G hb
  apply span_eq_of_iso (oneFibreOverBaseIso X.hom f L a c)
  · exact oneFibreOverBaseIso_hom_base X.hom f L a c
  · simpa only [Category.assoc] using
      congrArg (fun z ↦ z ≫ g) (oneFibreOverBaseIso_hom_original X.hom f L a c)

end Motivic.PolynomialPencilCycles

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Simplex.CategoricalProduct

public import Motivic.AlgebraicGeometry.Correspondences.Singular.Functor
public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.Graph
public import Motivic.Transfers.Presheaf.GraphRestriction
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Presheaf
public import Motivic.Aglib.Algebra.Homology.Embedding.SignedShift
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Indexing
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Singular complexes of presheaves with transfers

The actual exterior action makes every degree `U ↦ P(U × Δⁿ)` a presheaf
with transfers. The alternating coface differential is transfer-natural, so
these are a chain complex in presheaves with transfers, functorial in `P`.
The cochain placement sends chain degree `r` to degree `q-r`, preserving the
alternating differential and extending by zero above `q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial ZeroObject

universe v u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.SingularComplex

variable {k : Type u} [Field k]

/-- The degree-`n` singular transfer presheaf uses the actual exterior cycles. -/
def singularTerm (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    PresheafWithTransfers.{v} k :=
  AdditiveFunctor.of (singularFunctor P ⋙ HomologicalComplex.eval _ _ n)

/-- The all-degree alternating singular complex in presheaves with transfers. -/
def singularComplex (P : PresheafWithTransfers.{v} k) :
    ChainComplex (PresheafWithTransfers.{v} k) ℕ where
  X := singularTerm P
  d i j := ⟨{
    app U := (singularObj P U.unop).d i j
    naturality _U _V f := (singularTransfer P f.unop).comm i j }⟩
  shape i j hij := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (singularObj P U.unop).shape i j hij
  d_comp_d' i j l _ _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (singularObj P U.unop).d_comp_d i j l

@[simp]
theorem singularComplex_X_obj (P : PresheafWithTransfers.{v} k) (n : ℕ) (U : Cor k) :
    ((singularComplex P).X n).obj.obj (op U) = sections P (Cor.simplexProduct U n) := rfl

@[simp]
theorem singularComplex_X_map (P : PresheafWithTransfers.{v} k) (n : ℕ)
    {U V : Cor k} (α : U ⟶ V) :
    ((singularComplex P).X n).obj.map α.op = transfer P (Cor.simplexExterior n α) := rfl

/-- The differential is the original alternating sum of product-coface transfers. -/
theorem singularComplex_d_app (P : PresheafWithTransfers.{v} k) (n : ℕ) (U : Cor k) :
    ((singularComplex P).d (n + 1) n).hom.app (op U) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U.toSmoothSite)
          ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) :=
  singularObj_d P U n

private theorem transfer_square (P : PresheafWithTransfers.{v} k)
    {A B C D : Cor k} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D}
    (h : a ≫ b = c ≫ d) :
    transfer P b ≫ transfer P a = transfer P d ≫ transfer P c := by
  rw [← transfer_comp, ← transfer_comp, h]

/-- An individual coface gives an actual transfer-natural morphism of singular terms. -/
def singularFace (P : PresheafWithTransfers.{v} k) (n : ℕ) (i : Fin (n + 2)) :
    (singularComplex P).X (n + 1) ⟶ (singularComplex P).X n :=
  ⟨{
    app U := transfer P ((Cor.graphFunctor k).map
      (SmoothSite.productMap (𝟙 U.unop.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i)))
    naturality U V f := by
      change transfer P (Cor.simplexExterior (n + 1) f.unop) ≫ _ =
        _ ≫ transfer P (Cor.simplexExterior n f.unop)
      exact transfer_square P (Cor.simplexExterior_graph_interchange
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i) f.unop).symm }⟩

@[simp]
theorem singularFace_app (P : PresheafWithTransfers.{v} k) (n : ℕ)
    (i : Fin (n + 2)) (U : Cor k) :
    (singularFace P n i).hom.app (op U) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) := rfl

/-- The all-degree differential is the alternating sum of actual natural coface transfers. -/
theorem singularComplex_d (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (singularComplex P).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • singularFace P n i := by
  apply (AdditiveFunctor.forget _ _).map_injective
  simp only [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_zsmul]
  apply NatTrans.ext
  funext U
  simp only [NatTrans.app_sum, NatTrans.app_zsmul]
  exact singularObj_d P U.unop n

/-- The first differential is the difference of the two actual natural coface transfers. -/
theorem singularComplex_d_one_zero (P : PresheafWithTransfers.{v} k) :
    (singularComplex P).d 1 0 = singularFace P 0 0 - singularFace P 0 1 := by
  rw [singularComplex_d]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- A coefficient morphism gives a chain map natural for every actual transfer. -/
def singularComplexMap {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    singularComplex P ⟶ singularComplex Q where
  f n := ⟨{
    app U := η.hom.app (op (Cor.simplexProduct U.unop n))
    naturality _U _V f := η.hom.naturality (Cor.simplexExterior n f.unop).op }⟩
  comm' i j _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (SingularComplex.map (Cor.simplexProductCosimplicial U.unop) η.hom).comm i j

@[simp]
theorem singularComplexMap_f_app {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    (n : ℕ) (U : Cor k) :
    ((singularComplexMap η).f n).hom.app (op U) =
      η.hom.app (op (Cor.simplexProduct U n)) := rfl

/-- The full singular construction is functorial in the transfer presheaf. -/
def singularComplexFunctor : PresheafWithTransfers.{v} k ⥤
    ChainComplex (PresheafWithTransfers.{v} k) ℕ where
  obj := singularComplex
  map := singularComplexMap
  map_id P := by
    ext n : 1
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl
  map_comp η θ := by
    ext n : 1
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

instance : (singularComplexFunctor.{v} (k := k)).Additive where
  map_add := by
    intro P Q η θ
    ext n : 1
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

/-- On each smooth object, the actual transfer singular complex is the existing ordinary
singular complex through the canonical categorical/literal product comparison. -/
def singularParameterIso (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) :
    singularObj P (Cor.mk U) ≅
      SingularComplex.parameterObj (_root_.AlgebraicSimplex.cosimplicialSmoothSite k)
        ((toPresheaf k).obj P) U where
  hom := SingularComplex.geometryMap (_root_.AlgebraicSimplex.categoricalSimplexProductIso U).hom
      ((toPresheaf k).obj P)
  inv := SingularComplex.geometryMap (_root_.AlgebraicSimplex.categoricalSimplexProductIso U).inv
      ((toPresheaf k).obj P)
  hom_inv_id := by
    ext n : 1
    change ((toPresheaf k).obj P).map ((_root_.AlgebraicSimplex.categoricalSimplexProductIso
        U).hom.app ⦋n⦌).op ≫
      ((toPresheaf k).obj P).map ((_root_.AlgebraicSimplex.categoricalSimplexProductIso U).inv.app
          ⦋n⦌).op = 𝟙 _
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    ext n : 1
    change ((toPresheaf k).obj P).map ((_root_.AlgebraicSimplex.categoricalSimplexProductIso
        U).inv.app ⦋n⦌).op ≫
      ((toPresheaf k).obj P).map ((_root_.AlgebraicSimplex.categoricalSimplexProductIso U).hom.app
          ⦋n⦌).op = 𝟙 _
    rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id_app, op_id, CategoryTheory.Functor.map_id]

@[simp]
theorem singularParameterIso_hom_f (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) (n : ℕ) :
    (singularParameterIso P U).hom.f n =
      ((toPresheaf k).obj P).map
        (SmoothSite.categoricalProductIso U
          ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌)).hom.op :=
  rfl

/-- Pullback along the categorical/literal product comparison is natural for
an ordinary presheaf and an arbitrary fixed smooth factor. -/
theorem categoricalProduct_pullback_naturality
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v})
    {U V : SmoothSite (Spec (.of k))} (f : U ⟶ V) (T : SmoothSite (Spec (.of k))) :
    F.map (SmoothSite.productMap f (𝟙 T)).op ≫
        F.map (SmoothSite.categoricalProductIso U T).hom.op =
      F.map (SmoothSite.categoricalProductIso V T).hom.op ≫
        F.map (prod.map f (𝟙 T)).op := by
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  exact congrArg (fun g => F.map g.op)
    (SmoothSite.categoricalProductIso_naturality f (𝟙 T)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degreewise graph restriction recovers the existing ordinary singular presheaf,
through the actual categorical/literal product comparison. -/
def singularTermUnderlyingIso (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (toPresheaf k).obj ((singularComplex P).X n) ≅
      (SingularComplex.presheafObj (_root_.AlgebraicSimplex.cosimplicialSmoothSite k)
        ((toPresheaf k).obj P)).X n :=
  NatIso.ofComponents
    (fun U => ((toPresheaf k).obj P).mapIso
      (SmoothSite.categoricalProductIso U.unop
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌)).op)
    (by
      intro U V f
      change transfer P (Cor.simplexExterior n ((Cor.graphFunctor k).map f.unop)) ≫
          ((toPresheaf k).obj P).map (SmoothSite.categoricalProductIso V.unop
            ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌)).hom.op =
        ((toPresheaf k).obj P).map (SmoothSite.categoricalProductIso U.unop
            ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌)).hom.op ≫
          ((toPresheaf k).obj P).map
            (prod.map f.unop (𝟙 ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌))).op
      rw [Cor.simplexExterior_graph]
      exact categoricalProduct_pullback_naturality ((toPresheaf k).obj P) f.unop
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌))

/-- Forgetting the actual transfers recovers the pre-existing ordinary singular
complex by a chain isomorphism, including every differential and restriction. -/
def singularComplexUnderlyingIso (P : PresheafWithTransfers.{v} k) :
    ((toPresheaf k).mapHomologicalComplex (ComplexShape.down ℕ)).obj (singularComplex P) ≅
      SingularComplex.presheafObj (_root_.AlgebraicSimplex.cosimplicialSmoothSite k)
        ((toPresheaf k).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (singularTermUnderlyingIso P) (by
    intro i j _hij
    apply NatTrans.ext
    funext U
    exact (singularParameterIso P U.unop).hom.comm i j)

/-- The underlying comparison retains the literal product-isomorphism pullback. -/
@[simp]
theorem singularComplexUnderlyingIso_hom_f_app (P : PresheafWithTransfers.{v} k)
    (n : ℕ) (U : SmoothSite (Spec (.of k))) :
    ((singularComplexUnderlyingIso P).hom.f n).app (op U) =
      ((toPresheaf k).obj P).map
        (SmoothSite.categoricalProductIso U
          ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌)).hom.op := rfl

/-- The comparison with ordinary singular complexes is natural in the original
presheaf with transfers. -/
def singularComplexUnderlyingNatIso :
    singularComplexFunctor ⋙ (toPresheaf.{v} k).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      toPresheaf k ⋙
        SingularComplex.presheafConstruction (_root_.AlgebraicSimplex.cosimplicialSmoothSite k) :=
  NatIso.ofComponents singularComplexUnderlyingIso (by
    intro P Q η
    ext n : 1
    apply NatTrans.ext
    funext U
    exact (η.hom.naturality
      ((Cor.graphFunctor k).map (SmoothSite.categoricalProductIso U.unop
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌)).hom).op).symm)

/-- The zero ordinary presheaf is additive, so transfer presheaves have a zero object. -/
instance : (CategoryTheory.additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v}).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by change Functor.Additive _; infer_instance⟩

/-- Chain degree `r` is placed in cochain degree `q-r`, with zero extension. -/
def singularCochainFunctor (q : ℕ) : PresheafWithTransfers.{v} k ⥤
    CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  singularComplexFunctor ⋙ (ComplexShape.embeddingUpIntLE (q : ℤ)).extendFunctor _

/-- The actual cochain complex of transfer presheaves in the stated placement. -/
abbrev singularCochainComplex (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  (singularCochainFunctor q).obj P

/-- The term at `q-r` is the original singular transfer presheaf in degree `r`. -/
def singularCochainXIso (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (singularCochainComplex P q).X (Indexing.singularDegree q r) ≅
      (singularComplex P).X r :=
  (singularComplex P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl

/-- The placed complex vanishes above `q`. -/
theorem isZero_singularCochainComplex_X (P : PresheafWithTransfers.{v} k)
    (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((singularCochainComplex P q).X i) := by
  apply (singularComplex P).isZero_extend_X
  exact (ComplexShape.notMem_range_embeddingUpIntLE_iff (q : ℤ) i).2 hi

/-- Placement retains the exact alternating differential, without an extra shift sign. -/
theorem singularCochainComplex_d (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (singularCochainComplex P q).d (Indexing.singularDegree q (r + 1))
        (Indexing.singularDegree q r) =
      (singularCochainXIso P q (r + 1)).hom ≫ (singularComplex P).d (r + 1) r ≫
        (singularCochainXIso P q r).inv :=
  (singularComplex P).extend_d_eq (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl rfl

/-- The exact signed-shift comparison, natural in the transfer presheaf. -/
def singularCochainShiftNatIso (q : ℕ) :
    singularCochainFunctor.{v} (k := k) q ≅
      singularCochainFunctor 0 ⋙ CategoryTheory.shiftFunctor
        (CochainComplex (PresheafWithTransfers.{v} k) ℤ) (-(q : ℤ)) :=
  isoWhiskerLeft singularComplexFunctor (_root_.HomologicalComplex.ExtensionSignedShift.naturalIso
      q)

/-- Actual transfer cochains at weight `q` are weight zero shifted by `-q`. -/
def singularCochainShiftIso (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    singularCochainComplex P q ≅ (singularCochainComplex P 0)⟦-(q : ℤ)⟧ :=
  _root_.HomologicalComplex.ExtensionSignedShift.iso (singularComplex P) q

/-- The shifted weight-zero transfer term identified with singular degree `r`. -/
def singularShiftedCochainXIso (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    ((singularCochainComplex P 0)⟦-(q : ℤ)⟧).X (Indexing.singularDegree q r) ≅
      (singularComplex P).X r :=
  _root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (singularComplex P) q r rfl

/-- Every occupied component has exactly the sign `(-1)^(q*r)`. -/
theorem singularCochainShiftIso_hom_f (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (singularCochainShiftIso P q).hom.f (Indexing.singularDegree q r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularCochainXIso P q r).hom ≫ (singularShiftedCochainXIso P q r).inv) := by
  change (_root_.HomologicalComplex.ExtensionSignedShift.iso (singularComplex P) q).hom.f ((q : ℤ) -
      r) =
    (-1 : ℤ) ^ (q * r) •
      (((singularComplex P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
        (i' := (q : ℤ) - r) (ComplexShape.embeddingUpIntLE_f (q : ℤ) r)).hom ≫
        (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (singularComplex P) q r
            rfl).inv)
  simpa only [Units.smul_def, ← Nat.cast_mul, Int.coe_negOnePow_natCast] using
    _root_.HomologicalComplex.ExtensionSignedShift.iso_hom_f (singularComplex P) q r

/-- In weight two every component sign is positive. -/
theorem singularCochainShiftIso_two_hom_f (P : PresheafWithTransfers.{v} k) (r : ℕ) :
    (singularCochainShiftIso P 2).hom.f (Indexing.singularDegree 2 r) =
      (singularCochainXIso P 2 r).hom ≫ (singularShiftedCochainXIso P 2 r).inv := by
  simp [singularCochainShiftIso_hom_f, pow_mul]

end Motivic.PresheafWithTransfers

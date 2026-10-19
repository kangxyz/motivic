/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic
public import Lean.Util.CollectAxioms

/-!
# Public entry-point consumers

Only the public `Motivic` import supplies the actual correspondence category,
graph functor, additive presheaves and the all-degree singular transfer functor.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe v u

namespace MotivicTest.CorPublicImports

variable {k : Type u} [Field k]

example : Category (Cor k) := inferInstance
example : GrothendieckTopology (Cor k) := Cor.nisnevichTopology k
example : Preadditive (Cor k) := inferInstance
example : CategoryTheory.Limits.HasFiniteBiproducts (Cor k) := inferInstance
example : CategoryTheory.Limits.HasZeroObject (Cor k) := inferInstance
example : Preadditive (PresheafWithTransfers.{v} k) := inferInstance

example {X Y Z : SmoothSite (Spec (.of k))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Cor.graphFunctor k).map (f ≫ g) =
      (Cor.graphFunctor k).map f ≫ (Cor.graphFunctor k).map g :=
  (Cor.graphFunctor k).map_comp f g

example (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (α : X ⟶ Y) (n : ℕ) :
    (PresheafWithTransfers.singularTransfer P α).f n =
      PresheafWithTransfers.transfer P (Cor.simplexExterior n α) := rfl

example (n : ℕ) : Cor k ⥤+ Cor k := Cor.simplexExteriorAdditiveFunctor k n

example (P : PresheafWithTransfers.{v} k) :
    (Cor k)ᵒᵖ ⥤+ ChainComplex AddCommGrpCat.{v} ℕ :=
  PresheafWithTransfers.singularAdditiveFunctor P

example (P : PresheafWithTransfers.{v} k) {X Y Z : Cor k}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    PresheafWithTransfers.singularTransfer P (α ≫ β) =
      PresheafWithTransfers.singularTransfer P β ≫
        PresheafWithTransfers.singularTransfer P α :=
  PresheafWithTransfers.singularTransfer_comp P α β

example {X Y V : SmoothSite (Spec (.of k))} (α : Cor.mk X ⟶ Cor.mk Y)
    (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ α :=
  FiniteCorrespondence.exists_nisnevich_graph_factorization k α q hq x

example {X Y : SmoothSite (Spec (.of k))} (α : Cor.mk X ⟶ Cor.mk Y)
    {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left]
    (hq : ∀ y : Y.left, ∃ (i : I) (v : (V i).left),
      (q i).left v = y ∧ IsIso ((q i).left.residueFieldMap v)) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (label : Fin n → I) (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ α :=
  FiniteCorrespondence.exists_nisnevich_graph_family_factorization k α V q hq x

example {X Y V : SmoothSite (Spec (.of k))} (α : Cor.mk X ⟶ Cor.mk V)
    (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (hzero : α ≫ (Cor.graphFunctor k).map q = 0) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
        (Cor.graphFunctor k).map g ≫ α =
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
            β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) :=
  FiniteCorrespondence.exists_nisnevich_cech_boundary k α q hq hzero x

example (P : PresheafWithTransfers.{v} k) :
    PresheafWithTransfers.IsNisnevichSheaf k P ↔
      Presheaf.IsSheaf (Cor.nisnevichTopology k) P.obj :=
  PresheafWithTransfers.isNisnevichSheaf_iff_correspondenceTopology P

example : PresheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k :=
  PresheafWithTransfers.nisnevichSheafify k

example : PresheafWithTransfers.nisnevichSheafify k ⊣ SheafWithTransfers.forget k :=
  PresheafWithTransfers.nisnevichSheafificationAdjunction k

example : PresheafWithTransfers.toPresheaf k ⋙
    presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1} ≅
      PresheafWithTransfers.nisnevichSheafify k ⋙ SheafWithTransfers.toSheaf k :=
  PresheafWithTransfers.nisnevichSheafificationUnderlyingIso k

open Lean in
run_cmd do
  for name in #[``Motivic.Cor.category, ``Motivic.Cor.graphFunctor,
      ``Motivic.PresheafWithTransfers.yonedaAddEquiv,
      ``Motivic.PresheafWithTransfers.singularTransfer,
      ``Motivic.Cor.simplexExteriorAdditiveFunctor,
      ``Motivic.PresheafWithTransfers.singularAdditiveFunctor,
      ``Motivic.FiniteCorrespondence.exists_nisnevich_graph_factorization,
      ``Motivic.FiniteCorrespondence.exists_nisnevich_graph_family_factorization,
      ``Motivic.FiniteCorrespondence.exists_nisnevich_cech_boundary,
      ``Motivic.Cor.coproductIsColimit, ``Motivic.Cor.empty_isZero,
      ``Motivic.Cor.nisnevichTopology, ``Motivic.Cor.principal_covering_basis,
      ``Motivic.PresheafWithTransfers.isNisnevichSheaf_iff_correspondenceTopology,
      ``Motivic.PresheafWithTransfers.nisnevichSheafificationAdjunction,
      ``Motivic.PresheafWithTransfers.nisnevichSheafificationUnderlyingIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.CorPublicImports

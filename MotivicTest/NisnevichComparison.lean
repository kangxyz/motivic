/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.NisnevichComparison
public import Lean.Util.CollectAxioms

/-! # Consumers of actual Nisnevich descent with transfers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Opposite

universe u v

namespace MotivicTest.NisnevichComparison

variable {k : Type u} [Field k]

example (P : PresheafWithTransfers.{v} k) (E : AddCommGrpCat.{v})
    {n : ℕ} (Y : Fin n → SmoothSite (Spec (.of k))) :
    Function.Bijective (fun s : E ⟶ P.obj.obj (op (Cor.mk (SmoothSite.finiteCoproduct Y))) =>
      fun i => s ≫ PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i))) :=
  PresheafWithTransfers.finiteCoproduct_sections_bijective P.obj E Y

example (P : PresheafWithTransfers.{v} k) (E : AddCommGrpCat.{v})
    (s : E ⟶ P.obj.obj (op (Cor.empty k))) : s = 0 :=
  PresheafWithTransfers.section_eq_zero_of_isEmpty P.obj E (Cor.empty k) s

example (P : PresheafWithTransfers.{v} k)
    (hP : PresheafWithTransfers.IsNisnevichSheaf k P) :
    Presheaf.IsSheaf (Cor.nisnevichTopology k) P.obj :=
  PresheafWithTransfers.isSheaf_correspondenceTopology_of_restriction P.obj hP

example (P : PresheafWithTransfers.{v} k)
    (hP : Presheaf.IsSheaf (Cor.nisnevichTopology k) P.obj) (E : AddCommGrpCat.{v})
    {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X) (hq : Cor.IsNisnevichCover k q) :
    Presieve.IsSheafFor (((PresheafWithTransfers.toPresheaf k).obj P) ⋙
      coyoneda.obj (op E)) (Presieve.singleton q) :=
  PresheafWithTransfers.isSheafFor_restriction_singleton_of_correspondenceSheaf P.obj hP E q hq

example (P : PresheafWithTransfers.{v} k) :
    PresheafWithTransfers.IsNisnevichSheaf k P ↔
      Presheaf.IsSheaf (Cor.nisnevichTopology k) P.obj :=
  PresheafWithTransfers.isNisnevichSheaf_iff_correspondenceTopology P

example (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] :
    Presheaf.IsSheaf (Cor.nisnevichTopology k) F ↔
      Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((Cor.graphFunctor k).op ⋙ F) :=
  PresheafWithTransfers.isSheaf_correspondenceTopology_iff_restriction F

open Lean in
run_cmd do
  for name in #[``PresheafWithTransfers.finiteCoproduct_sections_bijective,
      ``PresheafWithTransfers.correspondence_compatible_of_cech_compatible,
      ``PresheafWithTransfers.isSheafFor_graph_singleton_iff,
      ``PresheafWithTransfers.isSheaf_correspondenceTopology_of_restriction,
      ``PresheafWithTransfers.isSheafFor_restriction_singleton_of_correspondenceSheaf,
      ``PresheafWithTransfers.isSheaf_correspondenceTopology_iff_restriction,
      ``PresheafWithTransfers.isNisnevichSheaf_iff_correspondenceTopology] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichComparison

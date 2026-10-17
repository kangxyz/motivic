/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteRepresentativeLiftComparison
public import Lean.Util.CollectAxioms

/-!
# Controlled lift independence for actual representatives of a germ tuple

The Čech matching condition is proved, not assumed. Common finite support and
actual branch-controlled lifts remain explicit; this is not yet an envelope
functor or an ordinary-cohomology acyclicity theorem.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace MotivicTest.FiniteRepresentativeLiftComparison
open Motivic Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))} {n : ℕ} (y : Fin n → Y.left)
  (N : ∀ i, SmoothSite.NisnevichNeighborhood Y (y i))
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
set_option quotPrecheck false in
local notation "V" => (fun i => (SmoothSite.nisnevichNeighborhoodFunctor Y (y i)).obj (N i))
set_option quotPrecheck false in
local notation "W" => (SmoothSite.finiteCoproduct V)
set_option quotPrecheck false in
local notation "q" => (SmoothSite.finiteCoproductDesc (fun i => (N i).toBase))
set_option quotPrecheck false in
local notation "T" => (Set.range (fun i => (SmoothSite.finiteCoproductι V i).left (N i).center))

/-- Different actual controlled lifts of the same correspondence have equal
original source germs on representatives of one original target germ tuple. -/
theorem actual_original_transfer_germ_comparison
    (α α' : FiniteCorrespondence X.hom (W).hom)
    (heq : (α : Cor.mk X ⟶ Cor.mk W) ≫ (Cor.graphFunctor k).map q =
      α' ≫ (Cor.graphFunctor k).map q)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ (α - α').support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap (q).left (MorphismProperty.Over.w q))
    (x : X.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hfirst' : ∀ A ∈ α'.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ v : (W).left, (q).left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso ((q).left.residueFieldMap v) ∧ v ∈ T)
    (a : ∀ z : Y.left, (SmoothSite.nisnevichPointFiberCocone Y z F).pt)
    (s : P.sections (Cor.mk W))
    (hs : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (y i) F).ι.app (op (N i))
      ((F).map (SmoothSite.finiteCoproductι V i).op s) = a (y i)) :
    SmoothSite.sectionToNisnevichPoint F X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint F X x (P.transfer α' s) := by
  exact transfer_germ_eq_of_finite_representatives k P y N α α' heq C j r hr x
    hfirst hfirst' hq a s hs

open Lean in
run_cmd do
  for name in #[``actual_original_transfer_germ_comparison,
      ``SmoothSite.finite_representative_cech_matching,
      ``SmoothSite.exists_section_with_finite_representative_cech_matching,
      ``SmoothSite.exists_original_germ_representative] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite-representative transfer comparison: standard foundations only."

end MotivicTest.FiniteRepresentativeLiftComparison

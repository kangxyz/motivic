/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteRepresentativeLiftIndependence
public import Lean.Util.CollectAxioms

/-!
# Actual finite-representative lift independence without supplied common support

Both common finite support and matching Čech germs are proved from the original
lifts and original germ tuple. Only the exact graph equality and actual target
center controls remain. This does not yet construct the transfer envelope.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace MotivicTest.FiniteRepresentativeLiftIndependence
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

/-- Original source germs agree for finite representative lifts; no common-support
or Čech-matching hypothesis is required. -/
theorem actual_original_lift_independence
    (α α' : FiniteCorrespondence X.hom (W).hom)
    (heq : (α : Cor.mk X ⟶ Cor.mk W) ≫ (Cor.graphFunctor k).map q =
      α' ≫ (Cor.graphFunctor k).map q)
    (x : X.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hfirst' : ∀ A ∈ α'.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (a : ∀ z : Y.left, (SmoothSite.nisnevichPointFiberCocone Y z F).pt)
    (s : P.sections (Cor.mk W))
    (hs : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (y i) F).ι.app (op (N i))
      ((F).map (SmoothSite.finiteCoproductι V i).op s) = a (y i)) :
    SmoothSite.sectionToNisnevichPoint F X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint F X x (P.transfer α' s) := by
  exact transfer_germ_eq_of_finite_representatives_auto_support k P y N α α' heq x
    hfirst hfirst' a s hs

open Lean in
run_cmd do
  for name in #[``actual_original_lift_independence,
      ``transfer_germ_eq_of_matching_cech_germs_auto_support,
      ``AlgebraicGeometry.exists_finite_common_closed_image_with_coverage] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original lift comparison with constructed support: standard foundations only."

end MotivicTest.FiniteRepresentativeLiftIndependence

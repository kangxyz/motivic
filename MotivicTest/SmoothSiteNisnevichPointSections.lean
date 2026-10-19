/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Sections
public import Lean.Util.CollectAxioms

/-! # Consumers of actual zero representatives in the Nisnevich point fiber -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open  _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u v

example {U X : Scheme.{u}} (f : U ⟶ X) (x : X)
    (t : Spec (X.residueField x) ⟶ U) (ht : t ≫ f = X.fromSpecResidueField x) :
    IsIso (f.residueFieldMap (t default)) :=
  f.isIso_residueFieldMap_of_canonicalPoint_lift x t ht

variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (s : F.obj (op X))

example (N : NisnevichNeighborhood X x) :
    IsIso (N.toBase.left.residueFieldMap N.center) := inferInstance

example (N : NisnevichNeighborhood X x) :
    F.map N.toBase.op ≫ (nisnevichPointFiberCocone X x F).ι.app (op N) =
      sectionToNisnevichPoint F X x := restriction_sectionToNisnevichPoint F N

example : sectionToNisnevichPoint F X x s = 0 ↔
    ∃ N : NisnevichNeighborhood X x, F.map N.toBase.op s = 0 :=
  sectionToNisnevichPoint_eq_zero_iff F s

example (hs : sectionToNisnevichPoint F X x s = 0)
    (T : Set X.left) (hT : T.Finite) (hclosed : ∀ y ∈ T, IsClosed ({y} : Set X.left))
    (hx : x ∈ T) :
    ∃ N : NisnevichNeighborhood X x, IsAffine N.obj.obj.left ∧
      N.toBase.left ⁻¹' T = {N.center} ∧ F.map N.toBase.op s = 0 :=
  exists_normalized_zero_representative F s hs T hT hclosed hx

open Lean in
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood in
run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_canonicalPoint_lift,
      ``isIso_residueFieldMap_center,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.sectionToNisnevichPoint,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.sectionToNisnevichPoint_eq_zero_iff,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_normalized_zero_representative] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual point-fiber zero representatives use only standard Lean foundations."

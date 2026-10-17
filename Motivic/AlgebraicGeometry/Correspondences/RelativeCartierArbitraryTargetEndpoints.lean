/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeCartierEndpoints
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatSpanForgottenEndpoints

/-!
# Arbitrary-target endpoints for separated finite-type Cartier curve families

A separated quasi-compact smooth relative curve over the affine line is
Noetherian. Its boundary-avoiding open is consequently an actual smooth-site
object. Retaining this open proves the divisor's joint embedding; the arbitrary
original target map can then be forgotten by the proved graph-postcomposition
identity. Family flatness and divisor properness remain explicit.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Hom
open scoped Polynomial

universe u

namespace Motivic.RelativeCartierDivisor

variable {k : Type u} [Field k] {C U : Scheme.{u}}
  (p : C ⟶ Spec (.of k[X])) [SmoothOfRelativeDimension 1 p]
  [IsSeparated p] [QuasiCompact p] (j : U ⟶ C) [IsOpenImmersion j]

/-- The actual boundary-avoiding open, with its original constant-field map.
Its quasi-compactness is derived from the finite-type relative curve. -/
def retainedOpen : SmoothSite (Spec (.of k)) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsNoetherian C := isNoetherian_of_finiteType p
  have : IsNoetherian U := isNoetherian_of_finiteType j
  exact SmoothSite.mk (j ≫ p ≫ (FiniteFlatCurveFamily.line k).hom)

variable {Y : SmoothSite (Spec (.of k))} {D : Scheme.{u}} (i : D ⟶ C)
  [IsClosedImmersion i] (hI : IsLocallyRankOne C (idealModule i))
  [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (hAvoid : Set.range i ⊆ Set.range j) (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ (FiniteFlatCurveFamily.line k).hom = g ≫ Y.hom)

/-- Actual graph evaluation for the original arbitrary target of a separated
finite-type relative Cartier family. Neither its original target map nor its
joint parameter/target map is required to be an embedding. -/
theorem graph_evaluation_correspondence_of_separated_quasiCompact (a : k) :
    (Cor.graphFunctor k).map (FiniteFlatCurveFamily.evaluationPoint k a) ≫
        correspondence (X := FiniteFlatCurveFamily.line k) (Y := Y) p i hI j hAvoid g hbase =
      endpointCorrespondence p i hI j hAvoid g hbase a := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  let R := retainedOpen p j
  let r : D ⟶ R.left := IsOpenImmersion.lift j i hAvoid
  have hr : (i ≫ p) ≫ (FiniteFlatCurveFamily.line k).hom = r ≫ R.hom := by
    change (i ≫ p) ≫ (FiniteFlatCurveFamily.line k).hom =
      IsOpenImmersion.lift j i hAvoid ≫ j ≫ p ≫ (FiniteFlatCurveFamily.line k).hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc]
  have : IsClosedImmersion (r ≫ j) := by
    change IsClosedImmersion (IsOpenImmersion.lift j i hAvoid ≫ j)
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have : IsClosedImmersion r := IsClosedImmersion.of_comp r j
  have : IsClosedImmersion (pullback.lift (i ≫ p) r hr) := by
    have : IsClosedImmersion
        (pullback.lift (i ≫ p) r hr ≫ pullback.snd (FiniteFlatCurveFamily.line k).hom R.hom) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd _ _)
  let q : R ⟶ Y := SmoothSite.homMk g hbase.symm
  simpa only [correspondence, endpointCorrespondence, targetMap, r, q,
    SmoothSite.homMk_left] using
    Cor.graph_evaluation_ofFiniteFlatSpan_postcompose (Y := R) (Z := Y)
      (i ≫ p) r hr q a

/-- Both original scheme-theoretic divisor endpoints, for an arbitrary target. -/
theorem graph_endpoints_correspondence_of_separated_quasiCompact :
    ((Cor.graphFunctor k).map (FiniteFlatCurveFamily.evaluationPoint k 0) ≫
        correspondence (X := FiniteFlatCurveFamily.line k) (Y := Y) p i hI j hAvoid g hbase =
      endpointCorrespondence p i hI j hAvoid g hbase 0) ∧
    ((Cor.graphFunctor k).map (FiniteFlatCurveFamily.evaluationPoint k 1) ≫
        correspondence (X := FiniteFlatCurveFamily.line k) (Y := Y) p i hI j hAvoid g hbase =
      endpointCorrespondence p i hI j hAvoid g hbase 1) :=
  ⟨graph_evaluation_correspondence_of_separated_quasiCompact p j i hI hAvoid g hbase 0,
    graph_evaluation_correspondence_of_separated_quasiCompact p j i hI hAvoid g hbase 1⟩

end Motivic.RelativeCartierDivisor

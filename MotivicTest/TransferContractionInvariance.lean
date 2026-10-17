/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance

/-! Ordinary HI for actual contraction, over arbitrary fields and coefficient universes. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers

universe v u

variable {k : Type u} [Field k]

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    IsA1Invariant (affineLineSections P) :=
  withParameter_isA1Invariant P hP (SmoothSite.affineLine (.of k))

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    IsA1Invariant (torusSections P) :=
  withParameter_isA1Invariant P hP (SmoothSite.torus (.of k))

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    IsA1Invariant (contraction P) := contraction_isA1Invariant P hP

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k) ((toPresheaf k).obj (contraction P)) X) :=
  contraction_isA1Invariant P hP X

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    (X : SmoothSite (Spec (.of k))) :
    IsIso (transfer (contraction P)
      ((Cor.graphFunctor k).map (SmoothSite.a1Projection (.of k) X))) :=
  contraction_isA1Invariant P hP X

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    (X : SmoothSite (Spec (.of k))) (a : k) :
    (A1.projectionIso (.of k) ((toPresheaf k).obj (contraction P))
      (contraction_isA1Invariant P hP) X).inv =
      A1.sectionPullback (.of k) ((toPresheaf k).obj (contraction P)) X a :=
  A1.projectionIso_inv _ _ _ _ _

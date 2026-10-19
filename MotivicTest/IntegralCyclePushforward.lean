/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.CorrespondenceCycle
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.ResidueDegree

/-! # Actual ideal-sheaf cycles, finite residue degrees, and correspondence consumers -/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (FiniteSupportCycle IntegralClosedSubscheme IntegralCycle)
open _root_.AlgebraicGeometry.Scheme.Hom (residueDegree_pos)
open CategoryTheory AlgebraicGeometry Motivic

universe u

variable {X Y Z S : Scheme.{u}}

example (f : X ⟶ Y) [IsFinite f] (x : X) : 0 < f.residueDegree x :=
  residueDegree_pos f x

example (f : X ⟶ Y) [IsFinite f] (V : IntegralClosedSubscheme X) :
    0 < V.imageDegree f := by
  rw [V.imageDegree_eq]
  exact residueDegree_pos f V.point

example (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g]
    (c : IntegralCycle X) :
    IntegralCycle.finitePushforward (f ≫ g) c =
      IntegralCycle.finitePushforward g (IntegralCycle.finitePushforward f c) := by
  rw [IntegralCycle.finitePushforward_comp]
  rfl

example (f : X ⟶ Y) [IsFinite f] (c : IntegralCycle X) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward f c) =
      FiniteSupportCycle.residuePushforward f (IntegralCycle.toPoints c) :=
  DFunLike.congr_fun (IntegralCycle.toPoints_finitePushforward f) c

example (f : X ⟶ S) (g : Y ⟶ S) (c d : FiniteCorrespondence f g)
    (h : FiniteCorrespondence.toPoints c = FiniteCorrespondence.toPoints d) : c = d :=
  FiniteCorrespondence.toPoints_injective h

example (φ : X ⟶ Y) (g : Y ⟶ S) [IsIntegral X] [IsSeparated g] :
    FiniteCorrespondence.toPoints (graphCycle φ g) =
      Finsupp.single (graphGenerator φ g).point 1 :=
  FiniteCorrespondence.toPoints_cycle _

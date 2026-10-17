/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ProperRelativeCurve
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlat

/-!
# Relative Cartier divisors with boundary avoidance as actual correspondences

A proper flat Cartier subscheme of a smooth relative curve gives a finite
correspondence to a smooth target. Its map to the target may be defined only
on an open of the curve, provided the whole divisor avoids the complement.
The original divisor scheme is retained, including nilpotents and every generic
local length. Finiteness follows from proved relative Cartier locality and
properness, rather than an assumed correspondence or splitting operation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace Motivic.RelativeCartierDivisor

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {C D U : Scheme.{u}} (p : C ⟶ X.left) (i : D ⟶ C)
  [SmoothOfRelativeDimension 1 p] [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (j : U ⟶ C) [IsOpenImmersion j]
  (hAvoid : Set.range i ⊆ Set.range j) (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ X.hom = g ≫ Y.hom)

/-- The target map uses the original whole divisor and its actual factorization
through the open complement of the boundary. -/
def targetMap : D ⟶ Y.left := IsOpenImmersion.lift j i hAvoid ≫ g

include hbase in
omit [SmoothOfRelativeDimension 1 p] [IsClosedImmersion i]
  [Flat (i ≫ p)] [IsProper (i ≫ p)] in
/-- Boundary avoidance gives the actual structural-map equation for the span. -/
theorem targetMap_base : (i ≫ p) ≫ X.hom = targetMap i j hAvoid g ≫ Y.hom := by
  calc
    (i ≫ p) ≫ X.hom =
        ((IsOpenImmersion.lift j i hAvoid ≫ j) ≫ p) ≫ X.hom := by
      rw [IsOpenImmersion.lift_fac]
    _ = targetMap i j hAvoid g ≫ Y.hom := by
      simp only [Category.assoc, hbase, targetMap]

/-- The proper flat relative Cartier divisor defines a morphism in the actual
finite-correspondence category. Smooth sources may be disconnected. -/
def correspondence : Cor.mk X ⟶ Cor.mk Y := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  exact Cor.ofFiniteFlatSpan (i ≫ p) (targetMap i j hAvoid g)
    (targetMap_base p i j hAvoid g hbase)

/-- The original divisor maps to the actual product by its two given coordinates. -/
def productMap : D ⟶ pullback X.hom Y.hom :=
  pullback.lift (i ≫ p) (targetMap i j hAvoid g) (targetMap_base p i j hAvoid g hbase)

include hI in
/-- The literal divisor-to-product map is finite, without being assumed to be
an embedding. Distinct divisor components may have the same image. -/
theorem isFinite_productMap : IsFinite (productMap p i j hAvoid g hbase) := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  exact FiniteFlatCorrespondence.isFinite_productMap (i ≫ p) _
    (pullback.lift_fst _ _ _)

include p hI in
/-- The full original divisor, rather than its reduction, is Noetherian by
its proved finite morphism to the smooth source. -/
theorem isNoetherian_divisor : IsNoetherian D := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  exact isNoetherian_of_finiteType (i ≫ p)

/-- The underlying cycle is the pushforward of the whole original Cartier
divisor's fundamental cycle, retaining all lengths and residue degrees. -/
theorem toIntegralCycle_correspondence :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      (correspondence p i hI j hAvoid g hbase) =
      letI : IsFinite (productMap p i j hAvoid g hbase) :=
        isFinite_productMap p i hI j hAvoid g hbase
      letI : IsNoetherian D := isNoetherian_divisor p i hI
      IntegralCycle.finitePushforward (productMap p i j hAvoid g hbase) (fundamentalCycle D) := by
  have : IsFinite (i ≫ p) :=
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1
  exact Cor.toIntegralCycle_ofFiniteFlatSpan (i ≫ p) _ _

end Motivic.RelativeCartierDivisor

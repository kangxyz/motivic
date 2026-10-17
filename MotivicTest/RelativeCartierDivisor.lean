/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeCartierDivisor

/-!
# Consumers of proper flat relative Cartier correspondences

Native geometry permits arbitrary nonreduced, non-Noetherian bases. The `Cor`
consumer works over every field and on disconnected smooth source schemes,
with an explicit boundary-avoidance condition on the whole Cartier subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace MotivicTest.RelativeCartierDivisor

/-- Finiteness and finite local bases require no Noetherian or reduced base. -/
theorem arbitraryBaseFiniteLocallyFree {S C D : Scheme.{u}}
    (p : C ⟶ S) (i : D ⟶ C) [SmoothOfRelativeDimension 1 p] [IsClosedImmersion i]
    (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)] :
    IsFinite (i ≫ p) ∧ LocallyOfFinitePresentation (i ≫ p) ∧
      IsFiniteLocallyFree S (pushforwardStructureSheaf (i ≫ p)) :=
  ⟨(isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).1,
    (isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier p i hI).2,
    pushforwardStructureSheaf_isFiniteLocallyFree_of_proper_flat_cartier p i hI⟩

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {C D U : Scheme.{u}} (p : C ⟶ X.left) (i : D ⟶ C)
  [SmoothOfRelativeDimension 1 p] [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (j : U ⟶ C) [IsOpenImmersion j]
  (hAvoid : Set.range i ⊆ Set.range j) (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ X.hom = g ≫ Y.hom)

omit [IsClosedImmersion i] in
/-- Boundary avoidance changes only the target factorization, retaining the
literal original divisor scheme and both structural maps. -/
theorem literalBoundaryTarget :
    Motivic.RelativeCartierDivisor.targetMap i j hAvoid g =
      IsOpenImmersion.lift j i hAvoid ≫ g := rfl

/-- The actual Cor morphism is the pushforward of the full original divisor.
In particular no reduction, irreducibility, or embedding is inserted. -/
theorem wholeDivisorCycle :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      (Motivic.RelativeCartierDivisor.correspondence p i hI j hAvoid g hbase) =
      letI : IsFinite (Motivic.RelativeCartierDivisor.productMap p i j hAvoid g hbase) :=
        Motivic.RelativeCartierDivisor.isFinite_productMap p i hI j hAvoid g hbase
      letI : IsNoetherian D := Motivic.RelativeCartierDivisor.isNoetherian_divisor p i hI
      IntegralCycle.finitePushforward
        (Motivic.RelativeCartierDivisor.productMap p i j hAvoid g hbase) (fundamentalCycle D) :=
  Motivic.RelativeCartierDivisor.toIntegralCycle_correspondence p i hI j hAvoid g hbase

omit [IsClosedImmersion i] in
/-- A globally defined target map is recovered from the identity open. -/
theorem identityOpenTarget (a : C ⟶ Y.left) :
    Motivic.RelativeCartierDivisor.targetMap i (𝟙 C)
      (by intro x _; exact ⟨x, rfl⟩) a =
      i ≫ a := by
  dsimp only [Motivic.RelativeCartierDivisor.targetMap]
  have heq : IsOpenImmersion.lift (𝟙 C) i
      (by intro x _; exact ⟨x, rfl⟩) = i := by
    simpa only [Category.comp_id] using IsOpenImmersion.lift_fac (𝟙 C) i
      (by intro x _; exact ⟨x, rfl⟩)
  rw [heq]

open Lean in
run_cmd do
  for name in #[``Scheme.Hom.isFinite_and_locallyOfFinitePresentation_of_proper_flat_cartier,
      ``Scheme.Hom.pushforwardStructureSheaf_isFiniteLocallyFree_of_proper_flat_cartier,
      ``Motivic.RelativeCartierDivisor.targetMap,
      ``Motivic.RelativeCartierDivisor.targetMap_base,
      ``Motivic.RelativeCartierDivisor.correspondence,
      ``Motivic.RelativeCartierDivisor.isFinite_productMap,
      ``Motivic.RelativeCartierDivisor.isNoetherian_divisor,
      ``Motivic.RelativeCartierDivisor.toIntegralCycle_correspondence,
      ``arbitraryBaseFiniteLocallyFree, ``literalBoundaryTarget, ``wholeDivisorCycle,
      ``identityOpenTarget] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Relative Cartier correspondence geometry uses only standard foundations."

end MotivicTest.RelativeCartierDivisor

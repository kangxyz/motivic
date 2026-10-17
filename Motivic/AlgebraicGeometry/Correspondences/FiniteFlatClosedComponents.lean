/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlat

/-!
# Original components of an embedded finite-flat span

For an explicitly closed joint map, the existing finite-flat producer's
component images are isomorphic to the original reduced component schemes.
The coordinate equations and weighted producer sum retain the original source
and its generic local lengths. The base may be disconnected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteFlatCorrespondence

variable {S X Y D : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
  [IsSeparated q] [LocallyOfFiniteType q]
  (f : D ⟶ X) [IsFinite f] [Flat f]
  (j : D ⟶ pullback p q) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst p q = f)

/-- Closedness identifies the producer's actual component image with its source. -/
def closedComponentSchemeIso (z : genericPoints D) :
    (IntegralClosedSubscheme.pointClosure z.val).val.subscheme ≅
      (componentGenerator f j hj z).scheme :=
  asIso ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ j).toImage

@[reassoc (attr := simp)]
theorem closedComponentSchemeIso_hom_projection (z : genericPoints D) :
    (closedComponentSchemeIso f j hj z).hom ≫ (componentGenerator f j hj z).projection =
      (IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ f := by
  change ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ j).toImage ≫
    ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ j).imageι ≫
      pullback.fst p q = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc, hj]

@[reassoc (attr := simp)]
theorem closedComponentSchemeIso_hom_target (z : genericPoints D) :
    (closedComponentSchemeIso f j hj z).hom ≫
        (componentGenerator f j hj z).targetProjection =
      (IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ j ≫ pullback.snd p q := by
  change ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ j).toImage ≫
    ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ j).imageι ≫
      pullback.snd p q = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc]

/-- A closed joint map has residue degree one, so the actual producer is the
original generic-length weighted sum of its actual component generators. -/
theorem fundamentalCorrespondence_eq_sum_of_closed [IsNoetherian D] :
    fundamentalCorrespondence f j hj =
      let := IntegralCycle.genericPointFintype D
      ∑ z : genericPoints D, (genericMultiplicity z : ℤ) • (componentGenerator f j hj z).cycle := by
  classical
  let := IntegralCycle.genericPointFintype D
  simp only [fundamentalCorrespondence, cycleAssembly,
    residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one,
    FiniteCorrespondenceGenerator.cycle, Finsupp.smul_single, smul_eq_mul]
  rfl

end Motivic.FiniteFlatCorrespondence

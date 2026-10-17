/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralCycleOpenRestriction
public import Motivic.AlgebraicGeometry.Cycles.GenericFinitePushforward

/-!
# All-point consumers for actual integral-cycle open restriction

These declarations test actual ideal-sheaf pullback, arbitrary point coefficients,
original residue degrees, open-stalk scalar attachment, full nonreduced
fundamental cycles, off-open deletion, negative weights, coincident finite
images, empty opens, and literal composition of restricted finite maps.
SOURCE-ONLY PROPOSAL: not compiled.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.IntegralCycleOpenRestriction

variable {X Y Z : Scheme.{u}}

/-- The support generator is the actual pulled-back ideal sheaf. -/
theorem actualRestrictedIdeal (W : IntegralClosedSubscheme X) (U : X.Opens)
    (h : W.point ∈ U) : (W.openRestriction U h).val = W.val.comap U.ι :=
  W.openRestriction_val U h

/-- No nongeneric scheme point is lost from the faithful coefficient dictionary. -/
theorem actualAllPointCoefficient (c : IntegralCycle X) (U : X.Opens) (x : U.toScheme) :
    IntegralCycle.toPoints (IntegralCycle.openRestriction U c) x =
      IntegralCycle.toPoints c x.1 :=
  IntegralCycle.toPoints_openRestriction_apply U c x

/-- Removing the generic point removes the entire integral closed support. -/
theorem actualOmittedSupport (W : IntegralClosedSubscheme X) (U : X.Opens)
    (h : W.point ∉ U) :
    U.ι ⁻¹' (W.val.support : Set X) = ∅ ∧
      IntegralCycle.openRestriction U (Finsupp.single W (-3)) = 0 :=
  ⟨W.support_preimage_eq_empty_of_point_not_mem U h,
    IntegralCycle.openRestriction_single_of_not_mem U W h (-3)⟩

/-- Negative cycle weights are retained exactly on the actual restricted support. -/
theorem actualNegativeWeight (W : IntegralClosedSubscheme X) (U : X.Opens)
    (h : W.point ∈ U) :
    IntegralCycle.openRestriction U (Finsupp.single W (-3)) =
      Finsupp.single (W.openRestriction U h) (-3) :=
  IntegralCycle.openRestriction_single_of_mem U W h (-3)

/-- The degree belongs to the original scheme residue-field map. -/
theorem actualRestrictedResidueDegree (f : X ⟶ Y) (V : Y.Opens)
    (x : (f ⁻¹ᵁ V).toScheme) : (f ∣_ V).residueDegree x = f.residueDegree x.1 :=
  FiniteSupportCycle.residueDegree_morphismRestrict f V x

/-- The actual restriction compares the whole scalar arrow, not just its rings. -/
def actualRestrictedStalkArrow (f : X ⟶ Y) (V : Y.Opens) (x : (f ⁻¹ᵁ V).toScheme) :
    Arrow.mk ((f ∣_ V).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) :=
  FiniteSupportCycle.morphismRestrictStalkArrowIso f V x

/-- Full generic local lengths survive open restriction without reducedness. -/
theorem actualNonreducedFundamentalRestriction (U : X.Opens)
    [IsNoetherian X] [IsNoetherian U.toScheme] :
    IntegralCycle.openRestriction U (fundamentalCycle X) = fundamentalCycle U.toScheme :=
  IntegralCycle.openRestriction_fundamentalCycle U

/-- Two colliding points retain their distinct original degree-weighted signed
contributions after restriction. Neither point is required to be a component generic. -/
theorem actualRestrictedCollision (f : X ⟶ Y) [IsFinite f] (V : Y.Opens)
    (x₁ x₂ : X) (h : f x₁ = f x₂) (hx₂ : f x₂ ∈ V) (m n : ℤ) :
    IntegralCycle.finitePushforward (f ∣_ V)
        (IntegralCycle.openRestriction (f ⁻¹ᵁ V)
          (Finsupp.single (IntegralClosedSubscheme.pointClosure x₁) m +
            Finsupp.single (IntegralClosedSubscheme.pointClosure x₂) n)) =
      Finsupp.single (IntegralClosedSubscheme.pointClosure (⟨f x₂, hx₂⟩ : V.toScheme))
        (m * (f.residueDegree x₁ : ℤ) + n * (f.residueDegree x₂ : ℤ)) := by
  rw [← IntegralCycle.openRestriction_finitePushforward,
    IntegralCycle.finitePushforward_two_pointClosures f x₁ x₂ h m n]
  simpa only [IntegralClosedSubscheme.openRestriction,
    IntegralClosedSubscheme.point_pointClosure] using
    IntegralCycle.openRestriction_single_of_mem V
      (IntegralClosedSubscheme.pointClosure (f x₂))
      (by simpa only [IntegralClosedSubscheme.point_pointClosure] using hx₂)
      (m * (f.residueDegree x₁ : ℤ) + n * (f.residueDegree x₂ : ℤ))

/-- The empty-open branch is zero without choosing any point or component. -/
theorem actualEmptyOpen (U : X.Opens) [IsEmpty U.toScheme] (c : IntegralCycle X) :
    IntegralCycle.openRestriction U c = 0 := by
  apply IntegralCycle.toPoints_injective
  ext x
  exact isEmptyElim x

/-- Literal map composition is compatible with both actual finite pushforwards. -/
theorem actualRestrictedComposition (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] (V : Z.Opens) :
    IntegralCycle.finitePushforward ((f ≫ g) ∣_ V) =
      (IntegralCycle.finitePushforward (g ∣_ V)).comp
        (IntegralCycle.finitePushforward (f ∣_ (g ⁻¹ᵁ V))) :=
  IntegralCycle.finitePushforward_morphismRestrict_comp f g V

end MotivicTest.IntegralCycleOpenRestriction

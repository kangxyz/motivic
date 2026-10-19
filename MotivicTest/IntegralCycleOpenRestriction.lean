/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.Open
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericFinitePushforward

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.IntegralCycleOpenRestriction

variable {X Y Z : Scheme.{u}}

/-- The support generator is the actual pulled-back ideal sheaf. -/
theorem actualRestrictedIdeal (W : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme X) (U :
    X.Opens)
    (h : W.point ∈ U) : (W.openRestriction U h).val = W.val.comap U.ι :=
  W.openRestriction_val U h

/-- No nongeneric scheme point is lost from the faithful coefficient dictionary. -/
theorem actualAllPointCoefficient (c : _root_.AlgebraicGeometry.Scheme.IntegralCycle X) (U :
    X.Opens) (x : U.toScheme) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U c) x =
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints c x.1 :=
  _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_openRestriction_apply U c x

/-- Removing the generic point removes the entire integral closed support. -/
theorem actualOmittedSupport (W : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme X) (U :
    X.Opens)
    (h : W.point ∉ U) :
    U.ι ⁻¹' (W.val.support : Set X) = ∅ ∧
      _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U (Finsupp.single W (-3)) = 0 :=
  ⟨W.support_preimage_eq_empty_of_point_not_mem U h,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_single_of_not_mem U W h (-3)⟩

/-- Negative cycle weights are retained exactly on the actual restricted support. -/
theorem actualNegativeWeight (W : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme X) (U :
    X.Opens)
    (h : W.point ∈ U) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U (Finsupp.single W (-3)) =
      Finsupp.single (W.openRestriction U h) (-3) :=
  _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_single_of_mem U W h (-3)

/-- The degree belongs to the original scheme residue-field map. -/
theorem actualRestrictedResidueDegree (f : X ⟶ Y) (V : Y.Opens)
    (x : (f ⁻¹ᵁ V).toScheme) : (f ∣_ V).residueDegree x = f.residueDegree x.1 :=
  _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residueDegree_morphismRestrict f V x

/-- The actual restriction compares the whole scalar arrow, not just its rings. -/
def actualRestrictedStalkArrow (f : X ⟶ Y) (V : Y.Opens) (x : (f ⁻¹ᵁ V).toScheme) :
    Arrow.mk ((f ∣_ V).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) :=
  _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.morphismRestrictStalkArrowIso f V x

/-- Full generic local lengths survive open restriction without reducedness. -/
theorem actualNonreducedFundamentalRestriction (U : X.Opens)
    [IsNoetherian X] [IsNoetherian U.toScheme] :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle X) =
        _root_.AlgebraicGeometry.Scheme.fundamentalCycle U.toScheme :=
  _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_fundamentalCycle U

/-- Two colliding points retain their distinct original degree-weighted signed
contributions after restriction. Neither point is required to be a component generic. -/
theorem actualRestrictedCollision (f : X ⟶ Y) [IsFinite f] (V : Y.Opens)
    (x₁ x₂ : X) (h : f x₁ = f x₂) (hx₂ : f x₂ ∈ V) (m n : ℤ) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (f ∣_ V)
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction (f ⁻¹ᵁ V)
          (Finsupp.single (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x₁)
              m +
            Finsupp.single (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x₂)
                n)) =
      Finsupp.single (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (⟨f x₂,
          hx₂⟩ : V.toScheme))
        (m * (f.residueDegree x₁ : ℤ) + n * (f.residueDegree x₂ : ℤ)) := by
  rw [← _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_finitePushforward,
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_two_pointClosures f x₁ x₂ h m n]
  simpa only [_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.openRestriction,
    _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.point_pointClosure] using
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction_single_of_mem V
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (f x₂))
      (by simpa only [_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.point_pointClosure]
          using hx₂)
      (m * (f.residueDegree x₁ : ℤ) + n * (f.residueDegree x₂ : ℤ))

/-- The empty-open branch is zero without choosing any point or component. -/
theorem actualEmptyOpen (U : X.Opens) [IsEmpty U.toScheme] (c :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle X) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.openRestriction U c = 0 := by
  apply _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints_injective
  ext x
  exact isEmptyElim x

/-- Literal map composition is compatible with both actual finite pushforwards. -/
theorem actualRestrictedComposition (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] (V : Z.Opens) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward ((f ≫ g) ∣_ V) =
      (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (g ∣_ V)).comp
        (_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward (f ∣_ (g ⁻¹ᵁ V))) :=
  _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_morphismRestrict_comp f g V

end MotivicTest.IntegralCycleOpenRestriction

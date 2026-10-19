/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Basic

/-!
# Actual correspondence-category consumers

These tests instantiate the category and its preadditive structure over an
arbitrary field. Definitional checks retain the actual cycles, componentwise
identities, and incidence Tor composition. Category laws, additivity, zero,
negation, and arbitrary integer multiplicities are consumed through the standard
category API, without imposing connectedness or integrality on the objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorrespondenceCategory
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable {k : Type u} [Field k] {X Y Z W : Cor k}

/-- Every smooth-site object is an object of the correspondence category. -/
theorem wrapsEverySmoothObject (S : SmoothSite (Spec (.of k))) :
    (Cor.mk S).toSmoothSite = S := rfl

/-- The hom type is literally the actual group of signed correspondence cycles. -/
theorem actualHom (X Y : Cor k) :
    (X ⟶ Y) = FiniteCorrespondence X.toSmoothSite.hom Y.toSmoothSite.hom := rfl

/-- The categorical identity is literally the full componentwise diagonal cycle. -/
theorem actualIdentity (X : Cor k) :
    𝟙 X = componentIdentityCycle (X := X.toSmoothSite.left) X.toSmoothSite.hom := rfl

/-- The categorical composition is literally the actual incidence Tor pairing. -/
theorem actualComposition (α : X ⟶ Y) (β : Y ⟶ Z) :
    α ≫ β = FiniteCorrespondence.incidenceTorPairing k
      (X := X.toSmoothSite) (Y := Y.toSmoothSite) (Z := Z.toSmoothSite) α β := rfl

/-- The standard category API supplies the left identity law on arbitrary cycles. -/
theorem leftIdentity (α : X ⟶ Y) : 𝟙 X ≫ α = α := Category.id_comp α

/-- The standard category API supplies the right identity law on arbitrary cycles. -/
theorem rightIdentity (α : X ⟶ Y) : α ≫ 𝟙 Y = α := Category.comp_id α

/-- Actual signed correspondences associate through the standard category API. -/
theorem associativity (α : X ⟶ Y) (β : Y ⟶ Z) (γ : Z ⟶ W) :
    (α ≫ β) ≫ γ = α ≫ (β ≫ γ) := Category.assoc α β γ

/-- Composition is additive in its first actual cycle argument. -/
theorem addLeft (α α' : X ⟶ Y) (β : Y ⟶ Z) :
    (α + α') ≫ β = α ≫ β + α' ≫ β := Preadditive.add_comp X Y Z α α' β

/-- Composition is additive in its second actual cycle argument. -/
theorem addRight (α : X ⟶ Y) (β β' : Y ⟶ Z) :
    α ≫ (β + β') = α ≫ β + α ≫ β' := Preadditive.comp_add X Y Z α β β'

/-- The zero cycle is absorbing on the left. -/
theorem zeroLeft (β : Y ⟶ Z) : (0 : X ⟶ Y) ≫ β = 0 := Limits.zero_comp

/-- The zero cycle is absorbing on the right. -/
theorem zeroRight (α : X ⟶ Y) : α ≫ (0 : Y ⟶ Z) = 0 := Limits.comp_zero

/-- Negative cycles compose using the ordinary preadditive law on the left. -/
theorem negLeft (α : X ⟶ Y) (β : Y ⟶ Z) :
    (-α) ≫ β = -(α ≫ β) := Preadditive.neg_comp α β

/-- Negative cycles compose using the ordinary preadditive law on the right. -/
theorem negRight (α : X ⟶ Y) (β : Y ⟶ Z) :
    α ≫ (-β) = -(α ≫ β) := Preadditive.comp_neg α β

/-- Associativity applies directly to signed linear combinations. -/
theorem negativeCombinationAssociativity
    (α α' : X ⟶ Y) (β : Y ⟶ Z) (γ : Z ⟶ W) :
    ((α - α') ≫ (-β)) ≫ ((-3 : ℤ) • γ) =
      (α - α') ≫ ((-β) ≫ ((-3 : ℤ) • γ)) := Category.assoc _ _ _

/-- Integer scalar composition includes negative and zero multiplicities. -/
theorem integerMultiplicities (α : X ⟶ Y) (β : Y ⟶ Z) (m n : ℤ) :
    (m • α) ≫ (n • β) = m • n • (α ≫ β) := by
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

end MotivicTest.CorrespondenceCategory

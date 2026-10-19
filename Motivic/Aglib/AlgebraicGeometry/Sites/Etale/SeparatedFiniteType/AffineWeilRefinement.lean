/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.FiniteFree.Pair
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich

/-!
# Original small-site objects from an actual affine Weil pair

An affine chart is retained on the original ambient object. The common object
is the constructed product of two Weil restrictions, not an assumed refinement.
Its arrow to the original ambient and its whole marked scheme are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open Module

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

open AlgebraicGeometry.AffineWeilRestriction

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {S : Scheme.{u}} (W : EtaleSeparatedFiniteType S)
variable {A B₁ B₂ C₁ C₂ : Type u}
variable [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C₁] [CommRing C₂]
variable [Algebra A B₁] [Algebra A B₂] [Algebra B₁ C₁] [Algebra B₂ C₂]
variable [Algebra.Etale B₁ C₁] [Algebra.Etale B₂ C₂]
variable {κ₁ κ₂ : Type u} [Fintype κ₁] [Fintype κ₂]
variable (b₁ : Basis κ₁ A B₁) (b₂ : Basis κ₂ A B₂)
variable (e : Spec (.of A) ≅ W.left)

/-- The actual Weil product as a separated finite-type étale object of the original site. -/
def affineWeilPair : EtaleSeparatedFiniteType S :=
  MorphismProperty.Over.mk ⊤
    (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫ e.hom ≫ W.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- The original ambient arrow, through its specified affine chart. -/
def affineWeilPairProjection : affineWeilPair (C₁ := C₁) (C₂ := C₂) W b₁ b₂ e ⟶ W :=
  MorphismProperty.Over.homMk (pairProjection b₁ b₂ ≫ e.hom) (by
    change (pairProjection b₁ b₂ ≫ e.hom) ≫ W.hom = _
    exact Category.assoc _ _ _)

instance : IsAffine (affineWeilPair (C₁ := C₁) (C₂ := C₂) W b₁ b₂ e).left :=
  inferInstanceAs (IsAffine (pairScheme (C₁ := C₁) (C₂ := C₂) b₁ b₂))

instance : Etale (affineWeilPairProjection (C₁ := C₁) (C₂ := C₂) W b₁ b₂ e).left :=
  inferInstanceAs (Etale (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂ ≫ e.hom))

variable {T : Type u} [CommRing T] [Algebra A T]
variable (g₁ : C₁ →ₐ[B₁] T ⊗[A] B₁) (g₂ : C₂ →ₐ[B₂] T ⊗[A] B₂)
variable {V : Scheme.{u}} (t : V ≅ Spec (.of T))

/-- The entire original marked scheme lifts, with no reducedness assumption. -/
def affineWeilPairMark : V ⟶ (affineWeilPair W b₁ b₂ e (C₁ := C₁) (C₂ := C₂)).left :=
  t.hom ≫ pairMark b₁ b₂ g₁ g₂

/-- The constructed marking lies over precisely the original marked ambient arrow. -/
theorem affineWeilPairMark_projection :
    affineWeilPairMark W b₁ b₂ e g₁ g₂ t ≫
        (affineWeilPairProjection W b₁ b₂ e).left =
      t.hom ≫ Spec.algebraMap A T ≫ e.hom := by
  change (t.hom ≫ pairMark b₁ b₂ g₁ g₂) ≫ (pairProjection b₁ b₂ ≫ e.hom) = _
  rw [Category.assoc, ← Category.assoc (pairMark b₁ b₂ g₁ g₂), pairMark_over]

/-- Composition retains any specified original cylinder or ambient projection. -/
theorem affineWeilPairMark_comp {W₀ : EtaleSeparatedFiniteType S} (f : W ⟶ W₀)
    (z : V ⟶ W.left)
    (hz : t.hom ≫ Spec.algebraMap A T ≫ e.hom = z) :
    affineWeilPairMark W b₁ b₂ e g₁ g₂ t ≫
        (affineWeilPairProjection W b₁ b₂ e ≫ f).left = z ≫ f.left := by
  change _ ≫ ((affineWeilPairProjection W b₁ b₂ e).left ≫ f.left) = _
  rw [← Category.assoc, affineWeilPairMark_projection, hz]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

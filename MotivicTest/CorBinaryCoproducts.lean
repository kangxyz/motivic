/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BinaryCoproducts

/-! # Consumers of actual disjoint-union coproducts in finite correspondences -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorBinaryCoproducts

variable (k : Type u) [Field k]

example : HasBinaryCoproducts (Cor k) := inferInstance

example : HasBinaryBiproducts (Cor k) := inferInstance

example : HasFiniteBiproducts (Cor k) := inferInstance

example : HasZeroObject (Cor k) := inferInstance

example : (Cor.empty k).toSmoothSite.left = (∅ : Scheme.{u}) := rfl

example : IsZero (Cor.empty k) := Cor.empty_isZero k

example (X Y : Cor k) :
    (Cor.coproduct k X Y).toSmoothSite.left = (X.toSmoothSite.left ⨿ Y.toSmoothSite.left) := rfl

example (X Y : Cor k) : Cor.coproductInl k X Y =
    (Cor.graphFunctor k).map (SmoothSite.coproductInl X.toSmoothSite Y.toSmoothSite) := rfl

example (X Y : Cor k) : Cor.coproductInr k X Y =
    (Cor.graphFunctor k).map (SmoothSite.coproductInr X.toSmoothSite Y.toSmoothSite) := rfl

example (X Y : SmoothSite (Spec (.of k))) (q : X ⟶ Y) [IsClosedImmersion q.left] :
    Mono ((Cor.graphFunctor k).map q) := inferInstance

example (X Y : Cor k) :
    IsColimit (BinaryCofan.mk (Cor.coproductInl k X Y) (Cor.coproductInr k X Y)) :=
  Cor.coproductIsColimit k X Y

example (X Y T : Cor k) : Function.Bijective
    (fun α : Cor.coproduct k X Y ⟶ T =>
      (Cor.coproductInl k X Y ≫ α, Cor.coproductInr k X Y ≫ α)) :=
  Cor.coproduct_restriction_bijective k X Y T

example (X Y : Cor k) :
    ∃ (p : Cor.coproduct k X Y ⟶ X) (q : Cor.coproduct k X Y ⟶ Y),
      Cor.coproductInl k X Y ≫ p = 𝟙 X ∧
      Cor.coproductInl k X Y ≫ q = 0 ∧
      Cor.coproductInr k X Y ≫ p = 0 ∧
      Cor.coproductInr k X Y ≫ q = 𝟙 Y ∧
      p ≫ Cor.coproductInl k X Y + q ≫ Cor.coproductInr k X Y =
        𝟙 (Cor.coproduct k X Y) := Cor.exists_coproduct_projections k X Y

example (X Y : SmoothSite (Spec (.of k))) :
    Cor.partialIdentity k (SmoothSite.coproductInl X Y) +
      Cor.partialIdentity k (SmoothSite.coproductInr X Y) =
        𝟙 (Cor.mk (SmoothSite.coproduct X Y)) :=
  Cor.partialIdentity_inl_add_inr k X Y

example {X Y : Cor k} [IsEmpty X.toSmoothSite.left] (α : X ⟶ Y) : α = 0 :=
  Cor.hom_eq_zero_of_isEmpty_source k α

example {X Y : Cor k} [IsEmpty Y.toSmoothSite.left] (α : X ⟶ Y) : α = 0 :=
  Cor.hom_eq_zero_of_isEmpty_target k α

end MotivicTest.CorBinaryCoproducts

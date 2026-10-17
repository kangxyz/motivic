/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ImageClosedFactor
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichGeneratorLift

/-!
# Literal closed-support control for constructed lift-image generators

The image generators used in the existing correspondence-lifting construction
retain every actual closed-support factorization of their defining component
maps. We descend that factorization through the scheme-theoretic image, keeping
both the original component map and the original graph postcomposition map.

This is control of the constructed image generator itself, not an inference
from a signed cancellation equation. Propagating these maps through the private
finite-sum lifting construction is still a separate assembly step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable (k : Type u) [Field k] {U V Y : SmoothSite (Spec (.of k))}
  (D : Scheme.{u}) [IsIntegral D]
  (m : D ⟶ pullback U.hom V.hom) [IsFinite m]
  (hm : Set.range (m ≫ pullback.fst U.hom V.hom) ∈ irreducibleComponents U.left)
  [IsFinite (m ≫ pullback.fst U.hom V.hom)]
  (q : V ⟶ Y) (C : Scheme.{u}) (j : C ⟶ pullback U.hom Y.hom) [IsClosedImmersion j]
  (a : D ⟶ C)
  (ha₁ : a ≫ j ≫ pullback.fst U.hom Y.hom = m ≫ pullback.fst U.hom V.hom)
  (ha₂ : a ≫ j ≫ pullback.snd U.hom Y.hom =
    m ≫ pullback.snd U.hom V.hom ≫ q.left)

include ha₁ ha₂

/-- The actual image generator has a literal factor map to the prescribed closed
support, compatible with both the defining component and original graph postcomposition. -/
theorem exists_supportLiftImageGenerator_closed_factor :
    ∃ r : (supportLiftImageGenerator k D m hm).scheme ⟶ C,
      m.toImage ≫ r = a ∧
      r ≫ j = (supportLiftImageGenerator k D m hm).graphPostcompositionMap
        q.left (MorphismProperty.Over.w q) := by
  let t : pullback U.hom V.hom ⟶ pullback U.hom Y.hom :=
    pullback.lift (pullback.fst U.hom V.hom) (pullback.snd U.hom V.hom ≫ q.left) (by
      rw [Category.assoc, MorphismProperty.Over.w]
      exact pullback.condition)
  have ht₁ : t ≫ pullback.fst U.hom Y.hom = pullback.fst U.hom V.hom :=
    pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd U.hom Y.hom = pullback.snd U.hom V.hom ≫ q.left :=
    pullback.lift_snd _ _ _
  have h : a ≫ j = m ≫ t := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, ht₁] using ha₁
    · simpa only [Category.assoc, ht₂] using ha₂
  refine ⟨m.imageToClosedFactor t j a h, m.toImage_imageToClosedFactor t j a h, ?_⟩
  rw [m.imageToClosedFactor_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, ht₁, graphPostcompositionMap_fst]
    rfl
  · rw [Category.assoc, ht₂, graphPostcompositionMap_snd]
    rfl

end Motivic.FiniteCorrespondenceGenerator

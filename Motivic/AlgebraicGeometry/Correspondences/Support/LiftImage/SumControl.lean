/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Support.LiftImage.Control

/-!
# Closed-support maps through signed finite sums of constructed image generators

Every generator surviving a signed finite sum comes from one of the original
summands. For the actual image generators in the lifting construction, we keep
that component's literal factor map to the closed support, including its
factorization from the defining scheme. Cancellation can remove generators
but cannot create untracked support. No positivity of Tor coefficients or
residue-degree coefficients is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {U V Y : SmoothSite (Spec (.of k))}
  {I : Type v} (E : Finset I) (c : I → ℤ)
  (D : I → Scheme.{u}) [∀ i, IsIntegral (D i)]
  (m : ∀ i, D i ⟶ pullback U.hom V.hom) [∀ i, IsFinite (m i)]
  (hm : ∀ i, Set.range (m i ≫ pullback.fst U.hom V.hom) ∈ irreducibleComponents U.left)
  [∀ i, IsFinite (m i ≫ pullback.fst U.hom V.hom)]
  (q : V ⟶ Y) (C : Scheme.{u}) (j : C ⟶ pullback U.hom Y.hom) [IsClosedImmersion j]
  (a : ∀ i, D i ⟶ C)
  (ha₁ : ∀ i ∈ E, a i ≫ j ≫ pullback.fst U.hom Y.hom = m i ≫ pullback.fst U.hom V.hom)
  (ha₂ : ∀ i ∈ E, a i ≫ j ≫ pullback.snd U.hom Y.hom =
    m i ≫ pullback.snd U.hom V.hom ≫ q.left)

include ha₁ ha₂

/-- Every surviving generator retains one original image component and both
of that component's actual closed-support triangles. Arbitrary signed weights are allowed. -/
theorem exists_component_factor_of_mem_signed_image_sum
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ (∑ i ∈ E, c i • (supportLiftImageGenerator k (D i) (m i) (hm i)).cycle).support) :
    ∃ i ∈ E, B = supportLiftImageGenerator k (D i) (m i) (hm i) ∧
      ∃ r : (supportLiftImageGenerator k (D i) (m i) (hm i)).scheme ⟶ C,
        (m i).toImage ≫ r = a i ∧
        r ≫ j = (supportLiftImageGenerator k (D i) (m i) (hm i)).graphPostcompositionMap
          q.left (MorphismProperty.Over.w q) := by
  classical
  obtain ⟨i, hi, hBi⟩ := Finsupp.mem_support_finsetSum B hB
  have hBi' : B = supportLiftImageGenerator k (D i) (m i) (hm i) := by
    simpa only [cycle, Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0),
      Finset.mem_singleton] using Finsupp.support_smul hBi
  exact ⟨i, hi, hBi', exists_supportLiftImageGenerator_closed_factor
    k (D i) (m i) (hm i) q C j (a i) (ha₁ i hi) (ha₂ i hi)⟩

/-- The actual signed sum consequently has a literal map to the closed support
on every one of its surviving generator schemes. -/
theorem exists_closed_factor_of_mem_signed_image_sum
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ (∑ i ∈ E, c i • (supportLiftImageGenerator k (D i) (m i) (hm i)).cycle).support) :
    ∃ r : B.scheme ⟶ C,
      r ≫ j = B.graphPostcompositionMap q.left (MorphismProperty.Over.w q) := by
  obtain ⟨i, _, rfl, r, _, hr⟩ := exists_component_factor_of_mem_signed_image_sum
    k E c D m hm q C j a ha₁ ha₂ B hB
  exact ⟨r, hr⟩

end Motivic.FiniteCorrespondenceGenerator

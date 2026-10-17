/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SupportLiftImageSumControl
public import Lean.Util.CollectAxioms

/-! # Consumers of literal support maps through arbitrary signed image sums -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.FiniteCorrespondenceGenerator

universe u v

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
  (B : FiniteCorrespondenceGenerator U.hom V.hom)
  (hB : B ∈ (∑ i ∈ E, c i • (supportLiftImageGenerator k (D i) (m i) (hm i)).cycle).support)

example : ∃ r : B.scheme ⟶ C,
    r ≫ j = B.graphPostcompositionMap q.left (MorphismProperty.Over.w q) :=
  exists_closed_factor_of_mem_signed_image_sum k E c D m hm q C j a ha₁ ha₂ B hB

open Lean Motivic.FiniteCorrespondenceGenerator in
run_cmd do
  for name in #[``exists_component_factor_of_mem_signed_image_sum,
      ``exists_closed_factor_of_mem_signed_image_sum] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Signed image sums retain actual support maps using only standard Lean foundations."

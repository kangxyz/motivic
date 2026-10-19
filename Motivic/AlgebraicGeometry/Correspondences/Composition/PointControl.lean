/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.PointControl

/-!
# Actual support-point provenance for signed correspondence composition

Every point of a surviving component of the original correspondence composition
comes from one actual incidence point of a pair of input support components.
The proof uses the Tor-weighted generic coefficient cycle and its genuine finite
pushforward, so it retains higher Tor terms, residue degrees, image collisions,
and signed cancellation. No support-composition law is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}

/-- Every actual point of a surviving generator of the original composition
of two geometric cycles lifts to their genuine incidence scheme. -/
theorem exists_incidence_point_of_mem_cycle_comp_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (C : FiniteCorrespondenceGenerator X.hom Z.hom)
    (hC : C ∈ ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫
      (show Cor.mk Y ⟶ Cor.mk Z from B.cycle)).support) (c : C.scheme) :
    ∃ w : A.incidence B, A.incidenceMap B w = C.inclusion c := by
  classical
  have hC' : C.toIntegralClosedSubscheme ∈
      (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
        ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫
          (show Cor.mk Y ⟶ Cor.mk Z from B.cycle))).support := by
    change C.toIntegralClosedSubscheme ∈ (Finsupp.mapDomain
      FiniteCorrespondenceGenerator.toIntegralClosedSubscheme _).support
    rw [Finsupp.mapDomain_support_of_injective toIntegralClosedSubscheme_injective]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  change C.toIntegralClosedSubscheme ∈
    (FiniteCorrespondence.toIntegralCycle (FiniteCorrespondence.incidenceTorPairing k
      (X := X) (Y := Y) (Z := Z) A.cycle B.cycle)).support at hC'
  rw [FiniteCorrespondence.incidenceTorPairing_cycle,
    A.toIntegralCycle_incidenceTorCorrespondence k B] at hC'
  exact IntegralCycle.range_subschemeι_subset_of_mem_finitePushforward
    (A.incidenceMap B)
    (IntegralCycle.ofGenericCoefficients (A.incidence B)
      (A.incidenceTorCoefficient (S := Spec (.of k)) B))
    C.toIntegralClosedSubscheme hC' (Set.mem_range_self c)

/-- Both input support points come from one actual incidence point; in
particular their intermediate projections agree exactly. -/
theorem exists_points_lift_of_mem_cycle_comp_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (C : FiniteCorrespondenceGenerator X.hom Z.hom)
    (hC : C ∈ ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫
      (show Cor.mk Y ⟶ Cor.mk Z from B.cycle)).support) (c : C.scheme) :
    ∃ a : A.scheme, ∃ b : B.scheme,
      A.projection a = C.projection c ∧
      A.targetProjection a = B.projection b ∧
      B.targetProjection b = C.targetProjection c := by
  obtain ⟨w, hw⟩ := A.exists_incidence_point_of_mem_cycle_comp_cycle B C hC c
  refine ⟨A.incidenceFst B w, A.incidenceSnd B w, ?_, ?_, ?_⟩
  · have h := congrArg (pullback.fst X.hom Z.hom) hw
    change (A.incidenceMap B ≫ pullback.fst X.hom Z.hom) w = C.projection c at h
    rw [incidenceMap_fst] at h
    exact h
  · exact congrArg (fun f : A.incidence B ⟶ Y.left ↦ f w) (A.incidence_condition B)
  · have h := congrArg (pullback.snd X.hom Z.hom) hw
    change (A.incidenceMap B ≫ pullback.snd X.hom Z.hom) w = C.targetProjection c at h
    rw [incidenceMap_snd] at h
    exact h

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}

/-- Signed cancellation can remove composition components, but every point of
every surviving component has exact provenance in two input support points. -/
theorem exists_support_points_lift_of_mem_comp
    (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom)
    (C : FiniteCorrespondenceGenerator X.hom Z.hom)
    (hC : C ∈ ((show Cor.mk X ⟶ Cor.mk Y from α) ≫ β).support) (c : C.scheme) :
    ∃ A ∈ α.support, ∃ B ∈ β.support, ∃ a : A.scheme, ∃ b : B.scheme,
      A.projection a = C.projection c ∧
      A.targetProjection a = B.projection b ∧
      B.targetProjection b = C.targetProjection c := by
  classical
  have hα : ∑ A ∈ α.support, α A • A.cycle = α := by
    simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
      Finsupp.smul_single, smul_eq_mul, mul_one] using α.sum_single
  have hβ : ∑ B ∈ β.support, β B • B.cycle = β := by
    simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
      Finsupp.smul_single, smul_eq_mul, mul_one] using β.sum_single
  have hsum : (show Cor.mk X ⟶ Cor.mk Y from α) ≫ β =
      ∑ A ∈ α.support, α A • ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫ β) := by
    change (incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip β α = _
    conv_lhs => rw [← hα]
    simp only [map_sum, map_zsmul]
    rfl
  rw [hsum] at hC
  obtain ⟨A, hA, hC⟩ := Finsupp.mem_support_finsetSum C hC
  have hC := Finsupp.support_smul hC
  have hsum' : (show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫ β =
      ∑ B ∈ β.support, β B • ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫
        (show Cor.mk Y ⟶ Cor.mk Z from B.cycle)) := by
    change incidenceTorPairing k (X := X) (Y := Y) (Z := Z) A.cycle β = _
    conv_lhs => rw [← hβ]
    simp only [map_sum, map_zsmul]
    rfl
  rw [hsum'] at hC
  obtain ⟨B, hB, hC⟩ := Finsupp.mem_support_finsetSum C hC
  obtain ⟨a, b, hs, hm, ht⟩ := A.exists_points_lift_of_mem_cycle_comp_cycle B C
    (Finsupp.support_smul hC) c
  exact ⟨A, hA, B, hB, a, b, hs, hm, ht⟩

/-- Designated target sets compose on all actual support points, including for
arbitrary signed correspondences and disconnected smooth objects. -/
theorem target_mem_of_mem_comp
    (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom)
    (x : X.left) (S : Set Y.left) (T : Set Z.left)
    (hS : ∀ A ∈ α.support, ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a ∈ S)
    (hT : ∀ B ∈ β.support, ∀ b : B.scheme,
      B.projection b ∈ S → B.targetProjection b ∈ T)
    (C : FiniteCorrespondenceGenerator X.hom Z.hom)
    (hC : C ∈ ((show Cor.mk X ⟶ Cor.mk Y from α) ≫ β).support)
    (c : C.scheme) (hc : C.projection c = x) :
    C.targetProjection c ∈ T := by
  obtain ⟨A, hA, B, hB, a, b, hs, hm, ht⟩ :=
    exists_support_points_lift_of_mem_comp α β C hC c
  exact ht ▸ hT B hB b (hm ▸ hS A hA a (hs.trans hc))

/-- Nested designated centers compose for the original signed correspondence
composition, by actual incidence-point provenance rather than a support axiom. -/
theorem target_eq_of_mem_comp
    (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom)
    (x : X.left) (y : Y.left) (z : Z.left)
    (hy : ∀ A ∈ α.support, ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a = y)
    (hz : ∀ B ∈ β.support, ∀ b : B.scheme,
      B.projection b = y → B.targetProjection b = z)
    (C : FiniteCorrespondenceGenerator X.hom Z.hom)
    (hC : C ∈ ((show Cor.mk X ⟶ Cor.mk Y from α) ≫ β).support)
    (c : C.scheme) (hc : C.projection c = x) :
    C.targetProjection c = z :=
  target_mem_of_mem_comp α β x {y} {z} hy hz C hC c hc

end FiniteCorrespondence

end Motivic

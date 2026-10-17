/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechSupportPairing

/-!
# Čech pairing with the original generic incidence coefficients

The integral-support pairing extends to every integer coefficient function on
an actual noetherian finite support. Both graph projections are the exact
finite pushforwards of that coefficient cycle. In particular the original
incidence Tor coefficients may be supplied without replacing them by the
multiplicities of a reduction or requiring a new base-change calculation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable (k : Type u) [Field k] {T Y V : SmoothSite (Spec (.of k))}

section ComponentImage

variable (W : Scheme.{u}) [IsNoetherian W]
  (m : W ⟶ pullback T.hom V.hom) [IsFinite m] (x : genericPoints W)
  [IsFinite (((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ m) ≫
    pullback.fst T.hom V.hom)]
  (hm : Set.range (((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ m) ≫
    pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)

/-- A weighted image of an actual generic point closure is the finite
pushforward of that same integral component with coefficient one. -/
theorem toIntegralCycle_weightedSupportImage_pointClosure :
    FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
      (weightedSupportImage k (T := T) (V := V)
        (IntegralClosedSubscheme.pointClosure x.val).val.subscheme
        ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ m) hm) =
      IntegralCycle.finitePushforward m
        (Finsupp.single (IntegralClosedSubscheme.pointClosure x.val) 1) := by
  rw [toIntegralCycle_weightedSupportImage, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply]
  change IntegralCycle.finitePushforward m
    (closedFundamentalCycle (IntegralClosedSubscheme.pointClosure x.val).val) = _
  rw [closedFundamentalCycle_of_isIntegral]
  rfl

end ComponentImage

section GenericPairing

variable (W : Scheme.{u}) [IsNoetherian W]
  (m₁ m₂ : W ⟶ pullback T.hom V.hom) [IsFinite m₁] [IsFinite m₂]
  [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
  [IsFinite (m₂ ≫ pullback.fst T.hom V.hom)]
  (hm₁ : ∀ x : genericPoints W,
    Set.range (((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ m₁) ≫
      pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  (q : V ⟶ Y) [Etale q.left]
  (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
  (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
    m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

include hm₁ hs ht

/-- Every signed generic coefficient is retained in an actual Čech pairing,
whose two projections are precisely the original finite cycle pushforwards. -/
theorem exists_cech_pairing_of_generic_coefficients_with_point_lift (c : genericPoints W → ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q)) =
        IntegralCycle.finitePushforward m₁ (IntegralCycle.ofGenericCoefficients W c) ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward m₂ (IntegralCycle.ofGenericCoefficients W c) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, ∃ w : W,
        (m₁ ≫ pullback.fst T.hom V.hom) w = B.projection z ∧
        (m₁ ≫ pullback.snd T.hom V.hom) w =
          (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
        (m₂ ≫ pullback.snd T.hom V.hom) w =
          (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) := by
  classical
  let := IntegralCycle.genericPointFintype W
  let D (x : genericPoints W) := IntegralClosedSubscheme.pointClosure x.val
  let r₁ (x : genericPoints W) := (D x).val.subschemeι ≫ m₁
  let r₂ (x : genericPoints W) := (D x).val.subschemeι ≫ m₂
  let (x : genericPoints W) : IsFinite (r₁ x ≫ pullback.fst T.hom V.hom) := by
    dsimp only [r₁]
    rw [Category.assoc]
    infer_instance
  let (x : genericPoints W) : IsFinite (r₂ x ≫ pullback.fst T.hom V.hom) := by
    dsimp only [r₂]
    rw [Category.assoc]
    infer_instance
  have hm₂ (x : genericPoints W) : Set.range (r₂ x ≫ pullback.fst T.hom V.hom) ∈
      irreducibleComponents T.left := by
    dsimp only [r₂]
    rw [Category.assoc, ← hs, ← Category.assoc]
    exact hm₁ x
  have h (x : genericPoints W) := exists_cech_pairing_of_common_support_with_point_lift k
    (D x).val.subscheme (r₁ x) (r₂ x) (hm₁ x) (hm₂ x) q
    (by simp only [r₁, r₂, Category.assoc, hs])
    (by simp only [r₁, r₂, Category.assoc, ht])
  choose β hβ₁ hβ₂ hpoint using h
  refine ⟨∑ x, c x • β x, ?_, ?_, ?_⟩
  · rw [Preadditive.sum_comp, IntegralCycle.ofGenericCoefficients_eq_sum]
    simp only [Preadditive.zsmul_comp, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro x _
    rw [hβ₁, toIntegralCycle_weightedSupportImage_pointClosure]
    simp only [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  · rw [Preadditive.sum_comp, IntegralCycle.ofGenericCoefficients_eq_sum]
    simp only [Preadditive.zsmul_comp, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro x _
    rw [hβ₂, toIntegralCycle_weightedSupportImage_pointClosure]
    simp only [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  · intro B hB z
    obtain ⟨x, _, hx⟩ := Finsupp.mem_support_finsetSum B hB
    obtain ⟨d, hd₁, hd₂, hd₃⟩ := hpoint x B (Finsupp.support_smul hx) z
    exact ⟨(D x).val.subschemeι d, hd₁, hd₂, hd₃⟩

/-- The original coefficient-cycle pairing is the projection of the same
construction retaining actual support-point witnesses. -/
theorem exists_cech_pairing_of_generic_coefficients (c : genericPoints W → ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q)) =
        IntegralCycle.finitePushforward m₁ (IntegralCycle.ofGenericCoefficients W c) ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward m₂ (IntegralCycle.ofGenericCoefficients W c) := by
  obtain ⟨β, h₁, h₂, _⟩ :=
    exists_cech_pairing_of_generic_coefficients_with_point_lift k W m₁ m₂ hm₁ q hs ht c
  exact ⟨β, h₁, h₂⟩

end GenericPairing

section IncidenceTor

variable {X : SmoothSite (Spec (.of k))}

/-- The genuine incidence Tor coefficient function can be used verbatim:
the first projection is the actual incidence Tor correspondence, and the
second is the finite pushforward of exactly its original coefficient cycle. -/
theorem exists_cech_pairing_of_incidenceTor_with_point_lift
    (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom)
    (m₂ : G.incidence A ⟶ pullback T.hom V.hom) [IsFinite m₂]
    (q : V ⟶ Y) [Etale q.left]
    (hs : G.incidenceMap A ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
    (ht : G.incidenceMap A ≫ pullback.snd T.hom V.hom ≫ q.left =
      m₂ ≫ pullback.snd T.hom V.hom ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        G.incidenceTorCorrespondence k A ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward m₂ (IntegralCycle.ofGenericCoefficients (G.incidence A)
          (G.incidenceTorCoefficient (S := Spec (.of k)) A)) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, ∃ w : G.incidence A,
        G.incidenceSource A w = B.projection z ∧
        G.incidenceTarget A w =
          (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
        (m₂ ≫ pullback.snd T.hom V.hom) w =
          (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) := by
  have : IsFinite (G.incidenceMap A ≫ pullback.fst T.hom V.hom) := by
    rw [incidenceMap_fst]
    infer_instance
  have : IsFinite (m₂ ≫ pullback.fst T.hom V.hom) := by rw [← hs]; infer_instance
  obtain ⟨β, h₁, h₂, hpoint⟩ := exists_cech_pairing_of_generic_coefficients_with_point_lift k
    (G.incidence A) (G.incidenceMap A) m₂ (fun x ↦ by
      rw [Category.assoc, incidenceMap_fst, G.range_incidence_component_source k A x]
      exact G.range_projection_mem) q hs ht
    (G.incidenceTorCoefficient (S := Spec (.of k)) A)
  refine ⟨β, ?_, h₂, ?_⟩
  · apply FiniteCorrespondence.toIntegralCycle_injective
    exact h₁.trans (G.toIntegralCycle_incidenceTorCorrespondence k A).symm
  · simpa only [incidenceMap_fst, incidenceMap_snd] using hpoint

/-- The original incidence-Tor pairing is retained with its unchanged type. -/
theorem exists_cech_pairing_of_incidenceTor
    (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom)
    (m₂ : G.incidence A ⟶ pullback T.hom V.hom) [IsFinite m₂]
    (q : V ⟶ Y) [Etale q.left]
    (hs : G.incidenceMap A ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
    (ht : G.incidenceMap A ≫ pullback.snd T.hom V.hom ≫ q.left =
      m₂ ≫ pullback.snd T.hom V.hom ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        G.incidenceTorCorrespondence k A ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward m₂ (IntegralCycle.ofGenericCoefficients (G.incidence A)
          (G.incidenceTorCoefficient (S := Spec (.of k)) A)) := by
  obtain ⟨β, h₁, h₂, _⟩ :=
    exists_cech_pairing_of_incidenceTor_with_point_lift k G A m₂ q hs ht
  exact ⟨β, h₁, h₂⟩

end IncidenceTor

end Motivic.FiniteCorrespondenceGenerator

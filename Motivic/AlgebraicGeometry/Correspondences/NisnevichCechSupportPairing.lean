/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichGeneratorLift
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor

/-!
# Pairing actual integral supports in an étale Čech relation

Two finite images of the same integral scheme, with the same source projection
and the same target after an étale arrow, admit an actual correspondence to the
scheme-theoretic Čech fiber product. Its two graph composites are the original
finite pushforwards, including their residue degrees. Integer weights therefore
remain unchanged. This is an elementary support-pairing bridge, not a claim of
local exactness or of the existence of compatible support sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable (k : Type u) [Field k]
  {T Y V : SmoothSite (Spec (.of k))}

local instance (X : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance (X : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

section FiniteImage

variable (D : Scheme.{u}) [IsIntegral D] [IsNoetherian D]
  (m : D ⟶ pullback T.hom V.hom) [IsFinite m]
  (hm : Set.range (m ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  [IsFinite (m ≫ pullback.fst T.hom V.hom)]

/-- The degree-weighted actual finite image, as a finite correspondence. -/
def weightedSupportImage : FiniteCorrespondence T.hom V.hom :=
  (m.residueDegree (genericPoint D) : ℤ) •
    (supportLiftImageGenerator k D m hm).cycle

set_option backward.isDefEq.respectTransparency false in
/-- The weighted image has exactly the full finite pushforward cycle. -/
theorem toIntegralCycle_weightedSupportImage :
    FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
      (weightedSupportImage k (T := T) (V := V) D m hm) =
      IntegralCycle.finitePushforward m (fundamentalCycle D) := by
  have h := supportLiftImageGenerator_graph k D m hm (𝟙 V) m rfl (by simp)
  change FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
    (FiniteCorrespondence.incidenceTorPairing k (X := T) (Y := V) (Z := V)
      (weightedSupportImage k (T := T) (V := V) D m hm)
      (componentIdentityCycle V.hom)) = _ at h
  rw [FiniteCorrespondence.incidenceTorPairing_componentIdentity_right] at h
  exact h


end FiniteImage

section Pairing

variable (D : Scheme.{u}) [IsIntegral D] [IsNoetherian D]
  (m₁ m₂ : D ⟶ pullback T.hom V.hom) [IsFinite m₁] [IsFinite m₂]
  (hm₁ : Set.range (m₁ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  (hm₂ : Set.range (m₂ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
  [IsFinite (m₂ ≫ pullback.fst T.hom V.hom)]
  (q : V ⟶ Y) [Etale q.left]
  (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
  (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
    m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

include hs ht

set_option backward.isDefEq.respectTransparency false in
/-- Pairing the two actual target maps gives a Čech correspondence whose graph
projections are their degree-weighted finite images. No target map is assumed
finite, and no support is assumed flat or geometrically reduced. -/
theorem exists_cech_pairing_of_common_support_with_point_lift :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        weightedSupportImage k D m₁ hm₁ ∧
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) =
        weightedSupportImage k D m₂ hm₂ ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, ∃ d : D,
        (m₁ ≫ pullback.fst T.hom V.hom) d = B.projection z ∧
        (m₁ ≫ pullback.snd T.hom V.hom) d =
          (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
        (m₂ ≫ pullback.snd T.hom V.hom) d =
          (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) := by
  let P := SmoothSite.etalePullback q q
  let a : D ⟶ P.left := pullback.lift
    (m₁ ≫ pullback.snd T.hom V.hom) (m₂ ≫ pullback.snd T.hom V.hom)
    (by simpa only [Category.assoc] using ht)
  have ha₁ : a ≫ (SmoothSite.etalePullbackFst q q).left =
      m₁ ≫ pullback.snd T.hom V.hom := pullback.lift_fst _ _ _
  have ha₂ : a ≫ (SmoothSite.etalePullbackSnd q q).left =
      m₂ ≫ pullback.snd T.hom V.hom := pullback.lift_snd _ _ _
  have hb : (m₁ ≫ pullback.fst T.hom V.hom) ≫ T.hom = a ≫ P.hom := by
    change _ = a ≫ (pullback.snd q.left q.left ≫ V.hom)
    rw [← Category.assoc, show a ≫ pullback.snd q.left q.left =
      m₂ ≫ pullback.snd T.hom V.hom from ha₂, hs]
    simp only [Category.assoc, pullback.condition]
  let m : D ⟶ pullback T.hom P.hom :=
    pullback.lift (m₁ ≫ pullback.fst T.hom V.hom) a hb
  have hm : m ≫ pullback.fst T.hom P.hom = m₁ ≫ pullback.fst T.hom V.hom :=
    pullback.lift_fst _ _ _
  have hmt : m ≫ pullback.snd T.hom P.hom = a := pullback.lift_snd _ _ _
  have : IsFinite (m ≫ pullback.fst T.hom P.hom) := by rw [hm]; infer_instance
  have : IsFinite m := IsFinite.of_comp m (pullback.fst T.hom P.hom)
  have hmr : Set.range (m ≫ pullback.fst T.hom P.hom) ∈
      irreducibleComponents T.left := by rw [hm]; exact hm₁
  refine ⟨weightedSupportImage k (T := T) (V := P) D m hmr, ?_, ?_, ?_⟩
  · apply FiniteCorrespondence.toIntegralCycle_injective
    rw [toIntegralCycle_weightedSupportImage]
    exact supportLiftImageGenerator_graph k D m hmr
      (SmoothSite.etalePullbackFst q q) m₁ hm.symm (by
        rw [← Category.assoc, hmt, ha₁])
  · apply FiniteCorrespondence.toIntegralCycle_injective
    rw [toIntegralCycle_weightedSupportImage]
    exact supportLiftImageGenerator_graph k D m hmr
      (SmoothSite.etalePullbackSnd q q) m₂ (hs.symm.trans hm.symm) (by
        rw [← Category.assoc, hmt, ha₂])
  · intro B hB z
    have hB' : B = supportLiftImageGenerator k D m hmr := by
      change B ∈ (((m.residueDegree (genericPoint D) : ℤ) •
        (supportLiftImageGenerator k D m hmr).cycle)).support at hB
      simpa only [cycle, Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0),
        Finset.mem_singleton] using Finsupp.support_smul hB
    subst B
    let B := supportLiftImageGenerator k D m hmr
    obtain ⟨d, hd⟩ := surjective_toImage m z
    have hi₁ : m.toImage ≫ B.projection = m₁ ≫ pullback.fst T.hom V.hom := by
      change m.toImage ≫ m.imageι ≫ _ = _
      rw [Scheme.Hom.toImage_imageι_assoc]
      exact hm
    have hi₂ : m.toImage ≫ B.targetProjection = a := by
      change m.toImage ≫ m.imageι ≫ _ = _
      rw [Scheme.Hom.toImage_imageι_assoc]
      exact hmt
    have ht₁ : m.toImage ≫ B.targetProjection ≫ (SmoothSite.etalePullbackFst q q).left =
        m₁ ≫ pullback.snd T.hom V.hom := by rw [← Category.assoc, hi₂, ha₁]
    have ht₂ : m.toImage ≫ B.targetProjection ≫ (SmoothSite.etalePullbackSnd q q).left =
        m₂ ≫ pullback.snd T.hom V.hom := by rw [← Category.assoc, hi₂, ha₂]
    refine ⟨d, ?_, ?_, ?_⟩
    · have h := congrArg (fun f : D ⟶ T.left ↦ f d) hi₁
      change B.projection (m.toImage d) = (m₁ ≫ pullback.fst T.hom V.hom) d at h
      rw [hd] at h
      exact h.symm
    · have h := congrArg (fun f : D ⟶ V.left ↦ f d) ht₁
      change (SmoothSite.etalePullbackFst q q).left (B.targetProjection (m.toImage d)) =
        (m₁ ≫ pullback.snd T.hom V.hom) d at h
      rw [hd] at h
      exact h.symm
    · have h := congrArg (fun f : D ⟶ V.left ↦ f d) ht₂
      change (SmoothSite.etalePullbackSnd q q).left (B.targetProjection (m.toImage d)) =
        (m₂ ≫ pullback.snd T.hom V.hom) d at h
      rw [hd] at h
      exact h.symm

/-- The original weighted projection endpoint, from the same constructed
pairing with its actual image-point lifts. -/
theorem exists_cech_pairing_of_common_support :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        weightedSupportImage k D m₁ hm₁ ∧
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) =
        weightedSupportImage k D m₂ hm₂ := by
  obtain ⟨β, h₁, h₂, _⟩ :=
    exists_cech_pairing_of_common_support_with_point_lift k D m₁ m₂ hm₁ hm₂ q hs ht
  exact ⟨β, h₁, h₂⟩

/-- Arbitrary signed multiplicities on the original support survive the Čech
boundary identity, rather than being replaced by effective multiplicity one. -/
theorem exists_cech_boundary_of_common_support (n : ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) =
      n • (weightedSupportImage k D m₁ hm₁ - weightedSupportImage k D m₂ hm₂) := by
  obtain ⟨β, h₁, h₂⟩ :=
    exists_cech_pairing_of_common_support k D m₁ m₂ hm₁ hm₂ q hs ht
  refine ⟨n • β, ?_⟩
  rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp, h₁, h₂, smul_sub]

end Pairing

end Motivic.FiniteCorrespondenceGenerator

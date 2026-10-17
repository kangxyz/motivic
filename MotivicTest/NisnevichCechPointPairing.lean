/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechSupportPairing
public import Lean.Util.CollectAxioms

/-! # Actual support-point witnesses for signed Čech pairings -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FiniteCorrespondenceGenerator

universe u

variable (k : Type u) [Field k] {T Y V : SmoothSite (Spec (.of k))}
  (D : Scheme.{u}) [IsIntegral D] [IsNoetherian D]
  (m₁ m₂ : D ⟶ pullback T.hom V.hom) [IsFinite m₁] [IsFinite m₂]
  (hm₁ : Set.range (m₁ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  (hm₂ : Set.range (m₂ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
  [IsFinite (m₂ ≫ pullback.fst T.hom V.hom)]
  (q : V ⟶ Y) [Etale q.left]
  (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
  (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
    m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

/-- Negative, zero, and positive multiplicities keep the original support
preimages, simultaneously with the literal signed boundary identity. -/
example (n : ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) =
      n • (weightedSupportImage k D m₁ hm₁ - weightedSupportImage k D m₂ hm₂) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, ∃ d : D,
        (m₁ ≫ pullback.fst T.hom V.hom) d = B.projection z ∧
        (m₁ ≫ pullback.snd T.hom V.hom) d =
          (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
        (m₂ ≫ pullback.snd T.hom V.hom) d =
          (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) := by
  obtain ⟨β, h₁, h₂, hpoints⟩ :=
    exists_cech_pairing_of_common_support_with_point_lift k D m₁ m₂ hm₁ hm₂ q hs ht
  refine ⟨n • β, ?_, ?_⟩
  · rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp, h₁, h₂, smul_sub]
  · intro B hB
    exact hpoints B (Finsupp.support_smul hB)

/-- Both selected fiber values are controlled by an actual preimage in D,
without inferring support information from the weighted graph equations. -/
example (x : T.left) (v₁ v₂ : V.left)
    (h₁ : ∀ d : D, (m₁ ≫ pullback.fst T.hom V.hom) d = x →
      (m₁ ≫ pullback.snd T.hom V.hom) d = v₁)
    (h₂ : ∀ d : D, (m₁ ≫ pullback.fst T.hom V.hom) d = x →
      (m₂ ≫ pullback.snd T.hom V.hom) d = v₂) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        weightedSupportImage k D m₁ hm₁ ∧
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) =
        weightedSupportImage k D m₂ hm₂ ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, B.projection z = x →
        (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) = v₁ ∧
        (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) = v₂ := by
  obtain ⟨β, hβ₁, hβ₂, hpoints⟩ :=
    exists_cech_pairing_of_common_support_with_point_lift k D m₁ m₂ hm₁ hm₂ q hs ht
  refine ⟨β, hβ₁, hβ₂, ?_⟩
  intro B hB z hz
  obtain ⟨d, hd, hd₁, hd₂⟩ := hpoints B hB z
  exact ⟨hd₁.symm.trans (h₁ d (hd.trans hz)), hd₂.symm.trans (h₂ d (hd.trans hz))⟩

open Lean in
run_cmd do
  for dependency in ← collectAxioms ``exists_cech_pairing_of_common_support_with_point_lift do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "Čech support-point lifting depends on unsupported assumption {dependency}"
  logInfo "Signed Čech pairing retains simultaneous actual source and target point preimages."

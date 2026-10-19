/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.SupportPairing
public import Lean.Util.CollectAxioms

/-!
# Actual support and signed Čech pairing consumers

The first projection recovers an original integral generator with coefficient
one. The second retains its actual finite-image degree. The signed consumer
allows any integer, including negative coefficients and zero.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (closedFundamentalCycle_of_isIntegral fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (IntegralCycle closedFundamentalCycle
  isNoetherian_of_finiteType)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FiniteCorrespondenceGenerator

universe u

namespace MotivicTest.NisnevichCechSupportPairing

variable {k : Type u} [Field k] {T Y V : SmoothSite (Spec (.of k))}
  (q : V ⟶ Y) [Etale q.left]

local instance (X : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance (A : FiniteCorrespondenceGenerator T.hom V.hom) :
    IsFinite (A.inclusion ≫ pullback.fst T.hom V.hom) :=
  inferInstanceAs (IsFinite A.projection)

local instance (A : FiniteCorrespondenceGenerator T.hom V.hom) : IsNoetherian A.scheme :=
  isNoetherian_of_finiteType A.projection

example (A : FiniteCorrespondenceGenerator T.hom V.hom)
    (m : A.scheme ⟶ pullback T.hom V.hom) [IsFinite m]
    (hs : m ≫ pullback.fst T.hom V.hom = A.projection)
    (ht : m ≫ pullback.snd T.hom V.hom ≫ q.left = A.targetProjection ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) = A.cycle ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
      IntegralCycle.finitePushforward m (fundamentalCycle A.scheme) := by
  have : IsFinite (m ≫ pullback.fst T.hom V.hom) := by rw [hs]; infer_instance
  have hm : Set.range (m ≫ pullback.fst T.hom V.hom) ∈
      irreducibleComponents T.left := by rw [hs]; exact A.range_projection_mem
  have : IsNoetherian (pullback T.hom V.hom) :=
    isNoetherian_of_finiteType (pullback.fst T.hom V.hom)
  have hA : weightedSupportImage k (T := T) (V := V) A.scheme
      A.inclusion A.range_projection_mem = A.cycle := by
    apply FiniteCorrespondence.toIntegralCycle_injective
    rw [toIntegralCycle_weightedSupportImage]
    change closedFundamentalCycle A.val = FiniteCorrespondence.toIntegralCycle A.cycle
    rw [FiniteCorrespondenceGenerator.cycle, FiniteCorrespondence.toIntegralCycle_single,
      closedFundamentalCycle_of_isIntegral]
    rfl
  obtain ⟨β, h₁, h₂⟩ := exists_cech_pairing_of_common_support k A.scheme A.inclusion m
    A.range_projection_mem hm q hs.symm ht.symm
  refine ⟨β, h₁.trans hA, ?_⟩
  rw [h₂, toIntegralCycle_weightedSupportImage]

example (D : Scheme.{u}) [IsIntegral D] [IsNoetherian D]
    (m₁ m₂ : D ⟶ pullback T.hom V.hom) [IsFinite m₁] [IsFinite m₂]
    (hm₁ : Set.range (m₁ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
    (hm₂ : Set.range (m₂ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
    [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
    [IsFinite (m₂ ≫ pullback.fst T.hom V.hom)]
    (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
    (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
      m₂ ≫ pullback.snd T.hom V.hom ≫ q.left) (n : ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) =
      n • (weightedSupportImage k D m₁ hm₁ - weightedSupportImage k D m₂ hm₂) :=
  exists_cech_boundary_of_common_support k D m₁ m₂ hm₁ hm₂ q hs ht n

open Lean in
run_cmd do
  for name in #[``exists_cech_pairing_of_common_support,
      ``exists_cech_boundary_of_common_support] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichCechSupportPairing

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechIncidencePairing
public import Lean.Util.CollectAxioms

/-! # Original signed generic and incidence-Tor support-point witnesses -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FiniteCorrespondenceGenerator

universe u

variable (k : Type u) [Field k] {T X Y V : SmoothSite (Spec (.of k))}

example (W : Scheme.{u}) [IsNoetherian W]
    (m₁ m₂ : W ⟶ pullback T.hom V.hom) [IsFinite m₁] [IsFinite m₂]
    [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
    [IsFinite (m₂ ≫ pullback.fst T.hom V.hom)]
    (hm₁ : ∀ x : genericPoints W,
      Set.range (((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ m₁) ≫
        pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
    (q : V ⟶ Y) [Etale q.left]
    (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
    (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
      m₂ ≫ pullback.snd T.hom V.hom ≫ q.left) (c : genericPoints W → ℤ) :
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
          (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) :=
  exists_cech_pairing_of_generic_coefficients_with_point_lift k W m₁ m₂ hm₁ q hs ht c

/-- The witness is on the original incidence scheme. In particular its first
target is the actual original generator's target map at incidenceSnd w. -/
example (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom)
    (m : G.incidence A ⟶ pullback T.hom V.hom) [IsFinite m]
    (q : V ⟶ Y) [Etale q.left]
    (hs : G.incidenceMap A ≫ pullback.fst T.hom V.hom = m ≫ pullback.fst T.hom V.hom)
    (ht : G.incidenceMap A ≫ pullback.snd T.hom V.hom ≫ q.left =
      m ≫ pullback.snd T.hom V.hom ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        G.incidenceTorCorrespondence k A ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward m (IntegralCycle.ofGenericCoefficients (G.incidence A)
          (G.incidenceTorCoefficient (S := Spec (.of k)) A)) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, ∃ w : G.incidence A,
        G.incidenceSource A w = B.projection z ∧
        A.targetProjection (G.incidenceSnd A w) =
          (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
        (m ≫ pullback.snd T.hom V.hom) w =
          (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) :=
  exists_cech_pairing_of_incidenceTor_with_point_lift k G A m q hs ht

open Lean in
run_cmd do
  for name in #[``exists_cech_pairing_of_generic_coefficients_with_point_lift,
      ``exists_cech_pairing_of_incidenceTor_with_point_lift] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original signed coefficient and incidence-Tor pairings retain actual support points."

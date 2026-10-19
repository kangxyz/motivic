/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TransverseCycle

/-!
# Consumers of actual transverse incidence coefficients

Explicit regular generators of the literal triple-stalk kernels and weak
regularity on actual support-product stalks identify the genuine diagonal-Tor
coefficients with full generic lengths. The resulting correspondence and its
signed bilinear basis value recover ordinary fundamental pushforward under
these hypotheses, including possible nilpotents and colliding image supports.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleInclusion)
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite genericMultiplicity)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence Motivic

universe u

namespace MotivicTest.TransverseIncidenceCycle

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (s : ∀ x : genericPoints (A.incidence B), List (A.incidenceAmbientStalk B x.val))
  (hker : ∀ x, RingHom.ker
    ((correspondenceTripleInclusion X.hom Y.hom Z.hom).stalkMap
      (A.incidenceInclusion B x.val)).hom = Ideal.ofList (s x))
  (hs : ∀ x, IsRegular (A.incidenceAmbientStalk B x.val) (s x))
  (hT : ∀ x, IsWeaklyRegular (A.incidenceSupportStalkModule B x.val) (s x))

include hker hs hT in
/-- Actual coefficient regularity proves the desired multiplicity, rather than assuming it. -/
theorem actual_transverse_coefficient (x : genericPoints (A.incidence B)) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) :=
  A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x
    (s x) (hker x) (hs x) (hT x)

include hker hs hT in
/-- The signed basis value of the actual candidate pairing becomes the ordinary
fundamental cycle. -/
theorem signed_transverse_basis (m n : ℤ) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (Finsupp.single A m) (Finsupp.single B n) =
      (m * n) • A.incidenceFundamentalCorrespondence k B := by
  rw [FiniteCorrespondence.incidenceTorPairing_single,
    A.incidenceTorCorrespondence_eq_fundamental_of_weaklyRegular k B s hker hs hT]

include hker hs hT in
/-- The full incidence fundamental cycle appears after faithful forgetting and
actual pushforward. -/
theorem actual_transverse_pushforward :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (A.incidenceTorCorrespondence k B) =
      IntegralCycle.finitePushforward (A.incidenceMap B) (fundamentalCycle (A.incidence B)) :=
  A.toIntegralCycle_incidenceTorCorrespondence_of_weaklyRegular k B s hker hs hT

end MotivicTest.TransverseIncidenceCycle

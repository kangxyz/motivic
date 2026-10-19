/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TorCycle
public import Motivic.Aglib.AlgebraicGeometry.Intersection.TransverseTor

/-!
# Incidence cycle comparison under actual coefficient regularity

A regular list generating the literal triple-inclusion stalk kernel need not
be weakly regular on the actual support-product stalk. When that additional
algebraic condition is proved at each genuine generic incidence point, the
actual four-factor diagonal-Tor coefficient is the full incidence generic
stalk length. Its finite-image correspondence is consequently the ordinary
incidence fundamental correspondence, with the same residue-field degrees
and collisions of component images.

All coefficient regularity hypotheses are explicit actual module statements.
They are not inferred from ambient smoothness. This comparison does not
assert the traditional triple-product Tor change-of-ambient theorem or the
unit and associativity laws of a correspondence category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Weak regularity on the actual support-product stalk removes the higher
Tor corrections and gives the full, possibly nonreduced incidence multiplicity. -/
theorem incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular
    (x : genericPoints (A.incidence B)) (s : List (A.incidenceAmbientStalk B x.val))
    (hker : RingHom.ker
      ((correspondenceTripleInclusion X.hom Y.hom Z.hom).stalkMap
        (A.incidenceInclusion B x.val)).hom = Ideal.ofList s)
    (hs : IsRegular (A.incidenceAmbientStalk B x.val) s)
    (hT : IsWeaklyRegular (A.incidenceSupportStalkModule B x.val) s) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) := by
  have := isLocallyNoetherian_correspondenceIntersectionAmbient
    (S := Spec (.of k)) X.hom Y.hom Z.hom
  exact Intersection.torEulerCoefficient_eq_genericMultiplicity_of_coefficient_regular
    (A.incidenceInclusion B) (A.incidenceToSupportProduct B)
    (correspondenceTripleInclusion X.hom Y.hom Z.hom) (A.supportProductInclusion B)
    (A.incidence_ambient_isPullback B) x.val x.property ⟨s, hs, hker⟩ s hker hs hT

variable
  (s : ∀ x : genericPoints (A.incidence B), List (A.incidenceAmbientStalk B x.val))
  (hker : ∀ x, RingHom.ker
    ((correspondenceTripleInclusion X.hom Y.hom Z.hom).stalkMap
      (A.incidenceInclusion B x.val)).hom = Ideal.ofList (s x))
  (hs : ∀ x, IsRegular (A.incidenceAmbientStalk B x.val) (s x))
  (hT : ∀ x, IsWeaklyRegular (A.incidenceSupportStalkModule B x.val) (s x))

include hker hs hT in
/-- Actual coefficient regularity at every component identifies the diagonal-Tor
correspondence with the genuine ordinary incidence fundamental correspondence. -/
theorem incidenceTorCorrespondence_eq_fundamental_of_weaklyRegular :
    A.incidenceTorCorrespondence k B = A.incidenceFundamentalCorrespondence k B := by
  unfold incidenceTorCorrespondence incidenceFundamentalCorrespondence
  apply congrArg (A.incidenceCycleAssembly k B)
  funext x
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x
    (s x) (hker x) (hs x) (hT x)

include hker hs hT in
/-- Under the stated actual module regularity, the forgotten diagonal-Tor cycle is
exactly finite pushforward of the full ordinary incidence fundamental cycle. -/
theorem toIntegralCycle_incidenceTorCorrespondence_of_weaklyRegular :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (A.incidenceTorCorrespondence k B) =
      IntegralCycle.finitePushforward (A.incidenceMap B) (fundamentalCycle (A.incidence B)) := by
  rw [A.incidenceTorCorrespondence_eq_fundamental_of_weaklyRegular k B s hker hs hT]
  exact A.toIntegralCycle_incidenceFundamentalCorrespondence k B

end Motivic.FiniteCorrespondenceGenerator

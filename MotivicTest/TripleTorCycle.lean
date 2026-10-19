/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.TorCycle

/-!
# Actual canonical total-cycle consumers on the smooth site

The finite all-degree Tor support, regular-list independence and finite-image
cycle are all constructed on the actual schemes, rather than provided as
comparison or finite-support hypotheses.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.HomologicalComplex.ModuleLengthEuler

universe u

namespace Motivic.MotivicTest.TripleTorCycle
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- All canonical total Tor degrees are finite length with finite degree support. -/
theorem actualTotalFiniteSupport (w : genericPoints (F.tripleIncidence G H)) :
    FiniteLengthSupport (F.tripleIncidenceTor G H w.val) :=
  F.tripleIncidenceTor_finiteLengthSupport (S := Spec (.of k)) G H w.val w.property

/-- The canonical coefficient is computed by a genuinely constructed finite
Koszul resolution of the combined diagonal, retaining every higher correction. -/
theorem actualCanonicalCoefficient (w : genericPoints (F.tripleIncidence G H)) :
    ∃ (r : List (F.tripleIncidenceAmbientStalk G H w.val))
      (_hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w.val) r)
      (hker : RingHom.ker
        ((correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
          correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).stalkMap
            (F.tripleIncidenceFourfoldInclusion G H w.val)).hom = Ideal.ofList r),
      F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w =
        chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
            (F.tripleIncidenceSupportStalkModule G H w.val) r)
          (F.tripleIncidenceKoszul_finiteHomology (S := Spec (.of k)) G H w r hker) := by
  obtain ⟨r, hr, hker⟩ := exists_regular_kernel_correspondenceFourfoldDiagonal
    X.hom Y.hom Z.hom W.hom (F.tripleIncidenceFourfoldInclusion G H w.val)
  exact ⟨r, hr, hker,
    F.tripleIncidenceTorCoefficient_eq_chainEuler (S := Spec (.of k)) G H w r hr hker⟩

/-- Forgetting the actual finite correspondence gives precisely the canonical
full triple-incidence cycle pushed by the genuine finite output map. -/
theorem actualCanonicalCycle :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
      (F.tripleTorCorrespondence k G H) =
      IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
        (F.tripleIncidenceTorCycle k G H) :=
  F.toIntegralCycle_tripleTorCorrespondence k G H

/-- Canonical total Tor coefficients survive the actual generic-point cycle representation. -/
theorem actualGenericCoefficient (w : genericPoints (F.tripleIncidence G H)) :
    IntegralCycle.toPoints (F.tripleIncidenceTorCycle k G H) w.val =
      F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w := by
  rw [FiniteCorrespondenceGenerator.tripleIncidenceTorCycle,
    IntegralCycle.toPoints_ofGenericCoefficients_apply, dite_eq_left w.property]

end Motivic.MotivicTest.TripleTorCycle

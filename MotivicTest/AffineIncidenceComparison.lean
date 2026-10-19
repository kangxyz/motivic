/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.AffineComparison

/-! # Actual affine-generator consumers of local Tor length and Euler comparison -/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Products.MiddleDiagonal

universe u

namespace Motivic.MotivicTest.AffineIncidenceComparison

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (F : FiniteCorrespondenceGenerator (structureMap k A) (structureMap k B))
  (G : FiniteCorrespondenceGenerator (structureMap k B) (structureMap k C))

/-- The original generator incidence modules have the actual pulled-support local lengths. -/
theorem actualDegreeLength (w : F.incidence G) (n : ℕ) :
    Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
      Module.length (ambientStalk (rightGeneratorPulledInclusion k A B C G)
        (incidenceToRightPulled k A B C F G w)) (pulledIncidenceStalkTor k A B C F G w n) :=
  incidenceTor_length_eq_pulled k A B C F G w n

/-- Finite-length evidence for actual incidence Tor transfers to the original pulled schemes. -/
theorem actualFiniteSupport (w : F.incidence G)
    (h : _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (F.incidenceTor G w)) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (pulledIncidenceStalkTor k A B C
        F G w) :=
  (incidenceTor_finiteLengthSupport_iff_pulled k A B C F G w).mp h

/-- Every higher correction is retained in the actual alternating local coefficient. -/
theorem actualAlternatingCoefficient (w : F.incidence G)
    (h : _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (F.incidenceTor G w)) :
    _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum (F.incidenceTor G w) (fun n ↦ (-1 :
        ℤ) ^ n) h =
      _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum (pulledIncidenceStalkTor k A B C F
          G w)
        (fun n ↦ (-1 : ℤ) ^ n) (actualFiniteSupport k A B C F G w h) :=
  incidenceTor_signedLengthSum_eq_pulled k A B C F G w _ h

section Generic

variable [LocallyOfFiniteType (structureMap k A)] [LocallyOfFiniteType (structureMap k C)]
  [Flat (structureMap k A)] [Smooth (structureMap k B)] [IsSeparated (structureMap k B)]
  [Flat (structureMap k C)]

/-- The existing smooth generic-incidence theorem supplies genuine source evidence. -/
theorem genericPulledFiniteSupport (w : genericPoints (F.incidence G)) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport (pulledIncidenceStalkTor k A B C
        F G w.val) :=
  actualFiniteSupport k A B C F G w.val
    (F.incidenceTor_finiteLengthSupport G w.val w.property)

/-- The existing actual generic-incidence coefficient equals the pulled-support Tor Euler sum. -/
theorem genericCoefficient (w : genericPoints (F.incidence G)) :
    F.incidenceTorCoefficient G w =
      _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum (pulledIncidenceStalkTor k A B C F
          G w.val)
        (fun n ↦ (-1 : ℤ) ^ n) (genericPulledFiniteSupport k A B C F G w) :=
  incidenceTor_signedLengthSum_eq_pulled k A B C F G w.val _
    (F.incidenceTor_finiteLengthSupport G w.val w.property)

end Generic

end Motivic.MotivicTest.AffineIncidenceComparison

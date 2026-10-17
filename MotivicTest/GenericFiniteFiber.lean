/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericFiniteFiber
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTor

/-! # Actual incidence consumers of generic-fiber reflection and Artinianness -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic Motivic.LengthEuler

universe u

namespace Motivic.MotivicTest.GenericFiniteFiber

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- An actual incidence point over a generic source point is a generic incidence point. -/
theorem actualIncidenceGeneric (w : A.incidence B)
    (hw : A.incidenceSource B w ∈ genericPoints X) :
    w ∈ genericPoints (A.incidence B) :=
  mem_genericPoints_of_image_generic (A.incidenceSource B) w hw

/-- The generic-fiber equivalence keeps the literal incidence point unchanged. -/
theorem actualFiberPoint (y : genericPoints X)
    (w : {w : A.incidence B // A.incidenceSource B w = y.1}) :
    ((genericFiberEquiv (A.incidenceSource B) y w).1 : A.incidence B) = w.1 :=
  genericFiberEquiv_apply_val _ _ _

/-- The genuine incidence local ring is Artinian; the source need not be reduced. -/
theorem actualIncidenceArtinian [IsLocallyNoetherian X] (w : A.incidence B)
    (hw : A.incidenceSource B w ∈ genericPoints X) :
    IsArtinianRing ((A.incidence B).presheaf.stalk w) := by
  have := A.isLocallyNoetherian_incidence B
  exact isArtinianRing_stalk_of_image_generic (A.incidenceSource B) w hw

/-- Source-generic fibers have actual all-degree categorical Tor finiteness,
using the smooth middle diagonal rather than an assumed coefficient family. -/
theorem actualIncidenceTorFinite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType h] [Flat f] [Smooth g]
    [IsSeparated g] [Flat h] (w : A.incidence B)
    (hw : A.incidenceSource B w ∈ genericPoints X) :
    FiniteLengthSupport (A.incidenceTor B w) :=
  A.incidenceTor_finiteLengthSupport B w (actualIncidenceGeneric A B w hw)

end Motivic.MotivicTest.GenericFiniteFiber

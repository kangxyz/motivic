/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.GenericTor
public import Motivic.AlgebraicGeometry.Diagonal.FlatBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceLocalLength

/-!
# Actual generic-incidence Tor coefficients

The product of the two correspondence support schemes is used as the actual
coefficient scheme in the four-factor ambient product. The source module is
the actual triple-product stalk. Their Cartesian intersection is the actual
incidence scheme, with its full scheme structure.

Over a locally Noetherian base, locally finite-type flat outer maps and a
smooth separated middle map supply Noetherian ambient stalks and the proved
regular equations for the literal triple-inclusion kernel. Thus every actual
generic incidence point has finite-length categorical Tor in finitely many
degrees. Its canonical integer coefficient retains every higher correction.
This file does not assert associativity or identify this coefficient with an
ordinary generic local length.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.LengthEuler

universe u

namespace Motivic

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The actual four-factor ambient intersection scheme is locally Noetherian over
any locally Noetherian base when all three structure maps are locally finite type. -/
theorem isLocallyNoetherian_correspondenceIntersectionAmbient [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h] :
    IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  have : IsLocallyNoetherian (pullback g h) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g h)
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))

namespace FiniteCorrespondenceGenerator

variable {f g h} (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual four-factor ambient stalk at an incidence point. -/
abbrev incidenceAmbientStalk (w : A.incidence B) :=
  Intersection.ambientStalk (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)

/-- The actual support-product stalk, with scalars through its actual closed immersion. -/
abbrev incidenceSupportStalkModule (w : A.incidence B) : ModuleCat (A.incidenceAmbientStalk B w) :=
  Intersection.coefficientStalkModule
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
    (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
    (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)

/-- The actual triple-product stalk, with scalars through the actual triple inclusion. -/
abbrev incidenceTripleStalkModule (w : A.incidence B) : ModuleCat (A.incidenceAmbientStalk B w) :=
  Intersection.sourceStalkModule
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)

/-- Genuine categorical Tor of the actual support-product and triple-product stalks. -/
def incidenceTor (w : A.incidence B) (n : ℕ) : ModuleCat (A.incidenceAmbientStalk B w) :=
  ((Tor (ModuleCat (A.incidenceAmbientStalk B w)) n).obj (A.incidenceSupportStalkModule B w)).obj
    (A.incidenceTripleStalkModule B w)

/-- The actual coefficient stalk is finite over the actual four-factor ambient stalk. -/
instance incidenceSupportStalkModule_finite (w : A.incidence B) :
    Module.Finite (A.incidenceAmbientStalk B w) (A.incidenceSupportStalkModule B w) :=
  inferInstanceAs (Module.Finite _ (Intersection.coefficientStalkModule _ _ _ _ _))

variable [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType h]
  [Flat f] [Smooth g] [IsSeparated g] [Flat h]

/-- Generic incidence yields finite lengths and degree support of actual categorical Tor,
using the genuine smooth flat-base-change theorem for the literal triple kernel. -/
theorem incidenceTor_finiteLengthSupport (w : A.incidence B)
    (hw : w ∈ genericPoints (A.incidence B)) : FiniteLengthSupport (A.incidenceTor B w) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := A.isLocallyNoetherian_incidence B
  have := isLocallyNoetherian_correspondenceIntersectionAmbient f g h
  exact Intersection.finiteLengthSupport_tor_of_regular_kernel
    (A.incidenceInclusion B) (A.incidenceToSupportProduct B)
    (correspondenceTripleInclusion f g h) (A.supportProductInclusion B)
    (A.incidence_ambient_isPullback B) w hw
    (exists_regular_kernel_correspondenceTripleInclusion f g h (A.incidenceInclusion B w))

/-- The actual generic-incidence Tor coefficient, with every higher correction retained. -/
def incidenceTorCoefficient (w : genericPoints (A.incidence B)) : ℤ :=
  signedLengthSum (A.incidenceTor B w.val) (fun n => (-1 : ℤ) ^ n)
    (A.incidenceTor_finiteLengthSupport B w.val w.property)

/-- Every actual generic-incidence Tor degree has finite ambient module length. -/
theorem incidenceTor_length_ne_top (w : genericPoints (A.incidence B)) (n : ℕ) :
    Module.length (A.incidenceAmbientStalk B w.val) (A.incidenceTor B w.val n) ≠ ⊤ :=
  (A.incidenceTor_finiteLengthSupport B w.val w.property).finite_length n

end FiniteCorrespondenceGenerator

end Motivic

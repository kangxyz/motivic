/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Ideal.GoingDown.Quotient

/-!
# Consumers of going down for actual quotient algebras

These consumers instantiate the quotient map explicitly and include the
unit ideal, whose quotient rings are zero rings. In particular, the result
does not require either quotient ring to be a domain.
-/

@[expose] public section

universe u v

namespace MotivicTest.GoingDownQuotient

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The theorem uses exactly the algebra induced by the quotient maps. -/
theorem explicit_quotient_algebra [Algebra.HasGoingDown R S] (I : Ideal R) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.le_comap_map : I ≤ (I.map (algebraMap R S)).comap (algebraMap R S))
    Algebra.HasGoingDown (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Algebra.HasGoingDown.quotient_map I

/-- The actual quotient algebra map commutes with the original algebra map. -/
theorem quotient_map_square (I : Ideal R) :
    (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap R S))).comp (algebraMap R S) :=
  Ideal.quotientMap_comp_mk Ideal.le_comap_map

/-- The theorem remains applicable when quotienting by the whole ring. -/
theorem unit_ideal_quotient [Algebra.HasGoingDown R S] :
    Algebra.HasGoingDown (R ⧸ (⊤ : Ideal R))
      (S ⧸ (⊤ : Ideal R).map (algebraMap R S)) :=
  Algebra.HasGoingDown.quotient_map ⊤

/-- Quotients of an arbitrary ring satisfy going down over themselves. -/
theorem self_quotient (I : Ideal R) :
    Algebra.HasGoingDown (R ⧸ I) (R ⧸ I.map (algebraMap R R)) :=
  Algebra.HasGoingDown.quotient_map I

end MotivicTest.GoingDownQuotient

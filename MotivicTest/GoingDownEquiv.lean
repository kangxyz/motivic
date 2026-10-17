/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Ideal.GoingDown.Equiv

/-!
# Consumers of going down under compatible equivalences

Reverse transport checks the orientation of the actual algebra-map square,
with four independent universes and arbitrary commutative rings. The
fixed-base test retains an actual algebra equivalence and also uses its
inverse. Neither test assumes domains or nontrivial rings.
-/

@[expose] public section

universe u v w x

namespace MotivicTest.GoingDownEquiv

/-- The same commuting square transports going down back through both inverses. -/
theorem reverse_transport
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra.HasGoingDown R' S']
    (e : R ≃+* R') (f : S ≃+* S')
    (h : f.toRingHom.comp (algebraMap R S) = (algebraMap R' S').comp e.toRingHom) :
    Algebra.HasGoingDown R S := by
  apply Algebra.HasGoingDown.of_equivalences e.symm f.symm
  ext r
  apply f.injective
  simpa using (congrArg (fun g : R →+* S' => g (e.symm r)) h).symm

/-- An actual algebra equivalence transports the property in the reverse direction. -/
theorem reverse_algEquiv
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.HasGoingDown R T] (e : S ≃ₐ[R] T) : Algebra.HasGoingDown R S :=
  Algebra.HasGoingDown.of_algEquiv e.symm

end MotivicTest.GoingDownEquiv

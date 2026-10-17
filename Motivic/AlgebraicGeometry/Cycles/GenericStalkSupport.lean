/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FundamentalStalk
public import Motivic.RingTheory.LocalLength.ArtinianQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ambient lengths at genuine generic support points

For a morphism surjective on stalks, the ambient stalk modulo its actual
stalk-map kernel is the source stalk. At a generic point of a locally
Noetherian source this quotient is Artinian. This gives finite ambient length
for a Noetherian module annihilated by the literal kernel; the ambient stalk
itself is not asserted Artinian. Closed immersions are an important instance.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace Motivic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f]

/-- The quotient by the actual ambient stalk-map kernel is the actual source stalk. -/
noncomputable def stalkQuotientKerEquiv (x : X) :
    (Y.presheaf.stalk (f x)) ⧸ RingHom.ker (f.stalkMap x).hom ≃+*
      X.presheaf.stalk x :=
  (f.stalkMap x).hom.quotientKerEquivOfSurjective (f.stalkMap_surjective x)

/-- At a genuine generic support point, the ambient kernel quotient is Artinian. -/
theorem stalk_quotient_ker_isArtinian [IsLocallyNoetherian X]
    (x : X) (hx : x ∈ genericPoints X) :
    IsArtinianRing ((Y.presheaf.stalk (f x)) ⧸ RingHom.ker (f.stalkMap x).hom) := by
  let := isArtinianRing_stalk_of_mem_genericPoints x hx
  exact (stalkQuotientKerEquiv f x).symm.isArtinianRing

/-- A Noetherian ambient module supported on the literal generic-stalk kernel
has finite ambient length, without Artinianness of the ambient ring. -/
theorem length_ne_top_of_generic_stalk_support [IsLocallyNoetherian X]
    (x : X) (hx : x ∈ genericPoints X) (M : Type v) [AddCommGroup M]
    [Module (Y.presheaf.stalk (f x)) M] [IsNoetherian (Y.presheaf.stalk (f x)) M]
    (hM : RingHom.ker (f.stalkMap x).hom ≤ Module.annihilator (Y.presheaf.stalk (f x)) M) :
    Module.length (Y.presheaf.stalk (f x)) M ≠ ⊤ := by
  let := stalk_quotient_ker_isArtinian f x hx
  exact LocalLength.length_ne_top_of_artinian_quotient M
    (RingHom.ker (f.stalkMap x).hom) hM

/-- Surjective stalk scalars preserve the literal module length. -/
theorem length_stalk_restrictScalars (x : X) :
    let := (f.stalkMap x).hom.toAlgebra
    Module.length (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  exact Module.length_eq_of_surjective (f.stalkMap_surjective x)

/-- Original generic multiplicities also equal lengths over the ambient local ring. -/
theorem genericMultiplicity_eq_ambient_length [IsLocallyNoetherian X]
    (x : genericPoints X) :
    let := (f.stalkMap x.val).hom.toAlgebra
    (genericMultiplicity x : ℕ∞) =
      Module.length (Y.presheaf.stalk (f x.val)) (X.presheaf.stalk x.val) := by
  let := (f.stalkMap x.val).hom.toAlgebra
  exact (genericMultiplicity_eq_length x).trans (length_stalk_restrictScalars f x.val).symm

end Motivic

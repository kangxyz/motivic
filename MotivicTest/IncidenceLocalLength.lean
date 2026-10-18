/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.IncidenceLocalLength
public import Motivic.AlgebraicGeometry.Cycles.FundamentalClosedSubscheme
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Generic-support local-length consumers

The first consumers use literal closed-subscheme local rings and original
fundamental multiplicities. The incidence consumer uses actual smooth objects
over an arbitrary field, deriving Noetherianity rather than assuming ambient
local rings Artinian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u v

namespace MotivicTest.IncidenceLocalLength

example {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (x : genericPoints I.subscheme) :
    IsArtinianRing ((X.presheaf.stalk (I.subschemeι x.val)) ⧸
      RingHom.ker (I.subschemeι.stalkMap x.val).hom) :=
  stalk_quotient_ker_isArtinian I.subschemeι x.val x.property

example {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (x : genericPoints I.subscheme) :
    letI := (I.subschemeι.stalkMap x.val).hom.toAlgebra
    (genericMultiplicity x : ℕ∞) =
      Module.length (X.presheaf.stalk (I.subschemeι x.val)) (I.subscheme.presheaf.stalk x.val) :=
  genericMultiplicity_eq_ambient_length I.subschemeι x

example {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (x : genericPoints I.subscheme) (M : Type v) [AddCommGroup M]
    [Module (X.presheaf.stalk (I.subschemeι x.val)) M]
    [Module.Finite (X.presheaf.stalk (I.subschemeι x.val)) M]
    (hM : RingHom.ker (I.subschemeι.stalkMap x.val).hom ≤
      Module.annihilator (X.presheaf.stalk (I.subschemeι x.val)) M) :
    Module.length (X.presheaf.stalk (I.subschemeι x.val)) M ≠ ⊤ :=
  length_ne_top_of_generic_stalk_support I.subschemeι x.val x.property M hM

example (K : Type u) [Field K] (X Y Z : SmoothSite (Spec (.of K)))
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
    (w : genericPoints (A.incidence B)) :
    IsArtinianRing
      (((correspondenceTripleProduct X.hom Y.hom Z.hom).presheaf.stalk
        ((A.incidenceInclusion B) w.val)) ⧸
        RingHom.ker ((A.incidenceInclusion B).stalkMap w.val).hom) := by
  have : IsLocallyNoetherian X.left := inferInstance
  exact FiniteCorrespondenceGenerator.incidence_stalk_quotient_isArtinian
    (X := X.left) A B w.val w.property

section IncidenceHomology

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyOfFiniteType f] [LocallyOfFiniteType h]
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
  (w : genericPoints (A.incidence B))

/-- Even zero equations have finite actual homology on a genuine generic incidence
support; no vanishing of the higher correction modules is assumed. -/
theorem zero_equations_generic_incidence_support :
    let R := (correspondenceTripleProduct f g h).presheaf.stalk ((A.incidenceInclusion B) w.val)
    let I := RingHom.ker ((A.incidenceInclusion B).stalkMap w.val).hom
    Module.KoszulPair.HasFiniteHomology (R ⧸ I) (0 : R) 0 := by
  dsimp only
  apply FiniteCorrespondenceGenerator.incidence_koszul_hasFiniteHomology
    A B w.val w.property _ 0 0
  rw [Ideal.span_insert_zero, Ideal.span_singleton_zero, bot_sup_eq,
    Ideal.annihilator_quotient]

end IncidenceHomology

end MotivicTest.IncidenceLocalLength

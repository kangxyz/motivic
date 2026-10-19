/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.AmbientIdeal

/-!
# Consumers of the actual diagonal-intersection ambient diagram

These examples use the literal support schemes, Cartesian squares, and ideal
sum. No hypothesis makes the incidence scheme integral, reduced, or flat.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Products (correspondenceIntersectionAmbient
  correspondenceMiddlePair correspondenceTripleInclusion correspondenceTripleMiddle
  correspondenceTripleProduct correspondenceTriple_isPullback ker_correspondenceTripleInclusion)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

example : correspondenceIntersectionAmbient f g h =
    pullback (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) := rfl

example : IsPullback (correspondenceTripleMiddle f g h)
    (correspondenceTripleInclusion f g h) (pullback.diagonal g)
    (correspondenceMiddlePair f g h) :=
  correspondenceTriple_isPullback f g h

/-- The actual ambient base change is flat solely from flatness of the outer factors. -/
theorem flatAmbientBaseChange [Flat f] [Flat h] :
    Flat (correspondenceMiddlePair f g h) := inferInstance

example [IsSeparated g] : IsClosedImmersion (correspondenceTripleInclusion f g h) :=
  inferInstance

example : A.supportProduct B = pullback (A.targetProjection ≫ g) (B.projection ≫ g) := rfl

example : IsClosedImmersion (A.supportProductInclusion B) := inferInstance

example : IsPullback (A.incidenceInclusion B) (A.incidenceToSupportProduct B)
    (correspondenceTripleInclusion f g h) (A.supportProductInclusion B) :=
  A.incidence_ambient_isPullback B

example [IsSeparated g] : IsClosedImmersion (A.incidenceAmbientInclusion B) := inferInstance

example [IsSeparated g] : (A.incidenceAmbientInclusion B).ker =
    (correspondenceTripleInclusion f g h).ker ⊔ (A.supportProductInclusion B).ker :=
  A.ker_incidenceAmbientInclusion B

example [IsSeparated g] : Nonempty (A.incidence B ≅
    ((correspondenceTripleInclusion f g h).ker ⊔ (A.supportProductInclusion B).ker).subscheme) :=
  ⟨A.incidenceAmbientIntersectionIso B⟩

/-- A downstream user can lift a compatible pair of maps into the literal incidence scheme. -/
noncomputable def liftToActualIncidence {Q : Scheme.{u}}
    (d : Q ⟶ correspondenceTripleProduct f g h) (t : Q ⟶ A.supportProduct B)
    (e : d ≫ correspondenceTripleInclusion f g h = t ≫ A.supportProductInclusion B) :
    Q ⟶ A.incidence B :=
  (A.incidence_ambient_isPullback B).lift d t e

example {Q : Scheme.{u}}
    (d : Q ⟶ correspondenceTripleProduct f g h) (t : Q ⟶ A.supportProduct B)
    (e : d ≫ correspondenceTripleInclusion f g h = t ≫ A.supportProductInclusion B) :
    liftToActualIncidence A B d t e ≫ A.incidenceInclusion B = d :=
  (A.incidence_ambient_isPullback B).lift_fst d t e

example [IsSeparated g] : (correspondenceTripleInclusion f g h).ker =
    (pullback.diagonal g).ker.comap (correspondenceMiddlePair f g h) :=
  ker_correspondenceTripleInclusion f g h

example [IsSeparated g] : (A.incidenceToSupportProduct B).ker =
    (correspondenceTripleInclusion f g h).ker.comap (A.supportProductInclusion B) :=
  A.ker_incidenceToSupportProduct B

example [IsSeparated g] : (A.incidenceAmbientInclusion B).ker =
    (pullback.diagonal g).ker.comap (correspondenceMiddlePair f g h) ⊔
      (A.supportProductInclusion B).ker :=
  A.ker_incidenceAmbientInclusion_eq_diagonal_sup B

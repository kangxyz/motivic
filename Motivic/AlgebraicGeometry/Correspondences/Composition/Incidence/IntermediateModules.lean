/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.ScalarRestriction.Surjective

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Tor

/-!
# Actual intermediate homology modules over the incidence stalk

The kernel of the actual ambient-to-incidence stalk map annihilates every Tor
degree, and every coefficient-Koszul homology degree for literal diagonal
kernel equations. These actual homology modules therefore carry constructed
incidence-stalk actions. Restriction along the literal stalk map recovers the
original ambient module by the identity on elements. No descent of the terms
or differentials of the original ambient complex is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u


namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)

/-- The literal ambient-to-incidence stalk map, retaining the full incidence scheme. -/
abbrev incidenceAmbientStalkMap (w : F.incidence G) :
    F.incidenceAmbientStalk G w →+* (F.incidence G).presheaf.stalk w :=
  ((F.incidenceInclusion G ≫ correspondenceTripleInclusion f g h).stalkMap w).hom

/-- The actual incidence inclusion is closed, so its literal stalk map is surjective. -/
theorem incidenceAmbientStalkMap_surjective [IsSeparated g] (w : F.incidence G) :
    Function.Surjective (F.incidenceAmbientStalkMap G w) :=
  (F.incidenceInclusion G ≫ correspondenceTripleInclusion f g h).stalkMap_surjective w

section Tor

variable [Flat f] [Smooth g] [IsSeparated g] [Flat h]

/-- The actual incidence ideal annihilates every actual intermediate categorical Tor module. -/
theorem incidenceTor_kernel_annihilator (w : F.incidence G) (n : ℕ) :
    RingHom.ker (F.incidenceAmbientStalkMap G w) ≤
      Module.annihilator (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) := by
  erw [Intersection.stalkMap_kernel_eq_sup (F.incidenceInclusion G)
    (F.incidenceToSupportProduct G) (correspondenceTripleInclusion f g h)
    (F.supportProductInclusion G) (F.incidence_ambient_isPullback G) w]
  obtain ⟨s, hs, hker⟩ := exists_regular_kernel_correspondenceTripleInclusion f g h
    (F.incidenceInclusion G w)
  exact Intersection.support_le_annihilator_tor (correspondenceTripleInclusion f g h)
    (F.incidenceInclusion G w) (F.supportProductInclusion G)
    (F.incidenceToSupportProduct G w)
    (Intersection.point_eq _ _ _ _ (F.incidence_ambient_isPullback G) w) s hker hs n

/-- Actual intermediate Tor, now with its constructed action by the full incidence local ring. -/
def incidenceTorOnIncidence (w : F.incidence G) (n : ℕ) :
    ModuleCat.{u} ((F.incidence G).presheaf.stalk w) :=
  _root_.ModuleCat.SurjectiveScalarDescent.descendedModule (F.incidenceAmbientStalkMap G w)
    (F.incidenceAmbientStalkMap_surjective G w) (F.incidenceTor G w n)
    (F.incidenceTor_kernel_annihilator G w n)

/-- The descended actual Tor retains exactly its original ambient scalar action. -/
def incidenceTorOnIncidenceRestrictIso (w : F.incidence G) (n : ℕ) :
    F.incidenceTor G w n ≅
      (ModuleCat.restrictScalars (F.incidenceAmbientStalkMap G w)).obj
        (F.incidenceTorOnIncidence G w n) :=
  _root_.ModuleCat.SurjectiveScalarDescent.restrictIso (F.incidenceAmbientStalkMap G w)
    (F.incidenceAmbientStalkMap_surjective G w) (F.incidenceTor G w n)
    (F.incidenceTor_kernel_annihilator G w n)

end Tor

variable [IsSeparated g] (w : F.incidence G)
  (s : List (F.incidenceAmbientStalk G w))
  (hker : RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
    (F.incidenceInclusion G w)).hom = Ideal.ofList s)

include hker in
/-- Literal diagonal equations and the coefficient kernel annihilate actual homology,
without regularity or finite-length assumptions on that homology. -/
theorem incidenceKoszul_kernel_annihilator (n : ℕ) :
    RingHom.ker (F.incidenceAmbientStalkMap G w) ≤
      Module.annihilator (F.incidenceAmbientStalk G w)
        ((_root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule G w)
            s).homology n) := by
  erw [Intersection.stalkMap_kernel_eq_sup (F.incidenceInclusion G)
    (F.incidenceToSupportProduct G) (correspondenceTripleInclusion f g h)
    (F.supportProductInclusion G) (F.incidence_ambient_isPullback G) w, hker]
  rw [← Intersection.coefficientStalkModule_annihilator (correspondenceTripleInclusion f g h)
    (F.incidenceInclusion G w) (F.supportProductInclusion G)
    (F.incidenceToSupportProduct G w)
    (Intersection.point_eq _ _ _ _ (F.incidence_ambient_isPullback G) w)]
  exact _root_.ChainComplex.Koszul.support_le_annihilator_coefficient_homology
    (F.incidenceSupportStalkModule G w) s n

/-- Actual intermediate coefficient-Koszul homology with its full incidence-stalk action. -/
def incidenceKoszulOnIncidence (n : ℕ) : ModuleCat.{u} ((F.incidence G).presheaf.stalk w) :=
  _root_.ModuleCat.SurjectiveScalarDescent.descendedModule (F.incidenceAmbientStalkMap G w)
    (F.incidenceAmbientStalkMap_surjective G w)
    ((_root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule G w) s).homology
        n)
    (F.incidenceKoszul_kernel_annihilator G w s hker n)

/-- The homology quotient action recovers the exact original ambient homology module. -/
def incidenceKoszulOnIncidenceRestrictIso (n : ℕ) :
    (_root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule G w) s).homology n
        ≅
      (ModuleCat.restrictScalars (F.incidenceAmbientStalkMap G w)).obj
        (F.incidenceKoszulOnIncidence G w s hker n) :=
  _root_.ModuleCat.SurjectiveScalarDescent.restrictIso (F.incidenceAmbientStalkMap G w)
    (F.incidenceAmbientStalkMap_surjective G w)
    ((_root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule G w) s).homology
        n)
    (F.incidenceKoszul_kernel_annihilator G w s hker n)

end Motivic.FiniteCorrespondenceGenerator

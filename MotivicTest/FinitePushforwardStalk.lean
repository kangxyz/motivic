/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardStalk
public import Motivic.Algebra.Homology.TorComparison.AmbientLength

/-!
# Actual finite-fiber stalk scalar consumers

The full localized finite algebra is compared to the actual source scheme
stalk. The constructed scalar square identifies the two literal module
restriction routes and preserves local length, without asserting finiteness
of an individual source stalk over the target local ring.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.FinitePushforwardStalk

open FiniteFiber

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B]
  (p : PrimeSpectrum A) (q : MaximalSpectrum (localAlgebra A B p))

/-- The two actual target-scalar routes act identically on every source-stalk module. -/
theorem actualRestrictionScalar
    (M : ModuleCat.{u} ((Spec B).presheaf.stalk (sourcePoint A B p q).1))
    (r : Localization.AtPrime p.asIdeal) (m : M) :
    (sourceSchemeStalkIso A B p q).hom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) r) • m =
      pointedSpecStalkMap (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
        (sourcePoint A B p q).1 (sourcePoint A B p q).2 ((Spec.stalkIso A p).inv r) • m :=
  by
    change ((CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) ≫ (sourceSchemeStalkIso A B p q).hom) r) • m = _
    rw [sourceSchemeStalkIso_base_square]
    rfl

/-- Every actual source-module map respects the common literal target action. -/
theorem actualRestrictionMap
    {M N : ModuleCat.{u} ((Spec B).presheaf.stalk (sourcePoint A B p q).1)} (g : M ⟶ N)
    (r : Localization.AtPrime p.asIdeal) (m : M) :
    g ((sourceSchemeStalkIso A B p q).hom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) r) • m) =
      pointedSpecStalkMap (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
        (sourcePoint A B p q).1 (sourcePoint A B p q).2 ((Spec.stalkIso A p).inv r) • g m := by
  rw [map_smul]
  exact actualRestrictionScalar A B p q N r (g m)

/-- The actual source residue map commutes on every base residue element. -/
theorem actualResidueScalar (z : p.asIdeal.ResidueField) :
    (sourceSchemeResidueIso A B p q).hom
      (IsLocalRing.ResidueField.map
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) z) =
      pointedSpecResidueMap (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
        (sourcePoint A B p q).1 (sourcePoint A B p q).2
        ((Scheme.Spec.residueFieldIso A p).inv z) :=
  ConcreteCategory.congr_hom (sourceSchemeResidueIso_base_square A B p q) z

/-- Length of every actual source-stalk module is preserved by the constructed equivalence. -/
theorem actualSourceStalkLength
    (M : ModuleCat.{u} ((Spec B).presheaf.stalk (sourcePoint A B p q).1)) :
    Module.length (Localization.AtPrime q.asIdeal)
        ((ModuleCat.restrictScalars.{u} (sourceSchemeStalkIso A B p q).hom.hom).obj M) =
      Module.length ((Spec B).presheaf.stalk (sourcePoint A B p q).1) M :=
  TorComparison.length_restrictScalars_of_surjective _
    (sourceSchemeStalkIso A B p q).commRingCatIsoToRingEquiv.surjective M

end Motivic.MotivicTest.FinitePushforwardStalk

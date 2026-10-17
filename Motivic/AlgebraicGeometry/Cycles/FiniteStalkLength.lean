/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.LengthEulerRestriction
public import Motivic.AlgebraicGeometry.Cycles.FiniteResidueDegree

/-!
# Actual finite-map stalk lengths and signed Euler sums

The local-ring restriction formula is applied to the literal stalk map of a
finite scheme morphism. Its residue extension is genuinely finite by the
existing finite-fiber proof, and its dimension is the same residue degree
used by finite cycle pushforward. Thus scalar restriction of actual stalk
modules multiplies finite signed Euler lengths by that actual degree.
This is a local module calculation, not a sheaf pushforward or an asserted
intersection projection formula.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic.LengthEuler

universe u v w

namespace Motivic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)

/-- Length along the actual stalk map is multiplied by the actual finite residue degree. -/
theorem length_finite_stalk_restrictScalars (M : ModuleCat.{v} (X.presheaf.stalk x)) :
    Module.length (Y.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj M) =
      Module.length (X.presheaf.stalk x) M * (f.residueDegree x : ℕ∞) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hmap : algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (f.residueFieldMap x).hom := by
    apply RingHom.ext
    intro r
    obtain ⟨r, rfl⟩ := Y.residue_surjective (f x) r
    rfl
  have : Module.Finite (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.finite_algebraMap.mp (hmap.symm ▸ residueFieldMap_finite f x)
  have hd : f.residueDegree x =
      Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
    dsimp +instances only [Scheme.Hom.residueDegree, Scheme.residueField,
      Scheme.instFieldCarrierResidueField]
    erw [← hmap, toAlgebra_algebraMap]
  rw [hd]
  exact LengthEuler.length_restrictScalars (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) M

variable {ι : Type w} (M : ι → ModuleCat.{v} (X.presheaf.stalk x))

/-- Finite graded stalk-module lengths remain finite under the literal finite-map restriction. -/
theorem finiteLengthSupport_finite_stalk_restrictScalars (hM : FiniteLengthSupport M) :
    FiniteLengthSupport (fun n => (ModuleCat.restrictScalars (f.stalkMap x).hom).obj (M n)) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hmap : algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (f.residueFieldMap x).hom := by
    apply RingHom.ext
    intro r
    obtain ⟨r, rfl⟩ := Y.residue_surjective (f x) r
    rfl
  have : Module.Finite (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.finite_algebraMap.mp (hmap.symm ▸ residueFieldMap_finite f x)
  exact hM.restrictScalars (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) M

/-- Every genuine finite signed stalk Euler sum scales by the finite cycle-pushforward degree. -/
theorem signedLengthSum_finite_stalk_restrictScalars (sign : ι → ℤ)
    (hM : FiniteLengthSupport M) :
    signedLengthSum
        (fun n => (ModuleCat.restrictScalars (f.stalkMap x).hom).obj (M n)) sign
        (finiteLengthSupport_finite_stalk_restrictScalars f x M hM) =
      signedLengthSum M sign hM * (f.residueDegree x : ℤ) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hmap : algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (f.residueFieldMap x).hom := by
    apply RingHom.ext
    intro r
    obtain ⟨r, rfl⟩ := Y.residue_surjective (f x) r
    rfl
  have : Module.Finite (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.finite_algebraMap.mp (hmap.symm ▸ residueFieldMap_finite f x)
  have hd : f.residueDegree x =
      Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
    dsimp +instances only [Scheme.Hom.residueDegree, Scheme.residueField,
      Scheme.instFieldCarrierResidueField]
    erw [← hmap, toAlgebra_algebraMap]
  rw [hd]
  exact LengthEuler.signedLengthSum_restrictScalars
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) M sign hM

end Motivic

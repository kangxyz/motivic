/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite

/-! # Canonical separation of the auxiliary row from the unchanged base coordinates -/
@[expose] public noncomputable section
open MvPolynomial
universe u
namespace QuadraticIncidence

/-- Only the canonical polynomial-ring equivalence is used; no coordinates are reselected. -/
def relativeCoordinateHom (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    (d : ℕ) (f : Fin (d + 1) → B) : Polynomial (MvPolynomial (Fin d) k) →+* B :=
  (aeval f).toRingHom.comp (finSuccEquiv k d).symm.toRingHom

/-- The original auxiliary coordinate is the polynomial variable. -/
theorem relativeCoordinateHom_X (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    (d : ℕ) (f : Fin (d + 1) → B) :
    relativeCoordinateHom k B d f Polynomial.X = f 0 := by
  have he : (finSuccEquiv k d).symm Polynomial.X = X 0 := by
    apply (finSuccEquiv k d).injective
    simp [finSuccEquiv_X_zero]
  simp [relativeCoordinateHom, he]

/-- The curve-base map consists of exactly the unchanged tail coordinates. -/
theorem relativeCoordinateHom_comp_C (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    (d : ℕ) (f : Fin (d + 1) → B) :
    (relativeCoordinateHom k B d f).comp Polynomial.C =
      (aeval (R := k) (fun i : Fin d => f i.succ)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have he := congrArg (fun h : k →+* MvPolynomial (Fin (d + 1)) k => h a)
      (finSuccEquiv_comp_C_eq_C (R := k) d)
    simpa [relativeCoordinateHom, RingHom.comp_apply] using congrArg (aeval f) he
  · intro i
    have he : (finSuccEquiv k d).symm (Polynomial.C (X i)) = X i.succ := by
      apply (finSuccEquiv k d).injective
      simp [finSuccEquiv_X_succ]
    simp [relativeCoordinateHom, he]

/-- Finiteness passes through this exact coordinate relabeling. -/
theorem relativeCoordinateHom_finite (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    (d : ℕ) (f : Fin (d + 1) → B) (hf : (aeval (R := k) f).toRingHom.Finite) :
    (relativeCoordinateHom k B d f).Finite :=
  hf.comp (RingHom.Finite.of_surjective _ (finSuccEquiv k d).symm.surjective)

/-- The already chosen étale principal neighborhood survives the same relabeling. -/
theorem relativeCoordinateHom_etale_away
    (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    (d : ℕ) (f : Fin (d + 1) → B) (r : B)
    (he : ((algebraMap B (Localization.Away r)).comp (aeval (R := k) f).toRingHom).Etale) :
    ((algebraMap B (Localization.Away r)).comp (relativeCoordinateHom k B d f)).Etale := by
  change (((algebraMap B (Localization.Away r)).comp (aeval (R := k) f).toRingHom).comp
    (finSuccEquiv k d).symm.toRingHom).Etale
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (finSuccEquiv k d).symm.bijective) he

end QuadraticIncidence

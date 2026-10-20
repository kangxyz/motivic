/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Boundary-one rational functions in a monic affine chart

The ambient ring is the actual localization of `R[X]` at monic polynomials
with invertible constant coefficient. The subgroup consists of fractions of
two such polynomials with the same degree and constant coefficient. These
are the affine polynomial presentations used in MVW, Lemma 4.3.

Coefficient homomorphisms need not be injective. In particular the maps here
include simplex face specializations. This file does not assert the geometric
presentation theorem for arbitrary finite correspondences, or identify this
subgroup with the full boundary-one sheaf on a projective line.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

universe u v w

namespace Polynomial.BoundaryOneRationalFunctions

variable (R : Type u) [CommRing R]

/-- Denominators regular and invertible at zero, normalized at infinity. -/
def denominators : Submonoid R[X] where
  carrier := {p | p.Monic ∧ IsUnit (p.coeff 0)}
  one_mem' := ⟨monic_one, by simp⟩
  mul_mem' := by
    intro p q hp hq
    exact ⟨hp.1.mul hq.1, by simpa only [mul_coeff_zero] using hp.2.mul hq.2⟩

/-- The genuine localized polynomial ring, not a formal group of presentations. -/
abbrev Ring := Localization (denominators R)

/-- Every allowed denominator is a non-zero-divisor, even over nonreduced rings. -/
theorem denominators_le_nonZeroDivisors : denominators R ≤ nonZeroDivisors R[X] :=
  fun _ hp => hp.1.mem_nonZeroDivisors

/-- The actual polynomial ring embeds in the ambient localization. -/
theorem algebraMap_injective :
    Function.Injective (algebraMap R[X] (Ring R)) :=
  IsLocalization.injective (Ring R) (denominators_le_nonZeroDivisors R)

variable {R}

/-- The unit represented by an allowed polynomial in the actual localization. -/
def polynomialUnit (p : denominators R) : (Ring R)ˣ :=
  (IsLocalization.map_units (Ring R) p).unit

@[simp] theorem polynomialUnit_val (p : denominators R) :
    (polynomialUnit p : Ring R) = algebraMap R[X] (Ring R) p :=
  IsUnit.unit_spec _

@[simp] theorem polynomialUnit_one : polynomialUnit (1 : denominators R) = 1 := by
  apply Units.ext
  simp

@[simp] theorem polynomialUnit_mul (p q : denominators R) :
    polynomialUnit (p * q) = polynomialUnit p * polynomialUnit q := by
  apply Units.ext
  simp

/-- A genuine rational function with a specified numerator and denominator. -/
def fraction (p q : denominators R) : (Ring R)ˣ :=
  polynomialUnit p / polynomialUnit q

@[simp] theorem fraction_self (p : denominators R) : fraction p p = 1 := by
  simp [fraction]

theorem fraction_mul (p q r s : denominators R) :
    fraction p q * fraction r s = fraction (p * r) (q * s) := by
  simp only [fraction, polynomialUnit_mul]
  exact div_mul_div_comm (polynomialUnit p) (polynomialUnit q)
    (polynomialUnit r) (polynomialUnit s)

@[simp] theorem fraction_inv (p q : denominators R) :
    (fraction p q)⁻¹ = fraction q p := inv_div _ _

/-- Equality of presentations is precisely ordinary polynomial cross-multiplication. -/
theorem fraction_eq_iff (p q r s : denominators R) :
    fraction p q = fraction r s ↔ (p : R[X]) * s = (r : R[X]) * q := by
  rw [fraction, fraction,
    div_eq_div_iff_mul_eq_mul (a := polynomialUnit p) (b := polynomialUnit q)
      (c := polynomialUnit r) (d := polynomialUnit s), ← polynomialUnit_mul,
    ← polynomialUnit_mul]
  constructor
  · intro h
    apply algebraMap_injective R
    exact congrArg (fun z : (Ring R)ˣ => (z : Ring R)) h
  · intro h
    exact congrArg polynomialUnit (Subtype.ext h)

/-- A boundary-one presentation is trivial exactly when its actual polynomials agree. -/
@[simp] theorem fraction_eq_one_iff (p q : denominators R) :
    fraction p q = 1 ↔ p = q := by
  rw [fraction, div_eq_one]
  constructor
  · intro h
    apply Subtype.ext
    apply algebraMap_injective R
    exact congrArg (fun z : (Ring R)ˣ => (z : Ring R)) h
  · exact congrArg polynomialUnit

variable (R)

/-- The multiplicative subgroup of actual boundary-one polynomial fractions. -/
def group : Subgroup (Ring R)ˣ where
  carrier := {f | ∃ p q : denominators R,
    (p : R[X]).natDegree = (q : R[X]).natDegree ∧
    (p : R[X]).coeff 0 = (q : R[X]).coeff 0 ∧ f = fraction p q}
  one_mem' := ⟨1, 1, rfl, rfl, (fraction_self 1).symm⟩
  mul_mem' := by
    rintro f g ⟨p, q, hd, hc, rfl⟩ ⟨r, s, he, hb, rfl⟩
    refine ⟨p * r, q * s, ?_, ?_, fraction_mul p q r s⟩
    · change ((p : R[X]) * r).natDegree = ((q : R[X]) * s).natDegree
      rw [p.2.1.natDegree_mul r.2.1, q.2.1.natDegree_mul s.2.1, hd, he]
    · change ((p : R[X]) * r).coeff 0 = ((q : R[X]) * s).coeff 0
      simp only [mul_coeff_zero, hc, hb]
  inv_mem' := by
    rintro f ⟨p, q, hd, hc, rfl⟩
    exact ⟨q, p, hd.symm, hc.symm, fraction_inv p q⟩

variable {R}

/-- Construct a boundary-one function from an honest monic polynomial ratio. -/
def ofPresentation (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (hd : p.natDegree = q.natDegree) (hc : p.coeff 0 = q.coeff 0)
    (hu : IsUnit (p.coeff 0)) : group R :=
  ⟨fraction ⟨p, hp, hu⟩ ⟨q, hq, hc ▸ hu⟩,
    ⟨⟨p, hp, hu⟩, ⟨q, hq, hc ▸ hu⟩, hd, hc, rfl⟩⟩

variable {S : Type v} [CommRing S]

/-- All coefficient homomorphisms preserve the allowed denominators. -/
def denominatorMap (φ : R →+* S) : denominators R →* denominators S where
  toFun p := ⟨p.val.map φ, p.2.1.map φ, by simpa only [coeff_map] using p.2.2.map φ⟩
  map_one' := Subtype.ext (Polynomial.map_one φ)
  map_mul' p q := Subtype.ext (Polynomial.map_mul φ)

/-- The canonical homomorphism of the actual localized polynomial rings. -/
def ringMap (φ : R →+* S) : Ring R →+* Ring S :=
  IsLocalization.map (M := denominators R) (T := denominators S)
    (Ring S) (Polynomial.mapRingHom φ) fun p hp =>
    (denominatorMap φ ⟨p, hp⟩).2

@[simp] theorem ringMap_algebraMap (φ : R →+* S) (p : R[X]) :
    ringMap φ (algebraMap R[X] (Ring R) p) =
      algebraMap S[X] (Ring S) (p.map φ) := by
  unfold ringMap
  apply IsLocalization.map_eq

theorem ringMap_polynomialUnit (φ : R →+* S) (p : denominators R) :
    Units.map (ringMap φ).toMonoidHom (polynomialUnit p) =
      polynomialUnit (denominatorMap φ p) := by
  apply Units.ext
  simp [denominatorMap]

@[simp] theorem ringMap_polynomialUnit_coe (φ : R →+* S) (p : denominators R) :
    Units.map (ringMap φ : Ring R →* Ring S) (polynomialUnit p) =
      polynomialUnit (denominatorMap φ p) :=
  ringMap_polynomialUnit φ p

theorem ringMap_fraction (φ : R →+* S) (p q : denominators R) :
    Units.map (ringMap φ).toMonoidHom (fraction p q) =
      fraction (denominatorMap φ p) (denominatorMap φ q) := by
  simp only [fraction, map_div]
  congr 1
  · exact ringMap_polynomialUnit φ p
  · exact ringMap_polynomialUnit φ q

@[simp] theorem ringMap_fraction_coe (φ : R →+* S) (p q : denominators R) :
    Units.map (ringMap φ : Ring R →* Ring S) (fraction p q) =
      fraction (denominatorMap φ p) (denominatorMap φ q) :=
  ringMap_fraction φ p q

/-- Restriction of actual rational functions along arbitrary coefficient maps. -/
def map (φ : R →+* S) : group R →* group S where
  toFun f := ⟨Units.map (ringMap φ).toMonoidHom f.val, by
    obtain ⟨p, q, hd, hc, hf⟩ := f.2
    refine ⟨denominatorMap φ p, denominatorMap φ q, ?_, ?_, ?_⟩
    · nontriviality S
      exact (p.2.1.natDegree_map φ).trans (hd.trans (q.2.1.natDegree_map φ).symm)
    · simpa only [denominatorMap, MonoidHom.coe_mk, OneHom.coe_mk, coeff_map] using congrArg φ hc
    · rw [hf, ringMap_fraction]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' f g := Subtype.ext (map_mul _ _ _)

@[simp] theorem ringMap_id : ringMap (RingHom.id R) = RingHom.id (Ring R) := by
  apply IsLocalization.ringHom_ext (denominators R)
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, ringMap_algebraMap, Polynomial.map_id, RingHom.id_apply]

@[simp] theorem ringMap_comp {T : Type w} [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    ringMap (ψ.comp φ) = (ringMap ψ).comp (ringMap φ) := by
  apply IsLocalization.ringHom_ext (denominators R)
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, ringMap_algebraMap, Polynomial.map_map]

@[simp] theorem map_id (f : group R) : map (RingHom.id R) f = f := by
  apply Subtype.ext
  apply Units.ext
  change ringMap (RingHom.id R) (f.val : Ring R) = _
  rw [ringMap_id]
  rfl

@[simp] theorem map_comp {T : Type w} [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (f : group R) :
    map (ψ.comp φ) f = map ψ (map φ f) := by
  apply Subtype.ext
  apply Units.ext
  change ringMap (ψ.comp φ) (f.val : Ring R) = ringMap ψ (ringMap φ (f.val : Ring R))
  rw [ringMap_comp]
  rfl

variable [Nontrivial S]

@[simp] theorem map_ofPresentation (φ : R →+* S) (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hd : p.natDegree = q.natDegree)
    (hc : p.coeff 0 = q.coeff 0) (hu : IsUnit (p.coeff 0)) :
    map φ (ofPresentation p q hp hq hd hc hu) =
      ofPresentation (p.map φ) (q.map φ) (hp.map φ) (hq.map φ)
        ((hp.natDegree_map φ).trans (hd.trans (hq.natDegree_map φ).symm))
        (by simpa only [coeff_map] using congrArg φ hc)
        (by simpa only [coeff_map] using hu.map φ) := by
  apply Subtype.ext
  exact ringMap_fraction φ ⟨p, hp, hu⟩ ⟨q, hq, hc ▸ hu⟩

variable (R)

/-- Evaluation at the zero section extends to the actual localized ring. -/
def zeroValue : Ring R →+* R :=
  IsLocalization.lift (M := denominators R) (g := evalRingHom 0)
    fun p => by simpa only [coe_evalRingHom, ← coeff_zero_eq_eval_zero] using p.2.2

@[simp] theorem zeroValue_algebraMap (p : R[X]) :
    zeroValue R (algebraMap R[X] (Ring R) p) = p.coeff 0 := by
  unfold zeroValue
  rw [IsLocalization.lift_eq]
  exact (coeff_zero_eq_eval_zero p).symm

variable {R}

/-- Equality of numerator and denominator constants is literal boundary value one. -/
theorem zeroValue_eq_one (f : group R) : zeroValue R (f.val : Ring R) = 1 := by
  obtain ⟨p, q, _, hc, hf⟩ := f.2
  have he : Units.map (zeroValue R).toMonoidHom (polynomialUnit p) =
      Units.map (zeroValue R).toMonoidHom (polynomialUnit q) := by
    apply Units.ext
    change zeroValue R (polynomialUnit p : Ring R) = zeroValue R (polynomialUnit q : Ring R)
    simpa only [polynomialUnit_val, zeroValue_algebraMap] using hc
  have h : Units.map (zeroValue R).toMonoidHom f.val = 1 := by
    rw [hf, fraction, map_div, he]
    exact div_self' _
  exact congrArg (fun u : Rˣ => (u : R)) h

variable (R)

/-- The affine-chart localization maps to the actual total quotient ring. -/
def toFractionRing : Ring R →+* FractionRing R[X] :=
  IsLocalization.map (M := denominators R) (T := nonZeroDivisors R[X])
    (FractionRing R[X]) (RingHom.id R[X]) (denominators_le_nonZeroDivisors R)

@[simp] theorem toFractionRing_algebraMap (p : R[X]) :
    toFractionRing R (algebraMap R[X] (Ring R) p) =
      algebraMap R[X] (FractionRing R[X]) p := by
  unfold toFractionRing
  apply IsLocalization.map_eq

/-- Over a domain these are literally rational functions, with no extra identifications. -/
theorem toFractionRing_injective [IsDomain R] : Function.Injective (toFractionRing R) :=
  IsLocalization.map_injective_of_injective' (denominators R) R[X]
    (f := RingHom.id R[X]) (N := nonZeroDivisors R[X])
    (FractionRing R[X]) (denominators_le_nonZeroDivisors R)
    zero_notMem_nonZeroDivisors Function.injective_id

/-- The actual rational function attached to a polynomial presentation is `p / q`. -/
theorem toFractionRing_fraction [IsDomain R] (p q : denominators R) :
    toFractionRing R (fraction p q : Ring R) =
      algebraMap R[X] (FractionRing R[X]) p /
        algebraMap R[X] (FractionRing R[X]) q := by
  change ((Units.map (toFractionRing R).toMonoidHom (fraction p q) :
    (FractionRing R[X])ˣ) : FractionRing R[X]) = _
  rw [fraction, map_div, Units.val_div_eq_div_val]
  change toFractionRing R (polynomialUnit p : Ring R) /
    toFractionRing R (polynomialUnit q : Ring R) = _
  simp only [polynomialUnit_val, toFractionRing_algebraMap]

end Polynomial.BoundaryOneRationalFunctions

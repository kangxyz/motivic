/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Tactic.FieldSimp

/-!
# The explicit unit comparing normed graph ratios

These are multiplicative identities for the native determinant norm. In the
geometric application the coefficients come from a finite-free chart and
actual unit neighborhoods; this file does not produce those neighborhoods or
claim that the original coefficients are units.


Intended upstream module: `Aglib.RingTheory.Norm.GraphRatioUnit`.
-/

@[expose] public noncomputable section

namespace Algebra

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- The explicit target unit comparing the normed source ratio with the
original target graph ratio. -/
def normGraphRatioUnit (a b : Bˣ) (a' b' u : Rˣ) : Rˣ :=
  (Units.map (Algebra.norm R) a * b') / (u * Units.map (Algebra.norm R) b * a')

/-- The graph equation cancels in the fraction field, leaving the image of
an actual target unit. Only its image must be nonzero; it is not inverted in
the target ring or the boundary ring. -/
theorem normGraphRatioUnit_fraction {K : Type*} [Field K] (ρ : R →+* K)
    (a b : Bˣ) (a' b' u : Rˣ) (g : B) (c : R)
    (hg : Algebra.norm R g = (u : R) * c) (hc : ρ c ≠ 0) :
    (ρ (Algebra.norm R (a : B)) /
        (ρ (Algebra.norm R g) * ρ (Algebra.norm R (b : B)))) /
      (ρ (a' : R) / (ρ c * ρ (b' : R))) =
        ρ (normGraphRatioUnit a b a' b' u : R) := by
  have hr : ρ (normGraphRatioUnit a b a' b' u : R) =
      (ρ (Algebra.norm R (a : B)) * ρ (b' : R)) /
        (ρ (u : R) * ρ (Algebra.norm R (b : B)) * ρ (a' : R)) := by
    change ((Units.map ρ.toMonoidHom (normGraphRatioUnit a b a' b' u) : Kˣ) : K) = _
    simp [normGraphRatioUnit, Units.val_div_eq_div_val]
  have hu : ρ (u : R) ≠ 0 := (u.isUnit.map ρ).ne_zero
  have ha' : ρ (a' : R) ≠ 0 := (a'.isUnit.map ρ).ne_zero
  have hb' : ρ (b' : R) ≠ 0 := (b'.isUnit.map ρ).ne_zero
  have hb : ρ (Algebra.norm R (b : B)) ≠ 0 :=
    ((b.isUnit.map (Algebra.norm R)).map ρ).ne_zero
  rw [hr, hg, map_mul]
  field_simp

/-- The actual cross-product relation on the full boundary suffices: no
cross-degree equality of the individual source and target coefficients is assumed. -/
theorem normGraphRatioUnit_map_eq_one {Q : Type*} [CommRing Q] (ρ : R →+* Q)
    (a b : Bˣ) (a' b' u : Rˣ)
    (h : ρ (Algebra.norm R (a : B)) * ρ (b' : R) =
      ρ (Algebra.norm R (b : B)) * ρ (a' : R))
    (hu : ρ (u : R) = 1) :
    Units.map ρ.toMonoidHom (normGraphRatioUnit a b a' b' u) = 1 := by
  have hh : Units.map ρ.toMonoidHom (Units.map (Algebra.norm R) a) *
      Units.map ρ.toMonoidHom b' =
      Units.map ρ.toMonoidHom (Units.map (Algebra.norm R) b) *
        Units.map ρ.toMonoidHom a' := Units.ext h
  have huu : Units.map ρ.toMonoidHom u = 1 := Units.ext hu
  simp only [normGraphRatioUnit, map_div, map_mul, huu, one_mul]
  exact div_eq_one.mpr hh

end Algebra

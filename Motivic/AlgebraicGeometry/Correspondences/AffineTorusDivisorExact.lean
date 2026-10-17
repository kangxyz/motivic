module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusDivisorEquivalence
public import Motivic.Aglib.RingTheory.BoundaryOneRationalInvariants

/-! # The actual affine weight-one divisor exact sequence

The middle term is the original finite-correspondence group. Both maps are
constructed, and injectivity, exactness, and surjectivity are proved.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Polynomial.BoundaryOneRationalFunctions

namespace Motivic.AffineTorusPolynomialPresentation

universe u

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [IsDomain R] [Algebra.Smooth k R] [IsNoetherianRing R]

/-- Degree and signed constant coefficient of the actual original correspondence. -/
def divisorDegreeUnit :
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) →+
      ℤ × Additive Rˣ :=
  (degreeHom.toAdditiveLeft.prod signedValueHom.toAdditive).comp
    (rationalDivisorEquiv (k := k) (R := R)).symm.toAddMonoidHom

/-- The invariant of a genuine rational divisor is its degree and signed unit. -/
@[simp] theorem divisorDegreeUnit_rationalDivisor (f : Additive (admissibleGroup R)) :
    divisorDegreeUnit (rationalDivisorHom (k := k) f) =
      (fractionDegree f.toMul, Additive.ofMul (signedValueHom f.toMul)) := by
  change (degreeHom.toAdditiveLeft.prod signedValueHom.toAdditive)
    ((rationalDivisorEquiv (k := k) (R := R)).symm
      ((rationalDivisorEquiv (k := k) (R := R)) f)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- Exactness of the actual affine divisor sequence at original correspondences. -/
theorem divisorDegreeUnit_eq_zero_iff (z :
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k))) :
    divisorDegreeUnit z = 0 ↔ ∃ f : Additive (group R), boundaryDivisor f = z := by
  let a := (rationalDivisorEquiv (k := k) (R := R)).symm z
  have ha : rationalDivisorHom (k := k) a = z :=
    (rationalDivisorEquiv (k := k) (R := R)).apply_symm_apply z
  rw [← ha, divisorDegreeUnit_rationalDivisor]
  have hb : (fractionDegree a.toMul, Additive.ofMul (signedValueHom a.toMul)) = 0 ↔
      boundaryInvariant a.toMul = 1 := by
    rfl
  rw [hb, boundaryInvariant_eq_one_iff]
  constructor
  · intro h
    refine ⟨Additive.ofMul ⟨a.toMul.val, h⟩, ?_⟩
    rfl
  · rintro ⟨f, hf⟩
    have he := (rationalDivisorEquiv (k := k) (R := R)).injective hf
    change boundaryInclusion.toAdditive f = a at he
    have hv : f.toMul.val = a.toMul.val :=
      congrArg (fun x : Additive (admissibleGroup R) => x.toMul.val) he
    exact hv ▸ f.toMul.property

/-- Surjectivity of degree and signed unit for actual original correspondences. -/
theorem divisorDegreeUnit_surjective : Function.Surjective
    (divisorDegreeUnit (k := k) (R := R)) := by
  rintro ⟨d, u⟩
  obtain ⟨f, hf⟩ := boundaryInvariant_surjective (R := R)
    (Multiplicative.ofAdd d, u.toMul)
  refine ⟨rationalDivisorHom (k := k) (Additive.ofMul f), ?_⟩
  rw [divisorDegreeUnit_rationalDivisor]
  exact congrArg (fun x : Multiplicative ℤ × Rˣ =>
    (x.1.toAdd, Additive.ofMul x.2)) hf

/-- The first composite in the actual affine divisor sequence is zero. -/
@[simp] theorem divisorDegreeUnit_boundaryDivisor (f : Additive (group R)) :
    divisorDegreeUnit (boundaryDivisor (k := k) f) = 0 :=
  (divisorDegreeUnit_eq_zero_iff _).mpr ⟨f, rfl⟩

end Motivic.AffineTorusPolynomialPresentation

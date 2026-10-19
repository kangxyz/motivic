/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.Interpolation.TwoUnitFamily
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finite monic deformations preserving two polynomial units

For `deg A + deg B < deg p`, the polynomial `p(z) - t γ A(z) B(z)`
is monic of the same degree as `p`. Coprimality of `p` with `A B` makes
both polynomial coordinates units in the entire finite free quotient.
No localization, reduction, or selection of components occurs.

Over an infinite field a scalar `c` avoids both coordinates. Choosing
`γ = p(c)/(A(c) B(c))` gives a rational root in the one fiber. When
`deg p > 1`, each irreducible factor of that whole fiber has smaller degree.
These are algebraic statements; the auxiliary coordinate `z` still matters
when forming a closed geometric embedding.
-/

@[expose] public noncomputable section

open Polynomial

namespace Polynomial.TwoUnitMonicDeformation

universe u

variable {k : Type u} [Field k]

/-- Evaluate a polynomial coordinate at the adjoined outer variable. -/
def coordinate (f : k[X][X]) (A : k[X]) : AdjoinRoot f :=
  AdjoinRoot.mk f (A.map C)

/-- Coprimality survives any deformation divisible by the coordinate. -/
theorem coordinate_isUnit_of_congruent (f : k[X][X]) (p A : k[X])
    (hcop : IsCoprime p A) (hdiv : A.map C ∣ f - p.map C) :
    IsUnit (coordinate f A) := by
  obtain ⟨q, hq⟩ := hdiv
  have hf : f = p.map C + A.map C * q := by linear_combination hq
  have hc : IsCoprime f (A.map C) := by
    rw [hf]
    exact (hcop.map (Polynomial.mapRingHom C)).add_mul_left_left q
  have hu := hc.map (AdjoinRoot.mk f)
  simpa only [coordinate, AdjoinRoot.mk_self, isCoprime_zero_left] using hu

/-- A polynomial of smaller degree is coprime to an irreducible polynomial. -/
theorem isCoprime_of_irreducible_of_natDegree_lt {p A : k[X]} (hp : Irreducible p)
    (hA : A ≠ 0) (hdeg : A.natDegree < p.natDegree) : IsCoprime p A := by
  exact (hp.isCoprime_or_dvd A).resolve_right
    (not_dvd_of_natDegree_lt hA hdeg)

/-- The degree bound makes the product coprime to the original irreducible polynomial. -/
theorem isCoprime_product {p A B : k[X]} (hp : Irreducible p)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) : IsCoprime p (A * B) :=
  isCoprime_of_irreducible_of_natDegree_lt hp (mul_ne_zero hA hB)
    (lt_of_le_of_lt natDegree_mul_le hdeg)

/-- Linear interpolation preserves a coordinate when the endpoint difference
is divisible by it. The coordinate is a unit on the whole family. -/
theorem interpolate_coordinate_isUnit (p q A : k[X]) (hcop : IsCoprime p A)
    (hdiv : A ∣ q - p) :
    IsUnit (coordinate (MonicUnitInterpolation.interpolate p q) A) := by
  apply coordinate_isUnit_of_congruent _ p _ hcop
  have heq : MonicUnitInterpolation.interpolate p q - p.map C =
      C X * (q - p).map C := by
    simp only [MonicUnitInterpolation.interpolate, Polynomial.map_sub]
    rw [C_sub, C_1]
    ring
  rw [heq]
  exact dvd_mul_of_dvd_right (Polynomial.map_dvd C hdiv) _

/-- The actual finite-family equation, with `t` in the coefficient ring. -/
def family (p A B : k[X]) (γ : k) : k[X][X] :=
  p.map C - C (X * C γ) * (A * B).map C

/-- The literal whole polynomial at parameter `s`. -/
def endpointPolynomial (p A B : k[X]) (γ s : k) : k[X] :=
  p - C (s * γ) * (A * B)

private theorem perturbation_natDegree_lt (p A B : k[X]) (γ : k)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    (C (X * C γ) * (A * B).map C).natDegree < (p.map C).natDegree := by
  rw [natDegree_map_eq_of_injective C_injective p]
  exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans
    (natDegree_map_le.trans natDegree_mul_le)) hdeg

/-- No leading coefficient is lost anywhere on the parameter line. -/
theorem family_monic (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) : (family p A B γ).Monic :=
  (hp.map C).sub_of_left (degree_lt_degree (perturbation_natDegree_lt p A B γ hdeg))

/-- The degree is constant on the entire family. -/
theorem family_natDegree (p A B : k[X]) (γ : k)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    (family p A B γ).natDegree = p.natDegree := by
  rw [family, natDegree_sub_eq_left_of_natDegree_lt
    (perturbation_natDegree_lt p A B γ hdeg), natDegree_map_eq_of_injective C_injective]

/-- Specialization is to the whole quotient polynomial, including repeated factors. -/
@[simp] theorem specialize (p A B : k[X]) (γ s : k) :
    (family p A B γ).map (evalRingHom s) = endpointPolynomial p A B γ s := by
  have hc : (evalRingHom s).comp C = RingHom.id k := by ext; simp
  simp only [family, endpointPolynomial, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, coe_evalRingHom, eval_mul, eval_X, eval_C,
    Polynomial.map_map, hc, Polynomial.map_id]

@[simp] theorem endpointPolynomial_zero (p A B : k[X]) (γ : k) :
    endpointPolynomial p A B γ 0 = p := by simp [endpointPolynomial]

/-- Every scalar fiber is monic. -/
theorem endpointPolynomial_monic (p A B : k[X]) (γ s : k) (hp : p.Monic)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    (endpointPolynomial p A B γ s).Monic := by
  rw [← specialize]
  exact (family_monic p A B γ hp hdeg).map _

/-- Every scalar fiber has the original degree. -/
theorem endpointPolynomial_natDegree (p A B : k[X]) (γ s : k)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    (endpointPolynomial p A B γ s).natDegree = p.natDegree := by
  apply natDegree_sub_eq_left_of_natDegree_lt
  exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans natDegree_mul_le) hdeg

/-- Both original coordinates remain units on the entire affine family. -/
theorem coordinate_isUnit (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    IsUnit (coordinate (family p A B γ) A) ∧
      IsUnit (coordinate (family p A B γ) B) := by
  have hu : IsUnit (coordinate (family p A B γ) (A * B)) := by
    apply coordinate_isUnit_of_congruent _ p _ hcop
    refine ⟨-C (X * C γ), ?_⟩
    simp only [family]
    ring
  simpa only [coordinate, Polynomial.map_mul, map_mul, IsUnit.mul_iff] using hu

/-- The first actual unit, before any specialization. -/
def firstUnit (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (AdjoinRoot (family p A B γ))ˣ := (coordinate_isUnit p A B γ hcop).1.unit

/-- The second actual unit, before any specialization. -/
def secondUnit (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (AdjoinRoot (family p A B γ))ˣ := (coordinate_isUnit p A B γ hcop).2.unit

@[simp] theorem firstUnit_val (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (firstUnit p A B γ hcop : AdjoinRoot (family p A B γ)) =
      coordinate (family p A B γ) A := IsUnit.unit_spec _

@[simp] theorem secondUnit_val (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (secondUnit p A B γ hcop : AdjoinRoot (family p A B γ)) =
      coordinate (family p A B γ) B := IsUnit.unit_spec _

/-- Finite freeness and faithful flatness hold for the actual unlocalized quotient. -/
theorem finite_free_faithfullyFlat (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    Module.Finite k[X] (AdjoinRoot (family p A B γ)) ∧
      Module.Free k[X] (AdjoinRoot (family p A B γ)) ∧
      Module.FaithfullyFlat k[X] (AdjoinRoot (family p A B γ)) := by
  have hm := family_monic p A B γ hp hdeg
  have hd : 0 < (family p A B γ).natDegree := by
    rw [family_natDegree p A B γ hdeg]
    exact lt_of_le_of_lt (Nat.zero_le _) hdeg
  exact ⟨hm.finite_adjoinRoot, hm.free_adjoinRoot,
    TwoUnitPolynomialFamily.faithfullyFlat hm hd⟩

/-- Scalar specialization preserves every polynomial coordinate. -/
@[simp] theorem endpoint_coordinate (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (A : k[X]) :
    TwoUnitPolynomialFamily.endpoint f s p hp (coordinate f A) = AdjoinRoot.mk p A := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB =>
    simpa only [coordinate, Polynomial.map_add, map_add] using congrArg₂ (· + ·) hA hB
  | monomial n a =>
    simp only [coordinate, ← C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, map_mul,
      map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      TwoUnitPolynomialFamily.endpoint_of, eval_C, TwoUnitPolynomialFamily.endpoint_root]

/-- The full tensor-fiber equivalence preserves every polynomial coordinate. -/
@[simp] theorem endpointFiberEquiv_coordinate (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (A : k[X]) :
    TwoUnitPolynomialFamily.endpointFiberEquiv f s p hp
        (Algebra.PolynomialFiber.specialize (AdjoinRoot f) s (coordinate f A)) =
      AdjoinRoot.mk p A := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB =>
    simpa only [coordinate, Polynomial.map_add, map_add] using congrArg₂ (· + ·) hA hB
  | monomial n a =>
    simp only [coordinate, ← C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, map_mul,
      map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      TwoUnitPolynomialFamily.endpointFiberEquiv_of, eval_C,
      TwoUnitPolynomialFamily.endpointFiberEquiv_root]

/-- The specific scalar which inserts the chosen rational root. -/
def gamma (p A B : k[X]) (c : k) : k := p.eval c / (A.eval c * B.eval c)

/-- Over an infinite field one can avoid the finite zero sets of both coordinates. -/
theorem exists_good_point [Infinite k] (A B : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ c : k, A.eval c ≠ 0 ∧ B.eval c ≠ 0 := by
  by_contra h
  have hz : A * B = 0 := zero_of_eval_zero _ (by
    intro c
    by_contra hc
    exact h ⟨c, by simpa only [eval_mul, mul_ne_zero_iff] using hc⟩)
  exact (mul_ne_zero hA hB) hz

/-- The whole one fiber has the specified rational root. -/
theorem endpoint_one_eval (p A B : k[X]) (c : k)
    (hA : A.eval c ≠ 0) (hB : B.eval c ≠ 0) :
    (endpointPolynomial p A B (gamma p A B c) 1).eval c = 0 := by
  simp only [endpointPolynomial, eval_sub, eval_mul, eval_C, one_mul, gamma]
  rw [div_mul_cancel₀ _ (mul_ne_zero hA hB), sub_self]

/-- For degree greater than one the chosen deformation scalar is nonzero. -/
theorem gamma_ne_zero (p A B : k[X]) (c : k) (hp : Irreducible p)
    (hdeg : 1 < p.natDegree) (hA : A.eval c ≠ 0) (hB : B.eval c ≠ 0) :
    gamma p A B c ≠ 0 :=
  div_ne_zero (hp.not_isRoot_of_natDegree_ne_one (ne_of_gt hdeg)) (mul_ne_zero hA hB)

/-- A monic polynomial with a rational root and degree greater than one has
only irreducible factors of strictly smaller degree. Multiplicities are unrestricted. -/
theorem irreducible_factor_natDegree_lt_of_root {q r : k[X]} (hq : q.Monic)
    (hdeg : 1 < q.natDegree) (c : k) (hc : q.eval c = 0)
    (hr : Irreducible r) (hdiv : r ∣ q) : r.natDegree < q.natDegree := by
  apply lt_of_le_of_ne (natDegree_le_of_dvd hdiv hq.ne_zero)
  intro heq
  have hqirr : Irreducible q :=
    (associated_of_dvd_of_natDegree_le hdiv hq.ne_zero heq.ge).irreducible hr
  exact hqirr.not_isRoot_of_natDegree_ne_one (ne_of_gt hdeg) hc

/-- Every irreducible factor of the entire one endpoint has smaller original degree. -/
theorem irreducible_factor_natDegree_lt (p A B : k[X]) (c : k) (hp : p.Monic)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) (hn : 1 < p.natDegree)
    (hA : A.eval c ≠ 0) (hB : B.eval c ≠ 0) (r : k[X]) (hr : Irreducible r)
    (hdiv : r ∣ endpointPolynomial p A B (gamma p A B c) 1) :
    r.natDegree < p.natDegree := by
  have hd := endpointPolynomial_natDegree p A B (gamma p A B c) 1 hdeg
  rw [← hd]
  exact irreducible_factor_natDegree_lt_of_root
    (endpointPolynomial_monic p A B _ 1 hp hdeg) (hd ▸ hn) c
    (endpoint_one_eval p A B c hA hB) hr hdiv

end Polynomial.TwoUnitMonicDeformation

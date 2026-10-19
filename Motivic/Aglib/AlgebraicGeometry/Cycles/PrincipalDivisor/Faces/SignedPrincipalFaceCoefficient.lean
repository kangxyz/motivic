/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalDivisorFaceSupport
public import Motivic.Aglib.RingTheory.Multiplicity.PrincipalEuler.FaceDifference

/-!
# Signed original principal-divisor face coefficients

The support-complete numerator and denominator formulas are subtracted at the
same actual face point. Interchange retains both scalar homology terms. A
literal numerator congruence modulo the face gives exact cancellation, even
when either divisor has no preimage over the point.

The finite-cut and reduced-component regularity conditions are genuine local
geometric inputs, not assumed coefficient identities. Producing these inputs
for the global rational-function family remains separate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsNoetherian P]

/-- Actual local geometric conditions for the complete original divisor-face
coefficient. This record contains no cycle or Euler comparison premise. -/
structure PrincipalFaceConditions (n f : P ⟶ Spec (.of k[X])) (a : k)
    (x : fiber f a) : Prop where
  /-- The original ambient double cut has finite length. -/
  finiteCut : Module.length (P.presheaf.stalk (fiberInclusion f a x))
    ((P.presheaf.stalk (fiberInclusion f a x)) ⧸
      (Ideal.ofList [scalar f a (fiberInclusion f a x)] ⊔
        Ideal.ofList [scalar n 0 (fiberInclusion f a x)])) ≠ ⊤
  /-- No contributing original reduced component is contained in the face. -/
  componentRegular : ∀ (y : fiber (fiberInclusion n 0 ≫ f) a),
    (fiberInclusion (fiberInclusion n 0 ≫ f) a ≫ fiberInclusion n 0) y =
        fiberInclusion f a x →
    ∀ z : genericPoints (fiber n 0),
      IsSMulRegular
        (((fiber n 0).presheaf.stalk (fiberInclusion (fiberInclusion n 0 ≫ f) a y)) ⧸
          (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι.ker.stalk
            (fiberInclusion (fiberInclusion n 0 ≫ f) a y))
        (scalar (fiberInclusion n 0 ≫ f) a
          (fiberInclusion (fiberInclusion n 0 ≫ f) a y))

variable (n d f : P ⟶ Spec (.of k[X])) (a : k) (x : fiber f a)

/-- The actual signed original face-cycle coefficient is the difference of
native face-quotient Euler expressions. Mixed and empty support are included. -/
theorem signed_principal_face_coefficient
    (hn : PrincipalFaceConditions n f a x) (hd : PrincipalFaceConditions d f a x)
    (hc : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar f a (fiberInclusion f a x)))
    (hnr : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar n 0 (fiberInclusion f a x)))
    (hdr : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar d 0 (fiberInclusion f a x))) :
    IntegralCycle.toPoints
        (principalDivisorFaceCycle n f a - principalDivisorFaceCycle d f a)
        (fiberInclusion f a x) =
      Module.principalEuler
          (N := Module.ScalarCokernel (P.presheaf.stalk (fiberInclusion f a x))
            (scalar f a (fiberInclusion f a x))) (scalar n 0 (fiberInclusion f a x)) -
        Module.principalEuler
          (N := Module.ScalarCokernel (P.presheaf.stalk (fiberInclusion f a x))
            (scalar f a (fiberInclusion f a x))) (scalar d 0 (fiberInclusion f a x)) := by
  rw [map_sub, Finsupp.sub_apply,
    principalDivisorFaceCycle_coefficient n f a x hn.finiteCut hn.componentRegular,
    principalDivisorFaceCycle_coefficient d f a x hd.finiteCut hd.componentRegular,
    Module.principalEuler_interchange _ _ hnr hc,
    Module.principalEuler_interchange _ _ hdr hc]

/-- A literal numerator congruent to the denominator modulo the original face
has zero signed coefficient, without deleting either polar contribution. -/
theorem signed_principal_face_coefficient_eq_zero
    (hn : PrincipalFaceConditions n f a x) (hd : PrincipalFaceConditions d f a x)
    (hc : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar f a (fiberInclusion f a x)))
    (hnr : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar n 0 (fiberInclusion f a x)))
    (hdr : IsSMulRegular (P.presheaf.stalk (fiberInclusion f a x))
      (scalar d 0 (fiberInclusion f a x)))
    (r : P.presheaf.stalk (fiberInclusion f a x))
    (hrelation : scalar n 0 (fiberInclusion f a x) =
      scalar d 0 (fiberInclusion f a x) + scalar f a (fiberInclusion f a x) * r) :
    IntegralCycle.toPoints
        (principalDivisorFaceCycle n f a - principalDivisorFaceCycle d f a)
        (fiberInclusion f a x) = 0 := by
  rw [signed_principal_face_coefficient n d f a x hn hd hc hnr hdr, hrelation,
    Module.principalEuler_add_face_mul, sub_self]

end AlgebraicGeometry.FiniteFlatCurve

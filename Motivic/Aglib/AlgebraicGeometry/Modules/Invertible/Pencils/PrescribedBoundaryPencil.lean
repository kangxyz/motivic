/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Actual affine pencils with prescribed scheme-theoretic boundary

The CRT construction produces a function with value one at infinity and the
specified value on the disjoint second boundary. The affine pencil is an actual
closed scheme, with literal endpoint intersection rings and full-ideal boundary
restrictions. No reduction of the boundary is used.

This is the local equation step in the principal-divisor construction. It does
not assert that the affine scheme is proper or finite over a parameter base;
extending its divisor across a compactification remains a separate obligation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.PrescribedBoundaryPencil

variable {R : Type u} [CommRing R]

/-- CRT supplies the actual prescribed function, on the full closed boundaries. -/
theorem exists_boundary_function (I J : Ideal R) (hIJ : IsCoprime I J)
    (r : R ⧸ J) : ∃ h : R, Ideal.Quotient.mk I h = 1 ∧ Ideal.Quotient.mk J h = r := by
  let e := Ideal.quotientInfEquivQuotientProd I J hIJ
  obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective (e.symm (1, r))
  have he : e (Ideal.Quotient.mk (I ⊓ J) h) = (1, r) := by rw [hh]; exact e.apply_symm_apply _
  exact ⟨h, by simpa [e] using congrArg Prod.fst he,
    by simpa [e] using congrArg Prod.snd he⟩

/-- The literal pencil, with its parameter as the polynomial variable. -/
def pencil (a b : R) : R[X] := C a + X * C (b - a)

@[simp] theorem pencil_eval_zero (a b : R) : (pencil a b).eval 0 = a := by
  simp [pencil]

@[simp] theorem pencil_eval_one (a b : R) : (pencil a b).eval 1 = b := by
  simp [pencil]

/-- Equal specified boundary values give a constant polynomial on the entire
scheme-theoretic boundary, including its nilpotents. -/
theorem pencil_map_quotient (I : Ideal R) (a b : R)
    (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b) :
    (pencil a b).map (Ideal.Quotient.mk I) = C (Ideal.Quotient.mk I a) := by
  simp [pencil, ← hab]

/-- If that common value is a unit, the boundary pencil is a unit. -/
theorem pencil_boundary_isUnit (I : Ideal R) (a b : R)
    (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b)
    (ha : IsUnit (Ideal.Quotient.mk I a)) :
    IsUnit ((pencil a b).map (Ideal.Quotient.mk I)) := by
  rw [pencil_map_quotient I a b hab]
  exact ha.map C

/-- A principal relation starting at one has a regular total-space equation,
even over a nonreduced or disconnected ring. This is absolute regularity only. -/
theorem principal_pencil_regular (h : R) : pencil 1 h ∈ nonZeroDivisors R[X] := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
  simp [pencil]

/-- A common invertible value on a nonempty boundary prevents every scalar
member from vanishing identically. This is the componentwise obstruction used
in a geometric-fiber regularity argument. -/
theorem pencil_eval_ne_zero_of_boundary (I : Ideal R) (hI : I ≠ ⊤)
    (a b t : R) (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b)
    (ha : IsUnit (Ideal.Quotient.mk I a)) : (pencil a b).eval t ≠ 0 := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have he : Ideal.Quotient.mk I ((pencil a b).eval t) = Ideal.Quotient.mk I a := by
    simp [pencil, ← hab]
  intro hz
  apply ha.ne_zero
  rw [← he, hz, map_zero]

/-- On an integral fiber component the boundary obstruction proves regularity;
regularity is not added as a premise. -/
theorem pencil_eval_regular_of_boundary [IsDomain R] (I : Ideal R) (hI : I ≠ ⊤)
    (a b t : R) (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b)
    (ha : IsUnit (Ideal.Quotient.mk I a)) : (pencil a b).eval t ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_of_ne_zero (pencil_eval_ne_zero_of_boundary I hI a b t hab ha)

/-- Evaluation of the whole endpoint intersection, not only its reduced points. -/
def endpointEquiv (f : R[X]) (t : R) :
    (R[X] ⧸ Ideal.span {f, X - C t}) ≃ₐ[R] R ⧸ Ideal.span {f.eval t} :=
  (Ideal.quotientEquivAlgOfEq R (J := Ideal.span {X - C t} ⊔ Ideal.span {f})
    (by rw [Ideal.span_insert, sup_comm])).trans <|
    (DoubleQuot.quotQuotEquivQuotSupₐ R _ _).symm.trans <|
      (Ideal.quotientEquivAlg _ _ (quotientSpanXSubCAlgEquiv t) rfl).trans <|
        Ideal.quotientEquivAlgOfEq R (by
          simp only [Ideal.map_span, Set.image_singleton]
          rfl)

/-- The zero endpoint is exactly the original principal closed scheme. -/
def zeroEndpointEquiv (a b : R) :
    (R[X] ⧸ Ideal.span {pencil a b, X - C 0}) ≃ₐ[R] R ⧸ Ideal.span {a} :=
  (endpointEquiv (pencil a b) 0).trans
    (Ideal.quotientEquivAlgOfEq R (by rw [pencil_eval_zero]))

/-- The one endpoint retains the whole principal divisor, including multiplicity. -/
def oneEndpointEquiv (a b : R) :
    (R[X] ⧸ Ideal.span {pencil a b, X - C 1}) ≃ₐ[R] R ⧸ Ideal.span {b} :=
  (endpointEquiv (pencil a b) 1).trans
    (Ideal.quotientEquivAlgOfEq R (by rw [pencil_eval_one]))

/-- The constructed affine family is the actual principal closed subscheme. -/
def familyScheme (a b : R) : Scheme.{u} :=
  Spec (.of (R[X] ⧸ Ideal.span {pencil a b}))

/-- Its literal closed immersion into the affine parameter cylinder. -/
def familyInclusion (a b : R) : familyScheme a b ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {pencil a b})))

instance familyInclusion_isClosedImmersion (a b : R) :
    IsClosedImmersion (familyInclusion a b) :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)

/-- Actual base change of the constructed family, with its complete quotient
ring. This computes categorical pullbacks, not merely pointwise fibers. -/
def familyBaseChangeIso (a b : R) (S : Type u) [CommRing S] (φ : R[X] →+* S) :
    CategoryTheory.Limits.pullback (Spec.map (CommRingCat.ofHom φ)) (familyInclusion a b) ≅
      Spec (.of (S ⧸ Ideal.span {φ (pencil a b)})) := by
  letI : Algebra R[X] S := φ.toAlgebra
  let e : (S ⧸ Ideal.span {φ (pencil a b)}) ≃ₐ[S]
      S ⊗[R[X]] (R[X] ⧸ Ideal.span {pencil a b}) :=
    (Ideal.quotientEquivAlgOfEq S (by
      rw [Ideal.map_span, Set.image_singleton]
      rfl)).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {pencil a b}))
  exact pullbackSpecIso R[X] S (R[X] ⧸ Ideal.span {pencil a b}) ≪≫
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The actual categorical endpoint fiber is the whole specialized zero scheme. -/
def fiberSchemeIso (a b t : R) :
    CategoryTheory.Limits.pullback (Spec.map (CommRingCat.ofHom (evalRingHom t)))
        (familyInclusion a b) ≅
      Spec (.of (R ⧸ Ideal.span {(pencil a b).eval t})) :=
  familyBaseChangeIso a b R (evalRingHom t)

/-- The actual zero fiber, with its unreduced principal scheme structure. -/
def zeroFiberSchemeIso (a b : R) :
    CategoryTheory.Limits.pullback (Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))))
        (familyInclusion a b) ≅ Spec (.of (R ⧸ Ideal.span {a})) :=
  fiberSchemeIso a b 0 ≪≫ Scheme.Spec.mapIso
    (Ideal.quotientEquivAlgOfEq R (I := Ideal.span {(pencil a b).eval 0})
      (J := Ideal.span {a}) (by rw [pencil_eval_zero])).symm.toRingEquiv.toCommRingCatIso.op

/-- The actual one fiber, with its unreduced principal scheme structure. -/
def oneFiberSchemeIso (a b : R) :
    CategoryTheory.Limits.pullback (Spec.map (CommRingCat.ofHom (evalRingHom (1 : R))))
        (familyInclusion a b) ≅ Spec (.of (R ⧸ Ideal.span {b})) :=
  fiberSchemeIso a b 1 ≪≫ Scheme.Spec.mapIso
    (Ideal.quotientEquivAlgOfEq R (I := Ideal.span {(pencil a b).eval 1})
      (J := Ideal.span {b}) (by rw [pencil_eval_one])).symm.toRingEquiv.toCommRingCatIso.op

/-- The whole boundary fiber is empty when the two endpoint values agree and
are invertible there. Scheme-theoretic nilpotents have not been discarded. -/
theorem boundaryFiber_isEmpty (I : Ideal R) (a b : R)
    (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b)
    (ha : IsUnit (Ideal.Quotient.mk I a)) :
    IsEmpty (CategoryTheory.Limits.pullback
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (Ideal.Quotient.mk I))))
      (familyInclusion a b) : Scheme.{u}) := by
  have htop : Ideal.span {(pencil a b).map (Ideal.Quotient.mk I)} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr (pencil_boundary_isUnit I a b hab ha)
  have : Subsingleton ((R ⧸ I)[X] ⧸ Ideal.span
      {(pencil a b).map (Ideal.Quotient.mk I)}) :=
    Ideal.Quotient.subsingleton_iff.mpr htop
  let e := familyBaseChangeIso a b (R ⧸ I)[X]
    (Polynomial.mapRingHom (Ideal.Quotient.mk I))
  refine ⟨fun x => ?_⟩
  have y : PrimeSpectrum ((R ⧸ I)[X] ⧸ Ideal.span
      {(pencil a b).map (Ideal.Quotient.mk I)}) := e.hom x
  exact isEmptyElim y

/-- The zero endpoint intersection scheme is the original whole zero scheme. -/
def zeroEndpointSchemeIso (a b : R) :
    Spec (.of (R[X] ⧸ Ideal.span {pencil a b, X - C 0})) ≅
      Spec (.of (R ⧸ Ideal.span {a})) :=
  Scheme.Spec.mapIso (zeroEndpointEquiv a b).symm.toRingEquiv.toCommRingCatIso.op

/-- The one endpoint intersection scheme is the original whole zero scheme. -/
def oneEndpointSchemeIso (a b : R) :
    Spec (.of (R[X] ⧸ Ideal.span {pencil a b, X - C 1})) ≅
      Spec (.of (R ⧸ Ideal.span {b})) :=
  Scheme.Spec.mapIso (oneEndpointEquiv a b).symm.toRingEquiv.toCommRingCatIso.op

/-- CRT and interpolation together construct the principal pencil fixed at one
on infinity, with the specified second-boundary endpoint. This second boundary
is not claimed to be avoided at intermediate parameters. -/
theorem exists_prescribed_principal_pencil (I J : Ideal R) (hIJ : IsCoprime I J)
    (r : R ⧸ J) : ∃ h : R,
      Ideal.Quotient.mk I h = 1 ∧ Ideal.Quotient.mk J h = r ∧
      (pencil 1 h).map (Ideal.Quotient.mk I) = 1 ∧
      (pencil 1 h).eval 0 = 1 ∧ (pencil 1 h).eval 1 = h ∧
      pencil 1 h ∈ nonZeroDivisors R[X] := by
  obtain ⟨h, hi, hj⟩ := exists_boundary_function I J hIJ r
  refine ⟨h, hi, hj, ?_, pencil_eval_zero _ _, pencil_eval_one _ _,
    principal_pencil_regular h⟩
  simpa using pencil_map_quotient I (1 : R) h (by simpa using hi.symm)

end AlgebraicGeometry.Scheme.PrescribedBoundaryPencil

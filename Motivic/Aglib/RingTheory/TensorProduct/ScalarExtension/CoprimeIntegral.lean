/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.FieldTheory.FiniteExtension.CoprimeTensorField
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleIntegralOfSingletonFiber
public import Motivic.Aglib.AlgebraicGeometry.Scheme.SmoothNormal
public import Motivic.Aglib.RingTheory.Bertini.ClosedPointMovingCoefficients
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Integral scalar extension with the entire original closed fiber retained

A finite separable scalar extension of degree coprime to the residue degree
has a field as its entire closed fiber. The actual scalar projection therefore
has exactly one point above the original mark. For a smooth integral affine
source, the finite étale singleton-fiber criterion proves that the complete
scalar extension remains integral. No component or residue branch is discarded.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Algebra.TensorProduct

universe u

/-- The full scalar-extension fiber algebra, with its original residue-field
scalar structure, is the tensor product of the residue and extension fields. -/
def scalarResidueFiberEquiv
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L] (x : PrimeSpectrum R) :
    x.asIdeal.Fiber (R ⊗[k] L) ≃ₐ[x.asIdeal.ResidueField]
      (x.asIdeal.ResidueField ⊗[k] L) :=
  cancelBaseChange k R x.asIdeal.ResidueField x.asIdeal.ResidueField L

/-- Exactly one point lies above the original mark; the proof identifies the
entire preimage with the spectrum of the actual tensor fiber. -/
theorem existsUnique_prime_over_of_coprime_residueDegree
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L]
    (x : PrimeSpectrum R)
    (h : (Module.finrank k x.asIdeal.ResidueField).Coprime (Module.finrank k L)) :
    ∃! y : PrimeSpectrum (R ⊗[k] L),
      PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x := by
  let e := scalarResidueFiberEquiv k R L x
  have hf := isField_of_coprime_finrank k x.asIdeal.ResidueField L h
  let : Field (x.asIdeal.Fiber (R ⊗[k] L)) := (e.toMulEquiv.isField hf).toField
  let E := PrimeSpectrum.preimageEquivFiber R (R ⊗[k] L) x
  let z : PrimeSpectrum (x.asIdeal.Fiber (R ⊗[k] L)) := ⟨⊥, inferInstance⟩
  let y := E.symm z
  refine ⟨y.val, y.property, ?_⟩
  intro y' hy'
  exact congrArg Subtype.val (E.injective (Subsingleton.elim (E ⟨y', hy'⟩) (E y)))

/-- The original smooth affine domain stays a domain, and its entire original
closed marked fiber consists of one point, under a coprime finite separable
scalar extension. Closedness supplies finiteness of the residue degree. -/
theorem isDomain_and_unique_prime_over_of_coprime_closedPoint
    (k R L : Type u) [Field k] [CommRing R] [IsDomain R] [Field L]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    (h : (Module.finrank k x.asIdeal.ResidueField).Coprime (Module.finrank k L)) :
    IsDomain (R ⊗[k] L) ∧
      ∃! y : PrimeSpectrum (R ⊗[k] L),
        PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x := by
  let := QuadraticIncidence.ClosedPoint.residueField_finite k R x
  have hu := existsUnique_prime_over_of_coprime_residueDegree k R L x h
  obtain ⟨y, hy, hyunique⟩ := hu
  let S := R ⊗[k] L
  let : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  let : Algebra.FinitePresentation k L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale k L := {}
  let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have : AlgebraicGeometry.Etale f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let b : Spec (.of S) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k S))
  have : AlgebraicGeometry.Smooth b := HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)
  have hI : IsIntegral (Spec (.of S)) :=
    Scheme.isIntegral_of_finite_etale_singletonFiber f
      (fun t => (Scheme.normalDomain_stalk_of_smooth_field k b t).1) y
      (fun t ht => hyunique t (ht.trans hy))
  exact ⟨(affine_isIntegral_iff (.of S)).mp hI, ⟨y, hy, hyunique⟩⟩

end Algebra.TensorProduct

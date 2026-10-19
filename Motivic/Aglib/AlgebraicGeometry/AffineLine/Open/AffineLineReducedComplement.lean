/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # The full reduced complement of an open of the affine line -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.AffineLineReducedComplement

variable {k : Type u} [Field k]

/-- The polynomial-spectrum affine line `Spec k[X]` over the coefficient field. -/
abbrev line (k : Type u) [Field k] : Scheme := Spec (.of (Polynomial k))

variable (U : (line k).Opens)

/-- The vanishing ideal of the entire complement, not of a selected finite subset. -/
def complementIdeal : Ideal (Polynomial k) :=
  PrimeSpectrum.vanishingIdeal (U : Set (line k))ᶜ

/-- The actual reduced closed complement. -/
def closedComplement : Scheme := Spec (.of (Polynomial k ⧸ complementIdeal U))

/-- Its literal closed immersion in the polynomial spectrum. -/
def inclusion : closedComplement U ⟶ line k :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (complementIdeal U)))

/-- The actual structure map to the coefficient field. -/
def projection : closedComplement U ⟶ Spec (.of k) :=
  inclusion U ≫ polynomialProjection (.of k)

instance : IsClosedImmersion (inclusion U) := by
  apply IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (complementIdeal U)))
  exact Ideal.Quotient.mk_surjective

instance : IsReduced (closedComplement U) := by
  have : _root_.IsReduced (Polynomial k ⧸ complementIdeal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp
      (PrimeSpectrum.isRadical_vanishingIdeal _)
  exact inferInstanceAs (IsReduced (Spec (.of (Polynomial k ⧸ complementIdeal U))))

/-- Literal equality of the image with the complete set-theoretic complement. -/
theorem range_inclusion : Set.range (inclusion U) = (U : Set (line k))ᶜ := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (complementIdeal U))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, complementIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact U.isOpen.isClosed_compl.closure_eq

/-- A generic-containing open contains a nonzero-polynomial principal open. -/
theorem exists_nonzero_basicOpen
    (hU : genericPoint (line k) ∈ U) :
    ∃ f : Polynomial k, f ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ U := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen _ hU
  refine ⟨f, ?_, hle⟩
  rw [genericPoint_eq_bot_of_affine] at hf
  simpa using hf

/-- Every defining polynomial of a principal open contained in `U` vanishes on
its entire complement. -/
theorem mem_complementIdeal {f : Polynomial k}
    (hf : PrimeSpectrum.basicOpen f ≤ U) : f ∈ complementIdeal U := by
  rw [complementIdeal, PrimeSpectrum.mem_vanishingIdeal]
  intro x hx
  by_contra h
  exact hx (hf h)

/-- A nonzero polynomial in the complement ideal makes its quotient a finite
vector space over the coefficient field. -/
theorem finite_quotient_of_basicOpen {f : Polynomial k} (hf : f ≠ 0)
    (hD : PrimeSpectrum.basicOpen f ≤ U) :
    Module.Finite k (Polynomial k ⧸ complementIdeal U) := by
  have hfin : Module.Finite k (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis hf).basis
  have : Module.Finite k (Polynomial k ⧸ Ideal.span {f}) := hfin
  have hle : Ideal.span {f} ≤ complementIdeal U :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (mem_complementIdeal U hD))
  exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ k hle).toLinearMap
    (Ideal.Quotient.factor_surjective hle)

/-- Finiteness of the actual full reduced complement is derived from generic
containment, rather than being an assumption. -/
theorem finite_projection (hU : genericPoint (line k) ∈ U) : IsFinite (projection U) := by
  obtain ⟨f, hf, hD⟩ := exists_nonzero_basicOpen U hU
  have := finite_quotient_of_basicOpen U hf hD
  change IsFinite (Spec.map _ ≫ Spec.map _)
  rw [← Spec.map_comp]
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap k (Polynomial k ⧸ complementIdeal U)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The original open is an actual smooth separated finite-type site object. -/
def openObject : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (U.ι ≫ polynomialProjection (.of k))

/-- The structural map from the original open to the actual affine-line object. -/
def openInclusion : openObject U ⟶ SmoothSite.affineLine (.of k) :=
  SmoothSite.homMk U.ι rfl

@[simp] theorem openObject_left : (openObject U).left = U.toScheme := rfl

@[simp] theorem openInclusion_left : (openInclusion U).left = U.ι := rfl

@[simp] theorem openObject_hom :
    (openObject U).hom = U.ι ≫ polynomialProjection (.of k) := rfl

end AlgebraicGeometry.Scheme.AffineLineReducedComplement

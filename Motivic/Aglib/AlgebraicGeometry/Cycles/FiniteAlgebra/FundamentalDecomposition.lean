/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance

/-!
# Fundamental cycles of finite algebras
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
universe u
section
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
variable (k : Type u) [Field k]
section FiniteAlgebra

variable {k} {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R]

/-- The canonical field structure on the quotient by the selected maximal ideal. -/
local instance _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.quotientField (p : MaximalSpectrum
    R) : Field (R ⧸
    p.asIdeal) :=
  Ideal.Quotient.field p.asIdeal

/-- Every quotient branch is included by the literal quotient homomorphism. -/
def _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.quotientMap (p : MaximalSpectrum R) : Spec (.of (R
    ⧸ p.asIdeal)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))

open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra

instance (p : MaximalSpectrum R) : IsClosedImmersion (quotientMap p) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The generic point of the actual maximal quotient maps to its original prime. -/
theorem _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.quotientMap_genericPoint (p : MaximalSpectrum
    R) :
    quotientMap p (genericPoint (Spec (.of (R ⧸ p.asIdeal)))) = p.toPrimeSpectrum := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk p.asIdeal)
    (genericPoint (Spec (.of (R ⧸ p.asIdeal)))).asIdeal = p.asIdeal
  let q : PrimeSpectrum (R ⧸ p.asIdeal) := genericPoint (Spec (.of (R ⧸ p.asIdeal)))
  have hb : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  rw [hb]
  exact Ideal.mk_ker

/-- The actual reduced closed support of a quotient branch. -/
def _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.quotientSupport (p : MaximalSpectrum R) :
    IntegralClosedSubscheme (Spec (.of R)) :=
  ⟨(quotientMap p).ker, IsIntegral.of_isIso (quotientMap p).toImage⟩

@[simp] theorem _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.quotientSupport_point (p :
    MaximalSpectrum R) :
    (quotientSupport p).point = p.toPrimeSpectrum := by
  exact (imageι_genericPoint (quotientMap p)).trans (quotientMap_genericPoint p)

include k in
/-- Every point of a finite algebra is an actual component generic point. -/
theorem _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.finiteAlgebra_mem_genericPoints (p :
    PrimeSpectrum R) :
    p ∈ genericPoints (Spec (.of R)) := by
  let : IsArtinianRing R := .of_finite k R
  have h : genericPoints (Spec (.of R)) = Set.univ := by
    rw [← genericPoints.closure (α := Spec (.of R))]
    exact (isClosed_discrete _).closure_eq.symm
  exact Set.eq_univ_iff_forall.mp h p

/-- The original scheme's stalk length is the literal localization length. -/
theorem _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.affine_genericMultiplicity (p :
    MaximalSpectrum R) :
    genericMultiplicity ⟨p.toPrimeSpectrum, finiteAlgebra_mem_genericPoints (k := k) _⟩ =
      (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)).toNat := by
  unfold genericMultiplicity
  rw [ringLength_eq_of_ringEquiv
    (Spec.stalkIso (.of R) p.toPrimeSpectrum).commRingCatIsoToRingEquiv]
  rfl

/-- The full fundamental cycle includes every maximal quotient with its
original local length. -/
theorem _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.fundamentalCycle_affine_eq_sum :
    let : IsArtinianRing R := .of_finite k R
    let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
    fundamentalCycle (Spec (.of R)) =
      ∑ p : MaximalSpectrum R, Finsupp.single (quotientSupport p)
        ((Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat : ℤ) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  apply IntegralCycle.toPoints_injective
  rw [toPoints_fundamentalCycle, map_sum]
  simp only [IntegralCycle.toPoints_single, quotientSupport_point]
  ext q
  let p : MaximalSpectrum R := IsArtinianRing.primeSpectrumEquivMaximalSpectrum q
  have hp : p.toPrimeSpectrum = q := rfl
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single p]
  · rw [← hp, Finsupp.single_eq_same, fundamentalPointCycle_apply,
      dite_eq_left (finiteAlgebra_mem_genericPoints (k := k) _),
      affine_genericMultiplicity (k := k)]
  · intro r _ hr
    exact Finsupp.single_eq_of_ne (fun h => hr
      (MaximalSpectrum.toPrimeSpectrum_injective (h.symm.trans hp.symm)))
  · simp



end FiniteAlgebra
end

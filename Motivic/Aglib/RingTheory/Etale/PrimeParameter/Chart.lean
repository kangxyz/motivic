/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.PrimeParameterDifferential
public import Motivic.Aglib.RingTheory.Etale.PrescribedResidueCoordinate
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity

/-! # Actual prime parameters in smooth affine etale charts -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Module TensorProduct KaehlerDifferential
universe u
namespace Algebra

/-- Smooth affine regularity supplies the actual localized regular local ring. -/
theorem isRegularLocalRing_atPrime_of_smooth
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hf : AlgebraicGeometry.Smooth f :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
      ((RingHom.smooth_algebraMap (R := k) (S := R)).mpr inferInstance)
  let : IsRegularLocalRing ((Spec (.of R)).presheaf.stalk ⟨p, inferInstance⟩) :=
    Scheme.smoothFieldRegularity k _ f hf _
  let e : Localization.AtPrime p ≃+*
      ((Spec (.of R)).presheaf.stalk ⟨p, inferInstance⟩) :=
    (StructureSheaf.stalkIso R ⟨p, inferInstance⟩).toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- A positive-local-rank prime of a smooth affine algebra over a perfect field
has an actual original prime element retained in an etale polynomial chart. -/
theorem exists_prime_parameter_etale_chart
    (k R : Type u) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Smooth k R] (p : Ideal R) [p.IsPrime]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ f ∈ p, ∃ (d : ℕ) (g : Fin d → R) (i : Fin d), g i = f ∧
      ∃ r ∉ p, ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) g).toRingHom).Etale := by
  let := isRegularLocalRing_atPrime_of_smooth k R p
  obtain ⟨f, hfp, hf⟩ := exists_prime_residue_differential_ne_zero k R p hpos
  exact ⟨f, hfp, exists_etale_polynomial_map_containing_of_residue_differential_ne_zero
    k R p f hf⟩

end Algebra

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Integral closedness from actual scheme stalks

An affine-open section ring that is a domain is integrally closed whenever
its actual scheme stalks are integrally closed. Integral closedness and the
domain property also pass to the actual stalks of open subschemes. These
lemmas do not impose global integrality on the ambient scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Integral closedness of actual stalks passes to open subschemes. -/
theorem isIntegrallyClosed_stalk_open_of_stalks {X : Scheme.{u}}
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (x : U) : IsIntegrallyClosed (U.toScheme.presheaf.stalk x) := by
  have := hX x.1
  exact IsIntegrallyClosed.of_equiv (U.stalkIso x).symm.commRingCatIsoToRingEquiv

/-- Domain and integral-closedness properties pass to actual open-subscheme stalks. -/
theorem normalDomain_stalk_open_of_stalks {X : Scheme.{u}}
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (x : U) :
    IsDomain (U.toScheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (U.toScheme.presheaf.stalk x) := by
  have := (hX x.1).1
  exact ⟨(U.stalkIso x).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _,
    isIntegrallyClosed_stalk_open_of_stalks (fun y ↦ (hX y).2) U x⟩

/-- If all stalks are integrally closed, any affine-open section ring that
is a domain is integrally closed. -/
theorem isIntegrallyClosed_sections_of_stalks {X : Scheme.{u}}
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)] :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ _
  let y : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  let x : X := hU.fromSpec y
  have hx : x ∈ U := (hU.isoSpec.inv y).2
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    hU.isLocalization_stalk' y hx
  have := hX x
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime p)).toRingEquiv

/-- Every nonempty affine open of an integral scheme with integrally closed
stalks has a normal-domain section ring. -/
theorem normalDomain_sections_of_isIntegral_of_stalks {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsDomain Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) :=
  ⟨inferInstance, isIntegrallyClosed_sections_of_stalks hX hU⟩

end AlgebraicGeometry.Scheme

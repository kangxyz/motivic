/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Motivic.RingTheory.Smooth.Normal
public import Motivic.AlgebraicGeometry.Scheme.NormalStalks

/-!
# Normal-domain stalks of schemes smooth over arbitrary fields

Smoothness of the affine chart ring over the field of global sections of
`Spec k` proves that every actual source stalk is an integrally closed domain.
No integrality, connectedness, nonemptiness, finite-type, or perfectness
hypothesis is imposed on the smooth source. For integral open pieces this
also proves normality of their nonempty affine section rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

/-- Every actual stalk of a scheme smooth over any field is a normal domain. -/
theorem normalDomain_stalk_of_smooth_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let := ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField
  have e : U ≤ f ⁻¹ᵁ ⊤ := by simp
  let := (f.appLE ⊤ U e).hom.toAlgebra
  have : Algebra.Smooth Γ(Spec (.of k), ⊤) Γ(X, U) :=
    (f.smooth_appLE (isAffineOpen_top _) hU e).toAlgebra
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨hD, hN⟩ := normalDomain_localizationAtPrime_of_smooth_field
    Γ(Spec (.of k), ⊤) Γ(X, U) p
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    hU.isLocalization_stalk ⟨x, hx⟩
  let E := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p) (X.presheaf.stalk x)
  exact ⟨E.symm.toRingEquiv.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv E.toRingEquiv⟩

/-- Every domain affine section ring of a scheme smooth over a field is integrally closed. -/
theorem isIntegrallyClosed_sections_of_smooth_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    {U : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)] :
    IsIntegrallyClosed Γ(X, U) :=
  isIntegrallyClosed_sections_of_stalks (fun x ↦ (normalDomain_stalk_of_smooth_field k f x).2) hU

/-- The nonempty affine sections of an integral open piece of a smooth scheme
are normal domains, without global integrality of the smooth scheme. -/
theorem normalDomain_sections_open_of_smooth_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    (V : X.Opens) [IsIntegral V.toScheme]
    {U : V.toScheme.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsDomain Γ(V.toScheme, U) ∧ IsIntegrallyClosed Γ(V.toScheme, U) :=
  normalDomain_sections_of_isIntegral_of_stalks
    (isIntegrallyClosed_stalk_open_of_stalks
      (fun x ↦ (normalDomain_stalk_of_smooth_field k f x).2) V) hU

end Motivic

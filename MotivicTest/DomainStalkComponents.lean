/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Scheme.DomainStalkComponents
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Consumers of the open-component decomposition

These consumers include arbitrary Noetherian schemes with domain stalks,
empty schemes, and the disconnected spectrum of a product of two arbitrary
fields. No perfectness or global domain hypothesis is imposed on that product.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MotivicTest.DomainStalkComponents

/-- Every component is an actual integral open subscheme. -/
theorem actual_open_integral_component (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsIntegral (Scheme.domainStalkComponentOpen hX Z hZ).toScheme :=
  Scheme.isIntegral_domainStalkComponentOpen hX Z hZ

/-- An empty scheme has no irreducible components to index; no component is fabricated. -/
theorem empty_components (X : Scheme.{u}) [IsEmpty X] :
    irreducibleComponents X = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro Z hZ
  obtain ⟨x, _⟩ := hZ.1.1
  exact isEmptyElim x

/-- The domain-stalk hypothesis itself permits an empty scheme. -/
theorem empty_domain_stalks (X : Scheme.{u}) [IsEmpty X] :
    ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x ↦ isEmptyElim x

/-- Every localization of a product of two fields at a prime is a domain. -/
theorem product_field_localizations (k : Type u) [Field k] (p : PrimeSpectrum (k × k)) :
    IsDomain (Localization.AtPrime p.asIdeal) := by
  let := (IsArtinianRing.isField_of_isReduced_of_isLocalRing
    (Localization.AtPrime p.asIdeal)).toField
  infer_instance

/-- The spectrum of a disconnected product has disjoint components. -/
theorem product_field_components (k : Type u) [Field k]
    {Z W : Set (PrimeSpectrum (k × k))}
    (hZ : Z ∈ irreducibleComponents (PrimeSpectrum (k × k)))
    (hW : W ∈ irreducibleComponents (PrimeSpectrum (k × k)))
    {x : PrimeSpectrum (k × k)} (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W :=
  _root_.PrimeSpectrum.irreducibleComponents_eq_of_mem_of_domain_localizations
    (product_field_localizations k) hZ hW hxZ hxW

/-- The decomposition is a finite cover by integral open subschemes. -/
theorem finite_integral_cover (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    Finite (Scheme.domainStalkComponentOpenCover X hX).I₀ ∧
      ∀ i, IsIntegral ((Scheme.domainStalkComponentOpenCover X hX).X i) :=
  ⟨inferInstance, fun _ ↦ inferInstance⟩

/-- The actual spectrum of a disconnected field product has domain stalks. -/
theorem product_field_stalks (k : Type u) [Field k] (x : PrimeSpectrum (k × k)) :
    IsDomain ((Spec (.of (k × k))).presheaf.stalk x) := by
  have : IsDomain (Localization.AtPrime x.asIdeal) := product_field_localizations k x
  exact (Spec.stalkIso (.of (k × k)) x).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

/-- Even for the disconnected spectrum of two fields, the actual open components
are integral; the original scheme is never assumed integral. -/
theorem product_field_open_components (k : Type u) [Field k]
    (Z : Set (Spec (.of (k × k)))) (hZ : Z ∈ irreducibleComponents (Spec (.of (k × k)))) :
    IsIntegral (Scheme.domainStalkComponentOpen (product_field_stalks k) Z hZ).toScheme :=
  Scheme.isIntegral_domainStalkComponentOpen (product_field_stalks k) Z hZ

/-- In the empty case the actual component-cover index type is empty. -/
theorem empty_cover_index (X : Scheme.{u}) [IsNoetherian X] [IsEmpty X] :
    IsEmpty (Scheme.domainStalkComponentOpenCover X (empty_domain_stalks X)).I₀ := by
  refine ⟨fun Z ↦ ?_⟩
  obtain ⟨x, _⟩ := Z.2.1.1
  exact isEmptyElim x

end MotivicTest.DomainStalkComponents

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Localization.DomainComponents
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Open integral components of schemes with domain stalks

Domain stalks imply that distinct irreducible components are disjoint. For a
Noetherian scheme these components are clopen, so each carries its actual
open-subscheme structure. Domain stalks also imply reducedness; consequently
these open component schemes are integral. The original scheme need not be
connected or nonempty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme all of whose stalks are domains is reduced. -/
theorem isReduced_of_domain_stalks (X : Scheme.{u})
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    have := hX x
    infer_instance
  exact isReduced_of_isReduced_stalk X

/-- Prime localizations of an affine-open section ring are domains when the
ambient scheme has domain stalks. -/
theorem isDomain_localizationAtPrime_of_domain_stalks
    {X : Scheme.{u}} (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    IsDomain (Localization.AtPrime p.asIdeal) := by
  let x : X := hU.fromSpec p
  have hx : x ∈ U := (hU.isoSpec.inv p).2
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk' p hx
  have : IsDomain (X.presheaf.stalk x) := hX x
  exact (IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (X.presheaf.stalk x)).toRingEquiv.toMulEquiv.isDomain _

/-- Two irreducible components that meet are equal if every stalk is a domain. -/
theorem irreducibleComponents_eq_of_mem_of_domain_stalks
    {X : Scheme.{u}} (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hW : W ∈ irreducibleComponents X) {x : X} (hxZ : x ∈ Z) (hxW : x ∈ W) :
    Z = W := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have hxrange : x ∈ Set.range hU.fromSpec := hU.range_fromSpec.symm ▸ hxU
  obtain ⟨p, hp⟩ := hxrange
  have hpZ : p ∈ hU.fromSpec ⁻¹' Z := by
    change hU.fromSpec p ∈ Z
    rwa [hp]
  have hpW : p ∈ hU.fromSpec ⁻¹' W := by
    change hU.fromSpec p ∈ W
    rwa [hp]
  have hZ' := preimage_mem_irreducibleComponents hZ hU.fromSpec.isOpenEmbedding
    ⟨x, hxZ, ⟨p, hp⟩⟩
  have hW' := preimage_mem_irreducibleComponents hW hU.fromSpec.isOpenEmbedding
    ⟨x, hxW, ⟨p, hp⟩⟩
  have heq : hU.fromSpec ⁻¹' Z = hU.fromSpec ⁻¹' W :=
    _root_.PrimeSpectrum.irreducibleComponents_eq_of_mem_of_domain_localizations
      (isDomain_localizationAtPrime_of_domain_stalks hX hU) hZ' hW' hpZ hpW
  have hclosureZ := closure_image_preimage_of_isPreirreducible hU.fromSpec
    hU.fromSpec.isOpenEmbedding.isOpenMap Z ⟨p, hpZ⟩ hZ.1.2
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have hclosureW := closure_image_preimage_of_isPreirreducible hU.fromSpec
    hU.fromSpec.isOpenEmbedding.isOpenMap W ⟨p, hpW⟩ hW.1.2
    (isClosed_of_mem_irreducibleComponents W hW)
  rw [← hclosureZ, ← hclosureW, heq]

/-- The irreducible components of a scheme with domain stalks are pairwise disjoint. -/
theorem pairwiseDisjoint_irreducibleComponents_of_domain_stalks
    {X : Scheme.{u}} (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    (irreducibleComponents X).PairwiseDisjoint id := by
  intro Z hZ W hW hZW
  apply Set.disjoint_left.mpr
  intro x hxZ hxW
  exact hZW (irreducibleComponents_eq_of_mem_of_domain_stalks hX hZ hW hxZ hxW)

/-- In a Noetherian scheme with domain stalks, each irreducible component is clopen. -/
theorem isClopen_irreducibleComponent_of_domain_stalks
    {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsClopen Z := by
  have hcompl : Zᶜ = ⋃₀ (irreducibleComponents X \ {Z}) := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      simpa only [Set.mem_singleton_iff] using
        fun h : irreducibleComponent x = Z ↦ hx (h ▸ mem_irreducibleComponent)
    · rintro ⟨W, ⟨hW, hWZ⟩, hxW⟩ hxZ
      exact hWZ (Set.mem_singleton_iff.mpr
        (irreducibleComponents_eq_of_mem_of_domain_stalks hX hW hZ hxW hxZ))
  refine ⟨isClosed_of_mem_irreducibleComponents Z hZ, ?_⟩
  rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
  exact (finite_irreducibleComponents_of_isNoetherian (X := X)).sdiff.isClosed_biUnion
    fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1

/-- The genuine open subscheme associated to an irreducible component. -/
def domainStalkComponentOpen {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : X.Opens :=
  ⟨Z, (isClopen_irreducibleComponent_of_domain_stalks hX hZ).2⟩

/-- Its underlying open set is precisely the specified component. -/
@[simp] theorem coe_domainStalkComponentOpen {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    (domainStalkComponentOpen hX Z hZ : Set X) = Z := rfl

/-- Open irreducible components of a Noetherian scheme with domain stalks are integral. -/
theorem isIntegral_domainStalkComponentOpen {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsIntegral (domainStalkComponentOpen hX Z hZ).toScheme := by
  have : IsReduced X := isReduced_of_domain_stalks X hX
  have : IrreducibleSpace (domainStalkComponentOpen hX Z hZ).toScheme :=
    Subtype.irreducibleSpace hZ.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The component's actual open immersion has the prescribed topological image. -/
theorem range_domainStalkComponentOpen_ι {X : Scheme.{u}} [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    Set.range (domainStalkComponentOpen hX Z hZ).ι = Z :=
  (domainStalkComponentOpen hX Z hZ).range_ι

/-- The actual open irreducible components cover the scheme. The index type is
precisely its irreducible components, so it is empty when the scheme is empty. -/
def domainStalkComponentOpenCover (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) : X.OpenCover where
  I₀ := irreducibleComponents X
  X Z := (domainStalkComponentOpen hX Z.1 Z.2).toScheme
  f Z := (domainStalkComponentOpen hX Z.1 Z.2).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    exact ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      ⟨⟨x, mem_irreducibleComponent⟩, rfl⟩⟩

/-- The actual component cover has a finite index type. -/
instance finite_domainStalkComponentOpenCover_index
    (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    Finite (domainStalkComponentOpenCover X hX).I₀ :=
  (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype

/-- Every member of the finite component cover is integral. -/
instance isIntegral_domainStalkComponentOpenCover_obj
    (X : Scheme.{u}) [IsNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : (domainStalkComponentOpenCover X hX).I₀) :
    IsIntegral ((domainStalkComponentOpenCover X hX).X Z) :=
  isIntegral_domainStalkComponentOpen hX Z.1 Z.2

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.SectionLifting.Basic
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.Principal
public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections

/-!
# One Serre bound on all principal base neighborhoods

The actual H¹ of the actual twisted kernel localizes to zero. Exact open
restriction then gives genuine section lifting on the inverse-image open,
without regarding that open as closed in the original projective space.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
namespace AlgebraicGeometry.Scheme.Cohomology

/-- Vanishing of native cohomology survives restriction to the inverse
image of any principal base open, by actual module localization. -/
theorem cohomology_restrict_principal_subsingleton
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (r : R) (q : ℕ)
    [Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)] :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme
        (M.restrict (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι)) q) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let V := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let := moduleHPrimeModuleOfHom X α M q ⊤
  let := moduleHPrimeModuleOfHom X α M q V
  let : Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) q ⊤) :=
    (moduleHPrimeTopLinearEquivOfHom X α M q).injective.subsingleton
  let ρ := moduleHPrimeRestrictionOfHom X α M q
    (homOfLE (show V ≤ ⊤ from le_top))
  let : IsLocalizedModule.Away r ρ :=
    moduleHPrimeRestriction_isLocalizedModule_principal f M r q
  let : Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) q V) :=
    IsLocalizedModule.subsingleton_of_subsingleton (Submonoid.powers r) ρ
  exact (moduleHPrimeOpenLinearEquiv X α M V q).symm.injective.subsingleton

/-- Surjectivity on the restricted scheme is surjectivity of the original
section map on the image open, through the native section comparison. -/
theorem sections_surjective_of_restrict_top {X : Scheme.{u}} (V : X.Opens)
    {M N : X.Modules} (a : M ⟶ N)
    (ha : Function.Surjective (((Modules.restrictFunctor V.ι).map a).app ⊤)) :
    Function.Surjective (a.app V) := by
  have hs : Function.Surjective (a.app V.ι.opensRange) := by
    let E := Modules.restrictedSectionsIso V.ι
    intro s
    obtain ⟨t, ht⟩ := ha ((E.app N).inv s)
    refine ⟨(E.app M).hom t, ?_⟩
    have hn := congrArg (fun f => f t) (E.hom.naturality a)
    change (E.app N).hom ((((Modules.restrictFunctor V.ι).map a).app ⊤) t) =
      a.app V.ι.opensRange ((E.app M).hom t) at hn
    rw [ht] at hn
    exact hn.symm.trans (ConcreteCategory.congr_hom (E.app N).inv_hom_id s)
  have hV : V.ι.opensRange = V := Scheme.Opens.opensRange_ι V
  exact Eq.mp (congrArg (fun W : X.Opens => Function.Surjective (a.app W)) hV) hs

/-- The same original Serre bound lifts sections over every principal base
neighborhood. Both the twist and its quotient map are the original ones
restricted to that open; no projective-space re-identification is assumed. -/
theorem projective_coherentQuotient_eventually_principal_sections_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M Q : (ProjectiveSpace R ι).Modules}
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M)
    (hQ : affineLocallyFiniteType (ProjectiveSpace R ι) Q)
    (π : M ⟶ Q) [Epi π] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      Function.Surjective
        (((Modules.restrictFunctor ((toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).map
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
            (twistingSheaf R ι d)).map π)).app ⊤) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have hK : affineLocallyFiniteType (ProjectiveSpace R ι) (kernel π) :=
    (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_kernel π hM hQ
  obtain ⟨B, hB⟩ := projectiveSerreVanishing R ι n e (kernel π) hK
  refine ⟨B, fun d hd r => ?_⟩
  let T := moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)
  let S := (ShortComplex.kernelSequence π).map T
  have hS : S.ShortExact := tensor_shortExact_finiteLocallyFree
    (twistingSheaf R ι d) (ShortComplex.kernelSequence π)
    { exact := ShortComplex.kernelSequence_exact π, epi_g := ‹Epi π› }
  have hTK := twistingTensor_affineLocallyFiniteType R ι d (kernel π) hK
  let : S.X₁.IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun A a _ => (hTK A a).1)
  let : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace R ι) S.X₁) 1) := hB d hd 1 (by decide)
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf V.toScheme (S.map (Modules.restrictFunctor V.ι)).X₁) 1) :=
    cohomology_restrict_principal_subsingleton (toSpec R ι) S.X₁ r 1
  exact globalSections_surjective_of_h1_zero V.toScheme
    (S.map (Modules.restrictFunctor V.ι)) (hS.map_of_exact _)

/-- Original section maps on principal inverse-image opens, with a uniform bound. -/
theorem projective_coherentQuotient_eventually_principal_app_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M Q : (ProjectiveSpace R ι).Modules}
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M)
    (hQ : affineLocallyFiniteType (ProjectiveSpace R ι) Q)
    (π : M ⟶ Q) [Epi π] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      Function.Surjective
        (((moduleTensorLeftFunctor (ProjectiveSpace R ι)
            (twistingSheaf R ι d)).map π).app
              ((toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r)) := by
  obtain ⟨B, hB⟩ := projective_coherentQuotient_eventually_principal_sections_surjective
    R ι n e hM hQ π
  exact ⟨B, fun d hd r => sections_surjective_of_restrict_top _ _ (hB d hd r)⟩

end AlgebraicGeometry.Scheme.Cohomology

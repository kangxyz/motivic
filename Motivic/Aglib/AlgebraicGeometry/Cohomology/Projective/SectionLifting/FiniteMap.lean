/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.SectionLifting.PrincipalGraphSections
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree
public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology

/-! # Section lifting along finite maps to projective space -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.Cohomology

/-- An affine direct image preserves the given coherent epimorphism, using
vanishing of its actual coherent kernel on affine inverse-image opens. -/
theorem affinePushforward_coherent_epi {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [IsAffineHom f] {M N : X.Modules}
    (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N)
    (π : M ⟶ N) [Epi π] : Epi ((Modules.pushforward f).map π) := by
  have hK : affineLocallyFiniteType X (kernel π) :=
    (affineLocallyFiniteType X).prop_kernel π hM hN
  let : (kernel π).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun A a _ => (hK A a).1)
  have hs (V : Y.Opens) (hV : IsAffineOpen V) :
      Function.Surjective (π.app (f ⁻¹ᵁ V)) := by
    let W := f ⁻¹ᵁ V
    let : IsAffine W.toScheme := hV.preimage f
    let S := ShortComplex.kernelSequence π
    have hS : S.ShortExact :=
      { exact := ShortComplex.kernelSequence_exact π, epi_g := ‹Epi π› }
    let : Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf W.toScheme (S.map (Modules.restrictFunctor W.ι)).X₁) 1) :=
      subsingleton_moduleAddSheafH_of_isAffine ((kernel π).restrict W.ι) 0
    exact sections_surjective_of_restrict_top W π
      (globalSections_surjective_of_h1_zero W.toScheme
        (S.map (Modules.restrictFunctor W.ι)) (hS.map_of_exact _))
  let p := (Modules.pushforward f).map π
  let g := (_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map p.val
  have hg : TopCat.Presheaf.IsLocallySurjective g := by
    apply (TopCat.Presheaf.isLocallySurjective_iff g).mpr
    intro V s y hy
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    obtain ⟨t, ht⟩ := hs W hW (((Modules.pushforward f).obj N).val.map (homOfLE hWV).op s)
    exact ⟨W, hWV, ⟨t, ht⟩, hyW⟩
  let : Epi ((SheafOfModules.toSheaf Y.ringCatSheaf).map p) :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map p)).mp hg
  exact Functor.epi_of_epi_map (SheafOfModules.toSheaf Y.ringCatSheaf) inferInstance

/-- The actual twisted quotient section map along a finite projective-space map. -/
theorem finite_coherentQuotient_eventually_principal_app_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C : Scheme.{u}} [IsLocallyNoetherian C] (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
    {M N : C.Modules}
    (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (π : M ⟶ N) [Epi π] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      Function.Surjective
        (((Modules.pushforward k).map
          ((moduleTensorLeftFunctor C ((Modules.pullback k).obj
            (twistingSheaf R ι d))).map π)).app V) := by
  let : Epi ((Modules.pushforward k).map π) := affinePushforward_coherent_epi k hM hN π
  have hM' := FiniteMorphism.affineLocallyFiniteType_pushforward k hM
  have hN' := FiniteMorphism.affineLocallyFiniteType_pushforward k hN
  obtain ⟨B, hB⟩ := projective_coherentQuotient_eventually_principal_app_surjective
    R ι n e hM' hN' ((Modules.pushforward k).map π)
  refine ⟨B, fun d hd r s => ?_⟩
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let E := twistingSheaf R ι d
  let eM := projectionFormulaIso k E M
  let eN := projectionFormulaIso k E N
  obtain ⟨t, ht⟩ := hB d hd r (eN.inv.app V s)
  refine ⟨eM.hom.app V t, ?_⟩
  have h := (projectionFormulaNatIso k E).hom.naturality π
  have hh := congrArg (fun f => f.app V t) h
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hh
  change eN.hom.app V
    (((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map
      ((Modules.pushforward k).map π)).app V t) = _ at hh
  rw [ht] at hh
  have hinv : eN.hom.app V (eN.inv.app V s) = s := by
    simpa only [Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Modules.Hom.id_app, ConcreteCategory.id_apply] using
      congrArg (fun f => f.app V s) eN.inv_hom_id
  exact hh.symm.trans hinv

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- Whole-boundary lifting along a finite map, without a closed projective embedding. -/
theorem finite_boundaryRestriction_eventually_principal_app_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
    (i : Z ⟶ C) [IsClosedImmersion i]
    (G : C.Modules) (hG : affineLocallyFiniteType C G) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      Function.Surjective (((Modules.pushforward k).map
        (boundaryRestriction i ((Modules.pullback k).obj
          (ProjectiveSpace.twistingSheaf R ι d)) G)).app V) := by
  let π := (pullbackPushforwardAdjunction i).unit.app G
  let : Epi π := pullbackPushforwardUnit_epi_of_closedImmersion i G
  have hQ := FiniteMorphism.affineLocallyFiniteType_pushforward i
    (affineLocallyFiniteType_pullback i hG)
  obtain ⟨B, hB⟩ := Cohomology.finite_coherentQuotient_eventually_principal_app_surjective
    R ι n e k hG hQ π
  refine ⟨B, fun d hd r => ?_⟩
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have he := ConcreteCategory.bijective_of_isIso
    (((Modules.pushforward k).map
      (closedImmersionProjectionFormulaIso i ((Modules.pullback k).obj
        (ProjectiveSpace.twistingSheaf R ι d)) ((Modules.pullback i).obj G)).hom).app V)
  dsimp only
  intro s
  obtain ⟨t, ht⟩ := he.surjective s
  obtain ⟨t₀, hr⟩ := hB d hd r t
  refine ⟨t₀, ?_⟩
  dsimp only [boundaryRestriction]
  rw [Functor.map_comp, Modules.Hom.comp_app]
  exact (congrArg (fun z => ((Modules.pushforward k).map
    (closedImmersionProjectionFormulaIso i ((Modules.pullback k).obj
      (ProjectiveSpace.twistingSheaf R ι d)) ((Modules.pullback i).obj G)).hom).app V z)
        hr).trans ht
end AlgebraicGeometry.Scheme.CoherentGraph


module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.SameFrameRelativeSectionMaps
/-! # One actual principal shrink supplies all relative section pairs -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- One shrink of the original base constructs all boundary twist frames, and those same
frames supply actual Serre pairs on every affine source mapping to the retained boundary.
The finite boundary may be nonflat or nonreduced; no source-dependent shrink occurs. -/
theorem exists_principal_uniform_relative_section_maps
    (k : Type u) [CommRing k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (x : Spec (.of k)) :
    ∃ r : k, x ∈ PrimeSpectrum.basicOpen r ∧
      let U := (g ≫ toSpec k ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
      ∃ eZ : (d : ℕ) → (Modules.pullback (U.ι ≫ g)).obj (twistingSheaf k ι (d : ℤ)) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf,
      ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (f : k →+* R)
        {C W : Scheme.{u}} [IsLocallyNoetherian C]
        (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
        (z : W ⟶ C) [IsClosedImmersion z]
        (b : W ⟶ U.toScheme)
        (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ (U.ι ≫ g))
        (M N : C.Modules) (_hM : affineLocallyFiniteType C M) (_hN : affineLocallyFiniteType C N)
        (eM : (Modules.pullback z).obj M ≅ SheafOfModules.unit W.ringCatSheaf)
        (eN : (Modules.pullback z).obj N ≅ SheafOfModules.unit W.ringCatSheaf),
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback z).obj L)
      let eQ := prescribedBoundaryRelativeCoefficientIso k R f ι (U.ι ≫ g) b a z ha d (eZ d)
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj M,
      ∃ t : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj N,
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map s ≫ pullbackTensorMap z L M =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eM.inv) ∧
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map t ≫ pullbackTensorMap z L N =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eN.inv) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map s) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map t) := by
  obtain ⟨r, hr, ⟨eZ⟩⟩ := exists_principal_positiveTwist_unitIso k ι g x
  refine ⟨r, hr, eZ, ?_⟩
  intro R _ _ f C W _ a _ z _ b ha M N hM hN eM eN
  exact exists_sameFrame_relative_boundary_section_maps k R f ι n e a z
    _ eZ b ha M N hM hN eM eN
end AlgebraicGeometry.Scheme.CoherentGraph

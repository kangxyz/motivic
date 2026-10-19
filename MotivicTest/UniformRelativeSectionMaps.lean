module
import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.SectionLifting.UniformRelativeSectionMaps
/-! # One actual base shrink constructs all native relative boundary section pairs -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
example
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
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map t) :=
  exists_principal_uniform_relative_section_maps k ι n e g x
#print axioms exists_principal_uniform_relative_section_maps
end AlgebraicGeometry.Scheme.CoherentGraph

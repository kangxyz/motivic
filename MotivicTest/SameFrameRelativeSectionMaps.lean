module
import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.SameFrameRelativeSectionMaps
/-! # Actual relative Serre lifts from the same original frames -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
example
    (k R : Type u) [CommRing k] [CommRing R] [IsNoetherianRing R]
    (f : k →+* R) (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z W : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (g : Z ⟶ ProjectiveSpace k ι)
    (eZ : ∀ d : ℕ, (Modules.pullback g).obj (twistingSheaf k ι (d : ℤ)) ≅
      SheafOfModules.unit Z.ringCatSheaf)
    (b : W ⟶ Z) (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ g)
    (M N : C.Modules) (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (eM : (Modules.pullback z).obj M ≅ SheafOfModules.unit W.ringCatSheaf)
    (eN : (Modules.pullback z).obj N ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback z).obj L)
      let eQ := prescribedBoundaryRelativeCoefficientIso k R f ι g b a z ha d (eZ d)
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj M,
      ∃ t : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj N,
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map s ≫ pullbackTensorMap z L M =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eM.inv) ∧
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map t ≫ pullbackTensorMap z L N =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eN.inv) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map s) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map t) := by
  exact exists_sameFrame_relative_boundary_section_maps k R f ι n e a z g eZ b ha
    M N hM hN eM eN
#print axioms exists_sameFrame_relative_boundary_section_maps
#print axioms prescribedBoundaryRelativeCoefficientIso
end AlgebraicGeometry.Scheme.CoherentGraph

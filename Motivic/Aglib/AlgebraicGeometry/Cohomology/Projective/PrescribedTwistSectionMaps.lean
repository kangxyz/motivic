module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalBoundarySectionMaps
/-! # Actual Serre lifts from specified whole-boundary twist frames -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- The original boundary frames determine actual global sections after one common Serre bound.
No sections or lifting premise is supplied. This works over any Noetherian ring. -/
theorem exists_prescribed_twist_boundary_section_maps
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C W : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor W
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
          SheafOfModules.unit W.ringCatSheaf)
    (M N : C.Modules) (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (eM : (Modules.pullback z).obj M ≅ SheafOfModules.unit W.ringCatSheaf)
    (eN : (Modules.pullback z).obj N ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback z).obj L)
      let eQ := eQ d
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj M,
      ∃ t : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj N,
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map s ≫ pullbackTensorMap z L M =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eM.inv) ∧
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map t ≫ pullbackTensorMap z L N =
          eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eN.inv) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map s) ∧
        IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map t) := by
  obtain ⟨BM, hBM⟩ := finiteMap_exists_global_section_map R ι n e a z M hM
  obtain ⟨BN, hBN⟩ := finiteMap_exists_global_section_map R ι n e a z N hN
  refine ⟨max BM BN, fun d hd => ?_⟩
  let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
  let T := moduleTensorLeftFunctor W ((Modules.pullback z).obj L)
  let eQ := eQ d
  obtain ⟨s, hs⟩ := hBM d ((le_max_left BM BN).trans hd)
    (eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eM.inv))
  obtain ⟨t, ht⟩ := hBN d ((le_max_right BM BN).trans hd)
    (eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eN.inv))
  let E := Invertible.pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
  have hsI := isIso_pullbackSection_of_tensor_eq z E M s _ hs
  have htI := isIso_pullbackSection_of_tensor_eq z E N t _ ht
  exact ⟨s, t, hs, ht, hsI, htI⟩

end AlgebraicGeometry.Scheme.CoherentGraph

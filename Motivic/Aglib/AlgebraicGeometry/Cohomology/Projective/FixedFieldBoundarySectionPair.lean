/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PushforwardTopSection
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalBoundarySectionMaps

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FieldBoundaryRelativeTwists

/-! # Actual prescribed section pairs on the unchanged affine source

The finite field boundary supplies a global generating section of every relative twist.
Serre lifting then gives both exact prescribed values without any principal base shrink.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Both sections and their generating boundary value are constructed on the entire base. -/
theorem exists_fixedField_boundary_section_pair
    (k R : Type u) [Field k] [CommRing R] [IsNoetherianRing R]
    (f : k →+* R) (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z W : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (b : W ⟶ Z) (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ g)
    (M N : C.Modules) (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (eM : (Modules.pullback z).obj M ≅ SheafOfModules.unit W.ringCatSheaf)
    (eN : (Modules.pullback z).obj N ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback z).obj L)
      let Q := T.obj ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))
      ∃ σ : Γ(Q, ⊤), IsIso ((unitHomGlobalSectionsEquiv W Q).symm σ) ∧
      ∃ s : Γ((Modules.pushforward a).obj ((moduleTensorLeftFunctor C L).obj M), ⊤),
      ∃ t : Γ((Modules.pushforward a).obj ((moduleTensorLeftFunctor C L).obj N), ⊤),
        ((Modules.pushforward a).map (boundaryRestriction z L M)).app ⊤ s =
          ((Modules.pushforward a).map ((Modules.pushforward z).map
            (T.map ((pullbackUnitIso z).hom ≫ eM.inv)))).app ⊤
              (pushforwardTopSection a z Q σ) ∧
        ((Modules.pushforward a).map (boundaryRestriction z L N)).app ⊤ t =
          ((Modules.pushforward a).map ((Modules.pushforward z).map
            (T.map ((pullbackUnitIso z).hom ≫ eN.inv)))).app ⊤
              (pushforwardTopSection a z Q σ) := by
  obtain ⟨B, hB⟩ := finiteMap_exists_global_boundary_unit_pair R ι n e a z M N hM hN eM eN
  refine ⟨B, fun d hd => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_fieldBoundaryRelativeCoefficient_unitSection k R f ι g b a z ha d
  obtain ⟨s, t, hs, ht⟩ := hB d hd (pushforwardTopSection a z _ σ)
  exact ⟨σ, hσ, s, t, hs, ht⟩

/-- The same actual lifts as unit-to-line morphisms, with literal tensor-pullback equations.
The boundary coefficient isomorphism is constructed from the original finite field boundary. -/
theorem exists_fixedField_boundary_section_maps
    (k R : Type u) [Field k] [CommRing R] [IsNoetherianRing R]
    (f : k →+* R) (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z W : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (b : W ⟶ Z) (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ g)
    (M N : C.Modules) (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (eM : (Modules.pullback z).obj M ≅ SheafOfModules.unit W.ringCatSheaf)
    (eN : (Modules.pullback z).obj N ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
      let T := moduleTensorLeftFunctor W ((Modules.pullback z).obj L)
      let eQ := fieldBoundaryRelativeCoefficientIso k R f ι g b a z ha d
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
  let eQ := fieldBoundaryRelativeCoefficientIso k R f ι g b a z ha d
  obtain ⟨s, hs⟩ := hBM d ((le_max_left BM BN).trans hd)
    (eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eM.inv))
  obtain ⟨t, ht⟩ := hBN d ((le_max_right BM BN).trans hd)
    (eQ.inv ≫ T.map ((pullbackUnitIso z).hom ≫ eN.inv))
  let E := Invertible.pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
  have hsI := isIso_pullbackSection_of_tensor_eq z E M s _ hs
  have htI := isIso_pullbackSection_of_tensor_eq z E N t _ ht
  exact ⟨s, t, hs, ht, hsI, htI⟩

end AlgebraicGeometry.Scheme.CoherentGraph

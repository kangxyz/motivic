/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.BoundaryRestrictionPullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-! # Prescribed boundary sections as literal global module morphisms -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- Serre lifting produces the actual global section morphism with its literal pullback value. -/
theorem finiteMap_exists_global_section_map
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : Z ⟶ C) [IsClosedImmersion z]
    (M : C.Modules) (hM : affineLocallyFiniteType C M) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
      ∀ t : SheafOfModules.unit Z.ringCatSheaf ⟶
        (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj ((Modules.pullback z).obj M),
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L).obj M,
        (pullbackUnitIso z).inv ≫ (Modules.pullback z).map s ≫ pullbackTensorMap z L M = t := by
  obtain ⟨B, hB⟩ := finite_boundaryRestriction_eventually_principal_app_surjective R ι n e a z M hM
  refine ⟨B, fun d hd t => ?_⟩
  let L := (Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))
  let Q := (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj ((Modules.pullback z).obj M)
  have h := hB (d : ℤ) (Int.ofNat_le.mpr hd) (1 : R)
  change Function.Surjective ((boundaryRestriction z L M).app
    (a ⁻¹ᵁ ((toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (1 : R)))) at h
  have htop : a ⁻¹ᵁ ((toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (1 : R)) = ⊤ := by
    rw [PrimeSpectrum.basicOpen_one, Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]
  rw [htop] at h
  let σ := unitHomGlobalSectionsEquiv Z Q t
  obtain ⟨s, hs⟩ := h (Q.presheaf.map (eqToHom (show z ⁻¹ᵁ ⊤ = ⊤ by simp)).op σ)
  refine ⟨(unitHomGlobalSectionsEquiv C _).symm s, ?_⟩
  simpa only [σ, Q, Equiv.symm_apply_apply] using
    pullback_section_of_boundary_value z L M s σ hs

/-- A generating prescribed tensor value makes the actual pulled global section a unit. -/
theorem isIso_pullbackSection_of_tensor_eq {C Z : Scheme.{u}} (z : Z ⟶ C)
    (L : Invertible.LineBundle C) (M : C.Modules)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ (moduleTensorLeftFunctor C L.val).obj M)
    (t : SheafOfModules.unit Z.ringCatSheaf ⟶
      (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L.val)).obj ((Modules.pullback z).obj M))
    [IsIso t]
    (h : (pullbackUnitIso z).inv ≫ (Modules.pullback z).map s ≫ pullbackTensorMap z L.val M = t) :
    IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map s) := by
  have := Invertible.PullbackTensor.Local.pullbackTensorMap_isIso z L.val M L.property
  have : IsIso (((pullbackUnitIso z).inv ≫ (Modules.pullback z).map s) ≫
      pullbackTensorMap z L.val M) := by rw [Category.assoc, h]; infer_instance
  exact IsIso.of_isIso_comp_right _ (pullbackTensorMap z L.val M)
end AlgebraicGeometry.Scheme.CoherentGraph

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.SectionLifting.Basic
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward

/-!
# Full closed-boundary section lifting on polynomial projective space

The native restriction unit is proved epic on stalks. Its coherent kernel
therefore gives eventual surjectivity on actual global sections by Serre
vanishing. The projection formula retains the genuine restricted twist.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
universe u

namespace ModuleCat

theorem extendRestrictScalarsAdj_unit_epi_of_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    Epi ((extendRestrictScalarsAdj f).unit.app M) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  let := f.toAlgebra
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
      obtain ⟨r, rfl⟩ := hf s
      refine ⟨r • m, ?_⟩
      change (1 : S) ⊗ₜ[R] (r • m) = f r ⊗ₜ[R] m
      rw [TensorProduct.tmul_smul]
      change (f r * 1) ⊗ₜ[R] m = f r ⊗ₜ[R] m
      rw [mul_one]
  | add t₁ t₂ h₁ h₂ =>
      obtain ⟨m₁, rfl⟩ := h₁
      obtain ⟨m₂, rfl⟩ := h₂
      exact ⟨m₁ + m₂, map_add _ _ _⟩

end ModuleCat

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to an entire closed subscheme is an epimorphism of sheaves,
although it need not be surjective on global sections before twisting. -/
theorem pullbackPushforwardUnit_epi_of_closedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : X.Modules) :
    Epi ((pullbackPushforwardAdjunction i).unit.app M) := by
  apply epi_of_moduleStalk
  intro x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hx
    have h := pullbackPushforwardUnit_moduleStalk i i.isClosedEmbedding.isInducing z M
    let := ModuleCat.extendRestrictScalarsAdj_unit_epi_of_surjective
      (i.stalkMap z).hom (i.stalkMap_surjective z) ((moduleStalk X (i z)).obj M)
    have : Epi (((moduleStalk X (i z)).map
        ((pullbackPushforwardAdjunction i).unit.app M)) ≫
        (pushforwardModuleStalkIso i i.isClosedEmbedding.isInducing z).hom.app
          ((pullback i).obj M) ≫
        (ModuleCat.restrictScalars (i.stalkMap z).hom).map
          ((pullbackModuleStalkIso i z).hom.app M)) := by
      rw [h]
      infer_instance
    exact (epi_comp_iff_of_isIso ((moduleStalk X (i z)).map
      ((pullbackPushforwardAdjunction i).unit.app M))
      ((pushforwardModuleStalkIso i i.isClosedEmbedding.isInducing z).hom.app
        ((pullback i).obj M) ≫
        (ModuleCat.restrictScalars (i.stalkMap z).hom).map
          ((pullbackModuleStalkIso i z).hom.app M))).mp inferInstance
  · exact (isZero_closedImmersion_moduleStalk_of_not_mem i x hx
      ((pullback i).obj M)).epi _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

open ProjectiveSpace Scheme.Modules Scheme.Modules.QuasiCoherent

/-- The actual boundary map: tensor the native restriction unit, then use
closed-immersion projection formula. Its codomain consists of sections of
`i* O(d) ⊗ i* M` on the entire closed boundary, not just a coordinate chart. -/
def projectiveBoundaryRestriction
    (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (i : Z ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (M : (ProjectiveSpace R ι).Modules) (d : ℤ) :=
  (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map
      ((pullbackPushforwardAdjunction i).unit.app M) ≫
    (closedImmersionProjectionFormulaIso i (twistingSheaf R ι d)
      ((Scheme.Modules.pullback i).obj M)).hom

/-- Serre lifting onto a full closed boundary, with the exact native
restriction map and the twist/restriction comparison included. -/
theorem projectiveBoundaryRestriction_eventually_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {Z : Scheme.{u}} (i : Z ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      Function.Surjective ((projectiveBoundaryRestriction R ι i M d).app ⊤) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let π := (pullbackPushforwardAdjunction i).unit.app M
  let : Epi π := pullbackPushforwardUnit_epi_of_closedImmersion i M
  have hQ := FiniteMorphism.affineLocallyFiniteType_pushforward i
    (affineLocallyFiniteType_pullback i hM)
  obtain ⟨B, hB⟩ := projective_coherentQuotient_eventually_sections_surjective
    R ι n e hM hQ π
  refine ⟨B, fun d hd => ?_⟩
  have he := ConcreteCategory.bijective_of_isIso
    ((closedImmersionProjectionFormulaIso i (twistingSheaf R ι d)
      ((Scheme.Modules.pullback i).obj M)).hom.app ⊤)
  exact he.surjective.comp (hB d hd)

end AlgebraicGeometry.Scheme.Cohomology

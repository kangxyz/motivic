/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientSupportAction
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Finite generation of actual categorical Tor

Over a Noetherian commutative ring, finitely generated modules form an abelian
category with enough projectives. Its inclusion preserves projectives: every
projective finite module splits a finite free cover. Mapping a projective
resolution through this exact inclusion constructs a degreewise finite genuine
projective resolution in the full module category. Thus categorical Tor of two
finite modules is finite, without a resolution supplied as an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Finite modules have enough projectives, using actual finite free covers. -/
instance finiteModuleEnoughProjectives : EnoughProjectives (FGModuleCat.{u} R) where
  presentation N := by
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R N
    let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    let g : FGModuleCat.of R P ⟶ N := FGModuleCat.ofHom f
    have : Epi (F.map g) := (ModuleCat.epi_iff_surjective _).mpr hf
    have : Epi g := F.epi_of_epi_map inferInstance
    have : Projective (FGModuleCat.of R P) :=
      F.projective_of_map_projective
        (ModuleCat.projective_of_free (Module.Free.chooseBasis R P))
    exact ⟨{ p := FGModuleCat.of R P, f := g }⟩

/-- A projective finite module is projective among all modules: a finite free
cover splits in the finite category and gives a retract after inclusion. -/
instance finiteModuleInclusionPreservesProjectives :
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).PreservesProjectiveObjects where
  projective_obj {N} hN := by
    let := hN
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R N
    let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    let g : FGModuleCat.of R P ⟶ N := FGModuleCat.ofHom f
    have : Epi (F.map g) := (ModuleCat.epi_iff_surjective _).mpr hf
    have : Epi g := F.epi_of_epi_map inferInstance
    let t : Retract N (FGModuleCat.of R P) :=
      { i := Projective.factorThru (𝟙 N) g
        r := g
        retract := Projective.factorThru_comp (𝟙 N) g }
    have : Projective (F.obj (FGModuleCat.of R P)) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis R P)
    exact (t.map F).projective

/-- A genuine projective resolution whose every term is finitely generated. -/
def finiteProjectiveResolution (N : ModuleCat.{u} R) [Module.Finite R N] :
    ProjectiveResolution N :=
  (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapProjectiveResolution
    (projectiveResolution (FGModuleCat.of R N))

/-- Finiteness follows from construction in the category of finite modules. -/
instance finiteProjectiveResolution_finite (N : ModuleCat.{u} R) [Module.Finite R N] (n : ℕ) :
    Module.Finite R ((finiteProjectiveResolution N).complex.X n) :=
  inferInstanceAs (Module.Finite R
    ((projectiveResolution (FGModuleCat.of R N)).complex.X n))

/-- Actual homology of a degreewise finite complex is finite over a Noetherian ring. -/
theorem finite_homology_of_finite_term (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    [Module.Finite R (C.X n)] : Module.Finite R (C.homology n) := by
  have : IsNoetherian R (C.cycles n) :=
    isNoetherian_of_injective (C.iCycles n).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (C.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Tor of two finite modules over a Noetherian ring is finite in every degree.
No projective or flat hypothesis on the coefficients is imposed. -/
instance finite_actual_tor (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (n : ℕ) : Module.Finite R (((Tor (ModuleCat R) n).obj M).obj N) := by
  let P := finiteProjectiveResolution N
  let C := (((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex _).obj P.complex
  have : Module.Finite R (C.X n) :=
    inferInstanceAs (Module.Finite R (M ⊗[R] (P.complex.X n)))
  have : Module.Finite R (C.homology n) := finite_homology_of_finite_term C n
  let e : C.homology n ≅ (((Tor (ModuleCat R) n).obj M).obj N) :=
    (P.isoLeftDerivedObj ((tensoringLeft (ModuleCat R)).obj M) n).symm
  exact Module.Finite.of_surjective
    e.hom.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Finiteness over the ambient ring implies finiteness for the constructed
quotient action, with its proved compatible scalar tower. -/
instance finite_quotientModule (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : I ≤ Module.annihilator R M) [Module.Finite R M] :
    Module.Finite (R ⧸ I) (quotientModule I M hM) := by
  let := quotientModuleAction I M hM
  have : IsScalarTower R (R ⧸ I) M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

/-- Actual quotient-supported Tor is finite over the full scheme-theoretic
support quotient, including nonradical support ideals. -/
instance finite_torSupportModule (J K : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ (J ⊔ K)) (torSupportModule J K n) :=
  finite_quotientModule _ _ _

end ModuleCat.TorComparison

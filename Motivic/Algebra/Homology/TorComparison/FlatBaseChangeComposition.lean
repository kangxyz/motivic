/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.FlatBaseChangeNaturality

/-!
# Coherence of the homology comparison in flat base change

This file proves intermediate exact-homology coherence lemmas for the canonical
flat Tor comparison. A scalar-ring composition theorem for Tor requires the
additional tensorator and projective-resolution comparison squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

universe u v w

namespace Motivic.TorComparison

section Homology

variable {C : Type u} {D : Type v} {E : Type w}
  [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E]

set_option backward.isDefEq.respectTransparency false in
/-- Canonical homology comparison commutes with composition of exact additive functors. -/
theorem exactMapHomologyIso_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : ShortComplex C) :
    (K.mapHomologyIso (F ⋙ G)).hom =
      ((K.map F).mapHomologyIso G).hom ≫ G.map (K.mapHomologyIso F).hom := by
  let h₁ := K.homologyData.left.map (F ⋙ G)
  let h₂ := (K.homologyData.left.map F).map G
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (K.map (F ⋙ G))) h₁ h₂ :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp [h₁, h₂]
      commf' := by simp [h₁, h₂]
      commπ := by simp [h₁, h₂] }
  have hm : h₂.homologyIso.hom = h₁.homologyIso.hom := by
    simpa [γ] using γ.homologyMap_comm
  rw [(K.homologyData.left.map F).mapHomologyIso_eq G]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  change h₁.homologyIso.hom = h₂.homologyIso.hom ≫
    G.map (K.mapHomologyIso F).inv ≫ G.map (K.mapHomologyIso F).hom
  erw [hm, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Exact homology comparison is compatible with every natural transformation. -/
theorem exactMapHomologyIso_natTrans (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : F ⟶ G) (K : ShortComplex C) :
    τ.app K.homology ≫ (K.mapHomologyIso G).inv =
      (K.mapHomologyIso F).inv ≫ ShortComplex.homologyMap (K.mapNatTrans τ) := by
  rw [τ.app_homology K]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison for the identity functor acts as the identity on actual homology. -/
theorem exactMapHomologyIso_id (K : ShortComplex C) :
    (K.mapHomologyIso (𝟭 C)).hom = 𝟙 K.homology := by
  let h₁ := K.homologyData.left
  let h₂ := K.homologyData.left.map (𝟭 C)
  let γ : ShortComplex.LeftHomologyMapData (𝟙 K) h₁ h₂ :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp [h₁, h₂]
      commf' := by simp [h₁, h₂]
      commπ := by simp [h₁, h₂] }
  have hm : h₂.homologyIso.hom = h₁.homologyIso.hom := by
    simpa [γ] using γ.homologyMap_comm
  change h₂.homologyIso.hom = _
  rw [hm]
  dsimp [h₁, ShortComplex.LeftHomologyData.homologyIso,
    ShortComplex.leftHomologyIso, ShortComplex.LeftHomologyData.leftHomologyIso,
    ShortComplex.leftHomologyMapIso']
  rw [← ShortComplex.leftHomologyMap'_comp, Category.id_comp,
    ShortComplex.leftHomologyMap'_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse exact-homology comparison obeys the same composition law. -/
theorem exactMapHomologyIso_comp_inv (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : ShortComplex C) :
    (K.mapHomologyIso (F ⋙ G)).inv =
      G.map (K.mapHomologyIso F).inv ≫ ((K.map F).mapHomologyIso G).inv := by
  have h : K.mapHomologyIso (F ⋙ G) =
      (K.map F).mapHomologyIso G ≪≫ G.mapIso (K.mapHomologyIso F) :=
    Iso.ext (exactMapHomologyIso_comp F G K)
  exact congrArg Iso.inv h

end Homology

section Scalars

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical scalar-extension associator respects the actual tensorator. -/
theorem extendScalarsComp_tensorator (f : R →+* S) (g : S →+* T)
    (M N : ModuleCat.{u} R) :
    Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (g.comp f)) M N ≫
        ((ModuleCat.extendScalarsComp f g).hom.app M ⊗ₘ
          (ModuleCat.extendScalarsComp f g).hom.app N) =
      (ModuleCat.extendScalarsComp f g).hom.app (M ⊗ N) ≫
        (ModuleCat.extendScalars g).map
          (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars f) M N) ≫
        Functor.OplaxMonoidal.δ (ModuleCat.extendScalars g)
          ((ModuleCat.extendScalars f).obj M) ((ModuleCat.extendScalars f).obj N) := by
  apply ((ModuleCat.extendRestrictScalarsAdj (g.comp f)).homEquiv _ _).injective
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  simp only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, ModuleCat.comp_apply]
  erw [ModuleCat.extendScalars_δ_tmul (g.comp f) M N m n]
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  have hl := congrArg₂ (fun (x : (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)
      (y : (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj N) => x ⊗ₜ[T] y)
    (ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m)
    (ModuleCat.extendScalarsComp_hom_app_one_tmul f g N n)
  have hr := congrArg (fun x =>
      (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars g)
        ((ModuleCat.extendScalars f).obj M) ((ModuleCat.extendScalars f).obj N))
      ((ModuleCat.extendScalars g).map
        (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars f) M N) x))
    (ModuleCat.extendScalarsComp_hom_app_one_tmul f g (M ⊗ N) (m ⊗ₜ[R] n))
  refine hl.trans (hr.trans ?_).symm
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The flat homology comparison respects the actual scalar-extension associator. -/
theorem flatExtendHomologyIso_comp (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalarsComp f g).hom.app (K.homology n) ≫
        (ModuleCat.extendScalars g).map (flatExtendHomologyIso f hf K n).hom ≫
        (flatExtendHomologyIso g hg
          (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K) n).hom =
      (flatExtendHomologyIso (g.comp f) (hf.comp hg) K n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).hom _).app K) n := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hg
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf.comp hg)
  have h := exactMapHomologyIso_natTrans
    (ModuleCat.extendScalars (g.comp f))
    (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g)
    (ModuleCat.extendScalarsComp f g).hom (K.sc n)
  rw [exactMapHomologyIso_comp_inv] at h
  exact h

end Scalars

end Motivic.TorComparison

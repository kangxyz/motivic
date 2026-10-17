/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingCoherence
public import Motivic.AlgebraicGeometry.Modules.AffineOpenTildeRestrictionCoherence

/-!
# Coherence for genuine nested open restrictions

The canonical restriction comparisons satisfy associativity on arbitrary
smaller opens. These equations permit chart isomorphisms to be compared on
common refinements, without assuming the desired descent cocycle.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.OpenRefinement

open Scheme.Modules Motivic.FiniteOpenModuleGluing

variable {X : Scheme.{u}} {U V W T : X.Opens}

/-- The actual comparison from direct restriction to two successive restrictions. -/
abbrev compositionIso (h : U ≤ V) (k : V ≤ W) :
    restrictFunctor (X.homOfLE (h.trans k)) ≅
      restrictFunctor (X.homOfLE k) ⋙ restrictFunctor (X.homOfLE h) :=
  AffineOpenTilde.openCompositionIso h k

set_option backward.isDefEq.respectTransparency false in
/-- The comparison is literal equality transport on original module sections. -/
theorem compositionIso_hom_app (h : U ≤ V) (k : V ≤ W)
    (M : W.toScheme.Modules) (A : U.toScheme.Opens) :
    ((compositionIso h k).hom.app M).app A =
      M.presheaf.map (eqToHom (show
        X.homOfLE k ''ᵁ X.homOfLE h ''ᵁ A = X.homOfLE (h.trans k) ''ᵁ A by
          simp [← Scheme.Hom.comp_image])).op := by
  simp only [compositionIso, AffineOpenTilde.openCompositionIso, Iso.trans_hom,
    NatTrans.comp_app, Hom.comp_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app,
    ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The actual three-step open restriction comparison is associative. -/
theorem compositionIso_assoc (h : T ≤ U) (k : U ≤ V) (l : V ≤ W)
    (M : W.toScheme.Modules) :
    (compositionIso (h.trans k) l).hom.app M ≫
        (compositionIso h k).hom.app ((restrictFunctor (X.homOfLE l)).obj M) =
      (compositionIso h (k.trans l)).hom.app M ≫
        (restrictFunctor (X.homOfLE h)).map ((compositionIso k l).hom.app M) := by
  apply Scheme.Modules.hom_ext
  intro A
  simp only [Hom.comp_app, compositionIso_hom_app, restrictFunctor_map_app,
    restrict_map, ← Functor.map_comp]
  congr 1

/-- Restrict a supplied chart comparison to a genuinely smaller open. -/
def liftIso (h : V ≤ W) {M : W.toScheme.Modules} {N : V.toScheme.Modules}
    (e : (restrictFunctor (X.homOfLE h)).obj M ≅ N) (k : U ≤ V) :
    (restrictFunctor (X.homOfLE (k.trans h))).obj M ≅
      (restrictFunctor (X.homOfLE k)).obj N :=
  (compositionIso k h).app M ≪≫ (restrictFunctor (X.homOfLE k)).mapIso e

set_option backward.isDefEq.respectTransparency false in
/-- Lifting a two-step comparison is exactly composition of its two lifted comparisons. -/
theorem liftIso_comp (h : V ≤ W) (k : U ≤ V) (l : T ≤ U)
    {M : W.toScheme.Modules} {N : V.toScheme.Modules} {Q : U.toScheme.Modules}
    (e : (restrictFunctor (X.homOfLE h)).obj M ≅ N)
    (f : (restrictFunctor (X.homOfLE k)).obj N ≅ Q) :
    liftIso (k.trans h) ((compositionIso k h).app M ≪≫
        (restrictFunctor (X.homOfLE k)).mapIso e ≪≫ f) l =
      liftIso h e (l.trans k) ≪≫ liftIso k f l := by
  apply Iso.ext
  simp only [liftIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Iso.app_hom, Category.assoc]
  rw [← reassoc_of% compositionIso_assoc l k h M]
  have hn := (compositionIso l k).hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a pair comparison to any common smaller open is the pair of lifted maps. -/
theorem transitionOn_pair {ι : Type u} (v : ι → X.Opens)
    (M : ∀ i, (v i).toScheme.Modules)
    (N : ∀ i j, (v i ⊓ v j).toScheme.Modules)
    (e : ∀ i j, (restrictFunctor (X.homOfLE (inf_le_left : v i ⊓ v j ≤ v i))).obj
      (M i) ≅ N i j)
    (f : ∀ i j, (restrictFunctor (X.homOfLE (inf_le_right : v i ⊓ v j ≤ v j))).obj
      (M j) ≅ N i j)
    {A : X.Opens} (i j : ι) (hi : A ≤ v i) (hj : A ≤ v j) :
    transitionOn v M (fun i j => e i j ≪≫ (f i j).symm) i j hi hj =
      liftIso (inf_le_left : v i ⊓ v j ≤ v i) (e i j) (le_inf hi hj) ≪≫
        (liftIso (inf_le_right : v i ⊓ v j ≤ v j) (f i j) (le_inf hi hj)).symm := by
  apply Iso.ext
  simp only [transitionOn, restrictToOverlapIso, liftIso, compositionIso,
    AffineOpenTilde.openCompositionIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, NatTrans.comp_app, Category.assoc]

end Motivic.OpenRefinement

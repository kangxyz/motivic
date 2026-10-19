/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.SchemeIso
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.FunctionalQuotientAffineChart
/-! # Native generic ratio norms under a source isomorphism

An isomorphism of the actual generic fibers must preserve both the displayed
scalar structure and their maps to the same original compactification. The
original functionals are pulled literally in both presentations. Neither finite
source nor the original parameter space is assumed integral.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.LineRatioIso`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.OriginalNormParameterGenericRatio`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme
open Modules Modules.Invertible

/-- The same original ratio has equal norms in two isomorphic generic-fiber
presentations. Both comparison equations are scheme equations, not scalar or
norm equality assumptions. -/
theorem genericFiberLineRatioNorm_eq_of_source_iso
    {B C₀ C₁ T : Scheme.{u}} [IsIntegral T]
    (f₀ : C₀ ⟶ T) (f₁ : C₁ ⟶ T) [IsFinite f₀] [IsFinite f₁]
    (k₀ : C₀ ⟶ B) (k₁ : C₁ ⟶ B) (L : LineBundle B)
    (a c : L.val ⟶ SheafOfModules.unit B.ringCatSheaf)
    [Mono (pullbackUnitMap k₀ a)] [Mono (pullbackUnitMap k₀ c)]
    [Mono (pullbackUnitMap k₁ a)] [Mono (pullbackUnitMap k₁ c)]
    (e : pullback f₀ (T.fromSpecStalk (genericPoint T)) ≅
      pullback f₁ (T.fromSpecStalk (genericPoint T)))
    (he : e.hom ≫ pullback.snd f₁ (T.fromSpecStalk (genericPoint T)) =
      pullback.snd f₀ (T.fromSpecStalk (genericPoint T)))
    (hk : e.hom ≫ pullback.fst f₁ (T.fromSpecStalk (genericPoint T)) ≫ k₁ =
      pullback.fst f₀ (T.fromSpecStalk (genericPoint T)) ≫ k₀) :
    genericFiberLineRatioNorm f₀ (pullbackLineBundle k₀ L)
        (pullbackUnitMap k₀ a) (pullbackUnitMap k₀ c) =
      genericFiberLineRatioNorm f₁ (pullbackLineBundle k₁ L)
        (pullbackUnitMap k₁ a) (pullbackUnitMap k₁ c) := by
  let n₀ := pullback.fst f₀ (T.fromSpecStalk (genericPoint T))
  let n₁ := pullback.fst f₁ (T.fromSpecStalk (genericPoint T))
  let : IsIso (pullbackUnitMap n₀ (pullbackUnitMap k₀ c)) :=
    genericFiberLineMap_isIso f₀ (pullbackLineBundle k₀ L) (pullbackUnitMap k₀ c)
  let : IsIso (pullbackUnitMap n₁ (pullbackUnitMap k₁ c)) :=
    genericFiberLineMap_isIso f₁ (pullbackLineBundle k₁ L) (pullbackUnitMap k₁ c)
  let := pullbackUnitMap_comp_isIso_of_nested k₀ n₀ c
  let := pullbackUnitMap_comp_isIso_of_nested k₁ n₁ c
  let := pullbackUnitMap_comp_isIso_of_first (n₁ ≫ k₁) e.hom c
  have hθ : Hom.unitEndomorphismPullback e.hom
      (inv (pullbackUnitMap n₁ (pullbackUnitMap k₁ c)) ≫
        pullbackUnitMap n₁ (pullbackUnitMap k₁ a)) =
      inv (pullbackUnitMap n₀ (pullbackUnitMap k₀ c)) ≫
        pullbackUnitMap n₀ (pullbackUnitMap k₀ a) := by
    rw [functionalQuotient_comp k₁ n₁ a c, functionalQuotient_comp k₀ n₀ a c,
      functionalQuotient_pullback (n₁ ≫ k₁) e.hom a c]
    have hmap (u v : pullback f₀ (T.fromSpecStalk (genericPoint T)) ⟶ B)
        (h : u = v) [IsIso (pullbackUnitMap u c)] [IsIso (pullbackUnitMap v c)] :
        inv (pullbackUnitMap u c) ≫ pullbackUnitMap u a =
          inv (pullbackUnitMap v c) ≫ pullbackUnitMap v a := by
      subst v
      rfl
    exact hmap _ _ hk
  have hu : (genericFiberLineRatioUnit f₀ (pullbackLineBundle k₀ L)
        (pullbackUnitMap k₀ a) (pullbackUnitMap k₀ c)).val =
      e.hom.appTop ((genericFiberLineRatioUnit f₁ (pullbackLineBundle k₁ L)
        (pullbackUnitMap k₁ a) (pullbackUnitMap k₁ c)).val) := by
    change Modules.Hom.app
      (inv (pullbackUnitMap n₀ (pullbackUnitMap k₀ c)) ≫
        pullbackUnitMap n₀ (pullbackUnitMap k₀ a)) ⊤
          (1 : Γ(pullback f₀ (T.fromSpecStalk (genericPoint T)), ⊤)) =
      e.hom.appTop (Modules.Hom.app
        (inv (pullbackUnitMap n₁ (pullbackUnitMap k₁ c)) ≫
          pullbackUnitMap n₁ (pullbackUnitMap k₁ a)) ⊤
            (1 : Γ(pullback f₁ (T.fromSpecStalk (genericPoint T)), ⊤)))
    rw [← hθ]
    exact Hom.unitEndomorphismPullback_app_one e.hom _
  unfold genericFiberLineRatioNorm
  rw [hu]
  exact FiniteSchemeNormBaseChange.norm_appTop_of_iso
    (pullback.snd f₀ (T.fromSpecStalk (genericPoint T)))
    (pullback.snd f₁ (T.fromSpecStalk (genericPoint T))) e he _

end AlgebraicGeometry.Scheme

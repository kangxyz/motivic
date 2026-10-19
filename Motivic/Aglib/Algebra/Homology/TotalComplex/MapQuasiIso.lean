/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.TotalComplex.Map
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Reflecting a total-complex quasi-isomorphism through an exact functor

The actual total-complex comparison isomorphisms identify the two images of a
bicomplex map. An exact functor reflecting isomorphisms therefore reflects a
quasi-isomorphism after totalization. The mapped total must genuinely be a
quasi-isomorphism; no rowwise or columnwise quasi-isomorphism criterion is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex₂

variable {C D I₁ I₂ J : Type*} [Category* C] [Category* D]
  [Abelian C] [Abelian D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.ReflectsIsomorphisms]
  {K L : HomologicalComplex₂ C c₁ c₂}
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [K.HasTotal c] [L.HasTotal c]
  [(exteriorMapBicomplex F K).HasTotal c] [(exteriorMapBicomplex F L).HasTotal c]
  [∀ j, PreservesColimit
    (Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F]
  [∀ j, PreservesColimit
    (Discrete.functor (L.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F]

/-- Exact faithful scalar restriction can reflect the quasi-isomorphism of a
literal total map, once its mapped total map has been proved a quasi-isomorphism. -/
theorem exteriorTotalMap_quasiIso_of_map (φ : K ⟶ L)
    [QuasiIso (HomologicalComplex₂.total.map
      (((F.mapHomologicalComplex c₂).mapHomologicalComplex c₁).map φ) c)] :
    QuasiIso (HomologicalComplex₂.total.map φ c) := by
  have hK : QuasiIso (exteriorTotalComparison F K c) := by
    change QuasiIso (exteriorMapTotalIso F K c).hom
    infer_instance
  have hL : QuasiIso (exteriorTotalComparison F L c) := by
    change QuasiIso (exteriorMapTotalIso F L c).hom
    infer_instance
  have hcomp : QuasiIso (exteriorTotalComparison F K c ≫
      (F.mapHomologicalComplex c).map (HomologicalComplex₂.total.map φ c)) := by
    rw [← exteriorTotalComparison_naturality]
    infer_instance
  have hmap : QuasiIso ((F.mapHomologicalComplex c).map
      (HomologicalComplex₂.total.map φ c)) :=
    quasiIso_of_comp_left (exteriorTotalComparison F K c) _
  exact (quasiIso_map_iff_of_preservesHomology _ F).mp hmap

end HomologicalComplex₂

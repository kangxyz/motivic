/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldObjectEvaluation

/-! # Sectionwise exact direct image from the small Nisnevich site of a field

Base change gives an actual finite étale field-site object. Its ordinary sheaf
evaluation is exact, even when that object is disconnected.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Motivic.FiniteEtaleSite

variable {K : Type u} [Field K] {X : Scheme.{u}} (b : Spec (.of K) ⟶ X)

/-- Direct image of an ordinary sheaf epimorphism is surjective on every section group. -/
theorem fieldDirectImage_map_app_surjective
    {F G : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) [Epi a] (V : FiniteEtaleSite X) :
    Function.Surjective (((directImage b).map a).hom.app (op V)) :=
  objectEvaluation_surjective_of_epi ((baseChange b).obj V) a

/-- The stronger underlying-presheaf epimorphism, needed for actual sheaf products. -/
theorem fieldDirectImage_map_presheaf_epi
    {F G : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) [Epi a] : Epi ((directImage b).map a).hom := by
  have (V : (FiniteEtaleSite X)ᵒᵖ) : Epi (((directImage b).map a).hom.app V) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (fieldDirectImage_map_app_surjective b a V.unop)
  exact NatTrans.epi_of_epi_app _

instance fieldDirectImage_preservesEpimorphisms : (directImage b).PreservesEpimorphisms where
  preserves a := by
    intro
    apply (sheafToPresheaf _ _).epi_of_epi_map
    exact fieldDirectImage_map_presheaf_epi b a

instance fieldDirectImage_additive : (directImage b).Additive where
  map_add := by intros; rfl

instance fieldDirectImage_preservesHomology : (directImage b).PreservesHomology := by
  have := (imageAdjunction b).isRightAdjoint
  exact Functor.preservesHomology_of_preservesEpis_and_kernels (directImage b)

/-- The genuine direct image preserves ordinary short exact sequences. -/
theorem fieldDirectImage_shortExact
    (C : ShortComplex (Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}))
    (hC : C.ShortExact) : (C.map (directImage b)).ShortExact := by
  have := hC.mono_f
  have := hC.epi_g
  exact hC.map (directImage b)

end Motivic.FiniteEtaleSite

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointInverseImage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Exact ordinary small-site evaluation at actual field objects

This is exactness at connected field objects only. Exactness at arbitrary finite
étale schemes still requires their actual disjoint-component sheaf decomposition.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}} (K : Type u) [Field K] (q : Spec (.of K) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]

/-- Evaluation of the original ordinary small-site sheaf at an actual field object. -/
def fieldEvaluation : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} ⥤
    AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙ (evaluation (FiniteEtaleSite S)ᵒᵖ _).obj (op (fieldObject K q))

instance : (fieldEvaluation K q).Additive := by
  unfold fieldEvaluation
  infer_instance

instance : PreservesFiniteLimits (fieldEvaluation K q) := by
  unfold fieldEvaluation
  infer_instance

instance : (fieldEvaluation K q).PreservesEpimorphisms :=
  Functor.PreservesEpimorphisms.of_iso (fieldPointSheafFiberIso K q AddCommGrpCat.{u + 1})

instance : (fieldEvaluation K q).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (fieldEvaluation K q)

/-- Every ordinary sheaf epimorphism is surjective at the actual field object. -/
theorem fieldEvaluation_surjective_of_epi
    {F G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}} (a : F ⟶ G) [Epi a] :
    Function.Surjective (a.hom.app (op (fieldObject K q))) :=
  (AddCommGrpCat.epi_iff_surjective ((fieldEvaluation K q).map a)).mp inferInstance

/-- Ordinary short exact sequences remain exact upon field evaluation. -/
theorem fieldEvaluation_shortExact
    (C : ShortComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}))
    (hC : C.ShortExact) : (C.map (fieldEvaluation K q)).ShortExact := by
  have := hC.mono_f
  have := hC.epi_g
  exact hC.map (fieldEvaluation K q)

end Motivic.FiniteEtaleSite

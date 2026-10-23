/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageExact
public import Motivic.Aglib.Algebra.Homology.DerivedCategory.FiniteEdge
public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Lean.Util.CollectAxioms

/-! Actual small-site injectives and the original ordinary cohomology source. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u w
namespace MotivicTest.SmallSiteImageAndFiniteEdge
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- A genuine scheme map supplies the injective middle object needed by the field-family step. -/
theorem actual_directImage_injective {S T : Scheme.{u}} (b : T ⟶ S)
    (I : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((directImage b).obj I) := inferInstance

/-- The finite-edge result uses the project's unchanged section-representing source. -/
theorem ordinary_source_edge_bijective (S : Scheme.{u})
    [HasDerivedCategory.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
    (U : Scheme.EtaleSeparatedFiniteType S)
    (T : Triangle (DerivedCategory (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})))
    (hT : T ∈ distTriang _) (n : ℤ)
    (hcone : ∀ i : ℤ, i ≤ n → IsZero ((DerivedCategory.homologyFunctor _ i).obj T.obj₃)) :
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor _ n).obj
          (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
            (nisnevichTopology S) U) ⟶ T.obj₁ =>
      f ≫ T.mor₁) :=
  DerivedCategory.single_postcomp_bijective_of_cone_homology T hT _ n hcone

open Lean in
run_cmd do
  for name in #[``actual_directImage_injective, ``ordinary_source_edge_bijective,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.inverseImage_shortExact,
      ``DerivedCategory.single_postcomp_injective_of_cone_homology,
      ``CategoryTheory.Triangulated.TStructure.postcomp_injective_of_cone_isGE] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Small-site injectives and original-source finite edges: standard foundations only."

end MotivicTest.SmallSiteImageAndFiniteEdge

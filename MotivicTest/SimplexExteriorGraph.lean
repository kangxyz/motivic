/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraph
public import Lean.Util.CollectAxioms

/-!
# Consumers of genuine exterior graph compatibility

These statements retain arbitrary fields, arbitrary smooth maps, all simplex
degrees, disconnected sources, and empty sources. The coefficient checks use
the original signed cycles, and the support check uses the actual finite
pushforward of the whole fundamental cycle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SimplexExteriorGraph

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- No flatness, connectedness, or nonemptiness is required of the graph map. -/
theorem actual_simplex_graph (n : ℕ) (φ : X ⟶ Y) :
    Cor.simplexExterior n ((Cor.graphFunctor k).map φ) =
      (Cor.graphFunctor k).map
        (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))) :=
  Cor.simplexExterior_graph n φ

/-- Arbitrary signed graph multiplicities are retained. -/
theorem actual_signed_graph (n : ℕ) (φ : X ⟶ Y) (a : ℤ) :
    Cor.simplexExterior n (a • (Cor.graphFunctor k).map φ) =
      a • (Cor.graphFunctor k).map
        (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))) := by
  rw [map_zsmul, Cor.simplexExterior_graph]
  rfl

/-- Empty sources are included in the same graph equality without additional cases. -/
theorem actual_empty_source [IsEmpty X.left] (n : ℕ) (φ : X ⟶ Y) :
    Cor.simplexExterior n ((Cor.graphFunctor k).map φ) = 0 := by
  have h : (Cor.graphFunctor k).map φ = 0 := by
    apply Finsupp.ext
    intro V
    exact isEmptyElim (show X.left from V.projection (Classical.arbitrary V.scheme))
  rw [h, map_zero]

section Parameter

variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The bridge holds for every geometrically integral smooth parameter. -/
theorem actual_parameter_graph (φ : X ⟶ Y) :
    FiniteCorrespondence.exteriorIdentity (X := X) (Y := Y) T
        (componentGraphCycleOver (X := X.left) (Y := Y.left)
          φ.left (MorphismProperty.Over.w φ)) =
      componentGraphCycleOver (X := (SmoothSite.product X T).left)
        (Y := (SmoothSite.product Y T).left)
        (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T))) :=
  FiniteCorrespondence.exteriorIdentity_componentGraphCycleOver T φ

/-- Every component of the exterior graph has exactly its original coefficient one. -/
theorem actual_component_coefficient (φ : X ⟶ Y)
    (D : Set (SmoothSite.product X T).left)
    (hD : D ∈ irreducibleComponents (SmoothSite.product X T).left) :
    (FiniteCorrespondence.exteriorIdentity (X := X) (Y := Y) T
      (componentGraphCycleOver (X := X.left) (Y := Y.left)
        φ.left (MorphismProperty.Over.w φ)))
      (componentGraphGeneratorOver (X := (SmoothSite.product X T).left)
        (Y := (SmoothSite.product Y T).left)
        (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T))) D hD) = 1 := by
  rw [FiniteCorrespondence.exteriorIdentity_componentGraphCycleOver,
    componentGraphCycleOver_coefficient]

/-- The graph support equality identifies whole fundamental pushforwards. -/
theorem actual_component_fundamental (φ : X ⟶ Y)
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (hCT : (pullback.fst X.hom T.hom) ⁻¹' C ∈
      irreducibleComponents (SmoothSite.product X T).left) :
    FiniteCorrespondence.toIntegralCycle
        (componentGraphGeneratorOver (X := (SmoothSite.product X T).left)
          (Y := (SmoothSite.product Y T).left)
          (SmoothSite.productMap φ (𝟙 T)).left
          (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T)))
          ((pullback.fst X.hom T.hom) ⁻¹' C) hCT).cycle =
      IntegralCycle.finitePushforward
        ((componentGraphGeneratorOver (X := X.left) (Y := Y.left)
          φ.left (MorphismProperty.Over.w φ) C hC).exteriorIdentityInclusion T)
        (fundamentalCycle
          ((componentGraphGeneratorOver (X := X.left) (Y := Y.left)
            φ.left (MorphismProperty.Over.w φ) C hC).exteriorIdentitySupport T)) :=
  componentGraphGeneratorOver_product_fundamental T φ C hC hCT

end Parameter

end MotivicTest.SimplexExteriorGraph

open Lean in
run_cmd do
  for name in #[
      `Motivic.FiniteCorrespondenceGenerator.inclusion_eq_projection_graph,
      `Motivic.FiniteCorrespondenceGenerator.eq_of_graph_range_eq,
      `Motivic.FiniteCorrespondenceGenerator.exteriorIdentityGenerator_projection_graph,
      `Motivic.componentGraphGeneratorOver_exteriorIdentityGenerator,
      `Motivic.componentGraphGeneratorOver_product_fundamental,
      `Motivic.FiniteCorrespondence.exteriorIdentity_componentGraphCycleOver,
      `Motivic.Cor.simplexExterior_graph,
      `MotivicTest.SimplexExteriorGraph.actual_simplex_graph,
      `MotivicTest.SimplexExteriorGraph.actual_signed_graph,
      `MotivicTest.SimplexExteriorGraph.actual_empty_source,
      `MotivicTest.SimplexExteriorGraph.actual_parameter_graph,
      `MotivicTest.SimplexExteriorGraph.actual_component_coefficient,
      `MotivicTest.SimplexExteriorGraph.actual_component_fundamental] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Exterior graph compatibility and consumers use only standard Lean foundations."

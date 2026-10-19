/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.GraphInterchange

/-!
# Consumers of actual mixed graph interchange

The field and smooth source and target are arbitrary. The tests retain the
original cosimplicial maps, all degrees, and arbitrary signed cycles, including
negative multiplicities. No categorical product in `Cor` is asserted.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open RingTheory.Sequence
open scoped Simplicial

universe u

namespace MotivicTest.SimplexExteriorGraphInterchange

variable {k : Type u} [Field k]

/-- Arbitrary original simplex maps intertwine all actual signed correspondences. -/
theorem actual_simplex_map {X Y : Cor k} {n m : ℕ}
    (u : _root_.AlgebraicSimplex.smoothSiteObj k n ⟶ _root_.AlgebraicSimplex.smoothSiteObj k m)
    (α : X ⟶ Y) :
    Cor.simplexExterior n α ≫
      (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 Y.toSmoothSite) u) =
      (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) u) ≫
        Cor.simplexExterior m α :=
  Cor.simplexExterior_graph_interchange u α

/-- Cofaces and codegeneracies use the literal existing cosimplicial scheme maps. -/
theorem actual_cosimplicial_map {X Y : Cor k} {p q : SimplexCategory}
    (f : p ⟶ q) (α : X ⟶ Y) :
    Cor.simplexExterior p.len α ≫
      (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 Y.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)) =
      (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)) ≫
        Cor.simplexExterior q.len α :=
  Cor.simplexExterior_graph_interchange _ α

/-- Negative coefficients and subtraction retain the same geometric interchange law. -/
theorem actual_signed_combination {X Y : Cor k} {n m : ℕ}
    (u : _root_.AlgebraicSimplex.smoothSiteObj k n ⟶ _root_.AlgebraicSimplex.smoothSiteObj k m)
    (α β : X ⟶ Y) :
    Cor.simplexExterior n (α - 3 • β) ≫
      (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 Y.toSmoothSite) u) =
      (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) u) ≫
        Cor.simplexExterior m (α - 3 • β) :=
  Cor.simplexExterior_graph_interchange u (α - 3 • β)

/-- Actual mixed incidence has full fundamental multiplicities without support flatness. -/
theorem actual_mixed_fundamental
    {X Y T T' : SmoothSite (Spec (.of k))} (u : T ⟶ T')
    [GeometricallyIntegral T'.hom]
    (V : FiniteCorrespondenceGenerator X.hom Y.hom)
    (A : FiniteCorrespondenceGenerator (SmoothSite.product X T).hom
      (SmoothSite.product X T').hom) [IsOpenImmersion A.projection]
    (hA : A.projection ≫ (SmoothSite.productMap (𝟙 X) u).left = A.targetProjection) :
    A.incidenceTorCorrespondence k (V.exteriorIdentityGenerator T') =
      A.incidenceFundamentalCorrespondence k (V.exteriorIdentityGenerator T') :=
  SimplexExteriorGraph.incidenceTorCorrespondence_eq_fundamental u V A hA

end MotivicTest.SimplexExteriorGraphInterchange

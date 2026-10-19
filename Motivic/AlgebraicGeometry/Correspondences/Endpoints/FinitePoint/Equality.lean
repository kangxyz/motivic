/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Cycle
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Relative.GeneratorComposition

/-!
# Original relative endpoints of signed finite point cycles

Graph precomposition is computed on the actual finite-image generators of the
original point-cycle assembly. Every original signed coefficient and residue
degree is retained, including collisions. Each generator contributes its whole
scheme-theoretic endpoint fiber, with no flatness hypothesis on its projection.

This is a linearization of the native generator endpoint theorem. Identifying
the resulting signed fiber sum with a specialized principal order cycle is a
separate local-length comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open scoped BigOperators

universe u

namespace Motivic.FinitePointCycleCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  {C V : Scheme.{u}} (q : C ⟶ relativeLine X.hom) (j : V ⟶ C) [IsOpenImmersion j]
  (c : FiniteSupportCycle C)
  (hretained : ∀ x : c.support,
    Set.range (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ⊆ Set.range j)
  (hfinite : ∀ x : c.support,
    IsFinite ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q))
  (hdominant : ∀ x : c.support,
    Set.range ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q) ∈
      irreducibleComponents (relativeLine X.hom))
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ relativeLineHom X.hom = g ≫ Y.hom)

local instance : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

/-- The original graph endpoint of the signed point-cycle correspondence is
its weighted sum of complete generator fibers. Scalar regularity on each
integral generator follows from its proved component dominance in the lower
endpoint theorem; no family or component flatness is supplied. -/
theorem toIntegralCycle_graph_endpoint (a : k) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (endpointMorphism X a) ≫
        correspondence (X := relativeLineSite X) q j c hretained hfinite hdominant g hbase) =
      ∑ x : c.support,
        (c x.val * ((productMap (X := relativeLineSite X) q j c hretained g hbase x).residueDegree
          (genericPoint (supportScheme c x)) : ℤ)) •
        IntegralCycle.finitePushforward
          ((generator (X := relativeLineSite X) q j c hretained hfinite hdominant
            g hbase x).graphPullbackMap (endpoint X.hom a) (endpoint_base X.hom a))
          (fundamentalCycle
            ((generator (X := relativeLineSite X) q j c hretained hfinite hdominant
              g hbase x).graphPullback (endpoint X.hom a))) := by
  classical
  have he : correspondence (X := relativeLineSite X) q j c hretained hfinite hdominant g hbase =
      ∑ x : c.support,
        (c x.val * ((productMap (X := relativeLineSite X) q j c hretained g hbase x).residueDegree
          (genericPoint (supportScheme c x)) : ℤ)) •
        (show Cor.mk (relativeLineSite X) ⟶ Cor.mk Y from
          (generator (X := relativeLineSite X) q j c hretained hfinite hdominant
            g hbase x).cycle) := by
    simp only [correspondence, FiniteCorrespondenceGenerator.cycle]
    apply Finset.sum_congr rfl
    intro x _
    change Finsupp.single _ _ =
      (_ : ℤ) • (Finsupp.single _ 1 :
        FiniteCorrespondenceGenerator (relativeLineHom X.hom) Y.hom →₀ ℤ)
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he, Preadditive.comp_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Preadditive.comp_zsmul, map_zsmul, toIntegralCycle_graph_endpoint_generator]
  rfl

end Motivic.FinitePointCycleCorrespondence

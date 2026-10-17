import Motivic.AlgebraicGeometry.Correspondences.FlatGraphPointControl

/-! Actual support points, disconnected sources, signed coefficients, and
designated target centers under pointed étale refinement. -/

set_option linter.hashCommand false

open CategoryTheory AlgebraicGeometry Motivic

universe u

variable {k : Type u} [Field k] {U X V : SmoothSite (Spec (.of k))}

example (β : FiniteCorrespondence X.hom V.hom) (g : U ⟶ X) [Etale g.left]
    (x : X.left) (x' : U.left) (hx : g.left x' = x) (v : V.left)
    (hv : ∀ A ∈ β.support, ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a = v)
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ ((Cor.graphFunctor k).map g ≫ β).support)
    (z : B.scheme) (hz : B.projection z = x') : B.targetProjection z = v :=
  FiniteCorrespondence.target_eq_of_mem_flat_graph_comp β g x x' hx v hv B hB z hz

example (β : FiniteCorrespondence X.hom V.hom) (g : U ⟶ X) [Etale g.left]
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ ((Cor.graphFunctor k).map g ≫
      (show Cor.mk X ⟶ Cor.mk V from -β)).support) (z : B.scheme) :
    ∃ A ∈ β.support, ∃ a : A.scheme,
      A.projection a = g.left (B.projection z) ∧
      A.targetProjection a = B.targetProjection z := by
  obtain ⟨A, hA, a, hs, ht⟩ :=
    FiniteCorrespondence.exists_support_point_lift_of_mem_flat_graph_comp (-β) g B hB z
  exact ⟨A, by simpa only [Finsupp.support_neg] using hA, a, hs, ht⟩

#print axioms IntegralCycle.range_subschemeι_subset_of_mem_finitePushforward
#print axioms FiniteCorrespondenceGenerator.exists_point_lift_of_mem_flat_graph_comp_cycle
#print axioms FiniteCorrespondence.exists_support_point_lift_of_mem_flat_graph_comp
#print axioms FiniteCorrespondence.target_mem_of_mem_flat_graph_comp
#print axioms FiniteCorrespondence.target_eq_of_mem_flat_graph_comp

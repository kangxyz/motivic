import Motivic.AlgebraicGeometry.Correspondences.Composition.PointControl

/-! Actual point provenance and nested designated centers for the original
signed correspondence composition, with no integral-object hypotheses. -/

set_option linter.hashCommand false

open CategoryTheory AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

universe u

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}

example (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom)
    (C : FiniteCorrespondenceGenerator X.hom Z.hom)
    (hC : C ∈ ((show Cor.mk X ⟶ Cor.mk Y from -α) ≫
      (show Cor.mk Y ⟶ Cor.mk Z from -β)).support) (c : C.scheme) :
    ∃ A ∈ α.support, ∃ B ∈ β.support, ∃ a : A.scheme, ∃ b : B.scheme,
      A.projection a = C.projection c ∧
      A.targetProjection a = B.projection b ∧
      B.targetProjection b = C.targetProjection c := by
  obtain ⟨A, hA, B, hB, a, b, hs, hm, ht⟩ :=
    FiniteCorrespondence.exists_support_points_lift_of_mem_comp (-α) (-β) C hC c
  exact ⟨A, by simpa only [Finsupp.support_neg] using hA,
    B, by simpa only [Finsupp.support_neg] using hB, a, b, hs, hm, ht⟩

example (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom)
    (x : X.left) (y : Y.left) (z : Z.left)
    (hy : ∀ A ∈ α.support, ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a = y)
    (hz : ∀ B ∈ β.support, ∀ b : B.scheme,
      B.projection b = y → B.targetProjection b = z)
    (C : FiniteCorrespondenceGenerator X.hom Z.hom)
    (hC : C ∈ ((show Cor.mk X ⟶ Cor.mk Y from α) ≫ β).support)
    (c : C.scheme) (hc : C.projection c = x) :
    C.targetProjection c = z :=
  FiniteCorrespondence.target_eq_of_mem_comp α β x y z hy hz C hC c hc

#print axioms FiniteCorrespondenceGenerator.exists_incidence_point_of_mem_cycle_comp_cycle
#print axioms FiniteCorrespondenceGenerator.exists_points_lift_of_mem_cycle_comp_cycle
#print axioms FiniteCorrespondence.exists_support_points_lift_of_mem_comp
#print axioms FiniteCorrespondence.target_mem_of_mem_comp
#print axioms FiniteCorrespondence.target_eq_of_mem_comp

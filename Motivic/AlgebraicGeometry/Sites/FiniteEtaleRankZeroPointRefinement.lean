/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointOpenRefinement
public import Motivic.AlgebraicGeometry.SmoothSiteRankZeroOpen

/-! # Integral affine refinements of actual rank-zero field-point neighborhoods

The field marker is retained in the existing point's category of elements.
The field spectrum is never asserted to be a smooth finite-type object.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))

/-- The actual field marker in every original etale neighborhood has the same
local rank as its center, by the original etale stalk map. -/
theorem fieldPoint_stalk_rank_eq (V : FiniteEtaleSite X.left)
    (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V) :
    ringKrullDim (V.left.presheaf.stalk
      ((relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p)) =
      ringKrullDim (X.left.presheaf.stalk (b p)) := by
  let t := (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left
  have ht : (show V.left ⟶ X.left from V.hom) (t p) = b p := by
    have he := congrArg (fun f : Spec (.of K) ⟶ X.left => f p)
      (Over.w (relativeFieldPointFiberEquiv b K (𝟙 _) V a))
    change (show V.left ⟶ X.left from V.hom) (t p) = (𝟙 _ ≫ b) p at he
    simpa only [Category.id_comp] using he
  rw [Scheme.ringKrullDim_stalk_eq_of_etale
    (show V.left ⟶ X.left from V.hom) (t p), ht]

/-- On an integral original neighborhood, a rank-zero field marker is its
actual generic point, including markers with nontrivial residue extensions. -/
theorem fieldPoint_eq_genericPoint_of_rank_zero
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = 0)
    (V : FiniteEtaleSite X.left) [IsIntegral V.left]
    (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V) :
    (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p = genericPoint V.left := by
  apply Scheme.eq_genericPoint_of_stalk_rank_zero (X := V.left)
  exact (fieldPoint_stalk_rank_eq X K b p V a).trans hd

include p in
/-- An actual integral affine open containing the marker refines the original
point index by its original open inclusion and preserves the complete field mark. -/
theorem exists_integral_affine_point_open_refinement
    (V : FiniteEtaleSite X.left) [IsNoetherian V.left]
    (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V) :
    ∃ O : V.left.Opens, IsAffineOpen O ∧ IsIntegral O.toScheme ∧
      ∃ a' : (relativeFieldPoint b K (𝟙 _)).fiber.obj (testOpenObject V O),
        (relativeFieldPoint b K (𝟙 _)).fiber.map (testOpenInclusion V O) a' = a := by
  obtain ⟨O, hO, ht, hI⟩ := SmoothSite.exists_integral_affine_open
    ((toSmoothSite X).obj V) ((relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p)
  obtain ⟨a', ha'⟩ := exists_point_open_refinement_of_mem K b V a p O ht
  exact ⟨O, hO, hI, a', ha'⟩

end Motivic.FiniteEtaleSite

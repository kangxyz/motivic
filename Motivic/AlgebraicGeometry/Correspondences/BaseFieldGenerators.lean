/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraph

/-!
# Actual finite correspondences from the base field to itself

Every integral closed support in the self-product of an integral base, finite
and surjective over that base, is its actual diagonal support. This follows
from equality of the graph projection relations and their full source images.
Consequently the geometric generator type has exactly one element, and every
signed correspondence from a field base to itself is a unique integer multiple
of the categorical identity. No separability hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator

variable {S : Scheme.{u}} [IsIntegral S]

/-- The unique actual elementary correspondence over an integral base is its diagonal. -/
theorem eq_identityGenerator_of_base (A : FiniteCorrespondenceGenerator (𝟙 S) (𝟙 S)) :
    A = identityGenerator (𝟙 S) := by
  apply eq_of_graph_range_eq (𝟙 S) (Category.id_comp (𝟙 S))
  · simpa only [Category.comp_id] using A.projection_base
  · simp only [Category.comp_id, identityGenerator_targetProjection]
  · rw [Set.range_eq_univ.mpr A.projection_surjective,
      Set.range_eq_univ.mpr (identityGenerator (𝟙 S)).projection_surjective]

/-- Actual integral closed supports over the identity base have no distinct choices. -/
instance baseGeneratorSubsingleton :
    Subsingleton (FiniteCorrespondenceGenerator (𝟙 S) (𝟙 S)) where
  allEq A B := A.eq_identityGenerator_of_base.trans B.eq_identityGenerator_of_base.symm

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

variable {S : Scheme.{u}} [IsIntegral S]

/-- The sole geometric coefficient determines every signed cycle over an integral base. -/
theorem eq_coefficient_zsmul_identity_cycle (α : FiniteCorrespondence (𝟙 S) (𝟙 S)) :
    α = α (identityGenerator (𝟙 S)) • (identityGenerator (𝟙 S)).cycle := by
  ext A
  rw [A.eq_identityGenerator_of_base]
  simp

end FiniteCorrespondence

namespace Cor

variable {k : Type u} [Field k]

/-- The categorical identity over a field is the cycle of its actual diagonal generator. -/
theorem base_id_eq_identityGenerator_cycle :
    (𝟙 (Cor.mk (SmoothSite.base (Spec (.of k))))) =
      (identityGenerator (𝟙 (Spec (.of k)))).cycle :=
  componentIdentityCycle_eq_identityGenerator_cycle (X := Spec (.of k)) _

/-- Every actual base-field endomorphism is its diagonal coefficient times the identity. -/
theorem base_endomorphism_eq_coefficient_zsmul_id
    (α : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.base (Spec (.of k)))) :
    α = Finsupp.toFun α
      (identityGenerator (𝟙 (Spec (.of k)))) •
      𝟙 (Cor.mk (SmoothSite.base (Spec (.of k)))) := by
  rw [base_id_eq_identityGenerator_cycle]
  exact FiniteCorrespondence.eq_coefficient_zsmul_identity_cycle (S := Spec (.of k)) α

/-- The scalar of a signed base-field correspondence is unique. -/
theorem base_endomorphism_existsUnique_zsmul_id
    (α : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.base (Spec (.of k)))) :
    ∃! n : ℤ, α = n • 𝟙 (Cor.mk (SmoothSite.base (Spec (.of k)))) := by
  refine ⟨Finsupp.toFun α
      (identityGenerator (𝟙 (Spec (.of k)))),
    base_endomorphism_eq_coefficient_zsmul_id α, ?_⟩
  intro n hn
  have h := congrArg
    (fun β : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.base (Spec (.of k))) =>
      Finsupp.toFun β
        (identityGenerator (𝟙 (Spec (.of k))))) hn
  rw [base_id_eq_identityGenerator_cycle] at h
  change Finsupp.toFun α (identityGenerator (𝟙 (Spec (.of k)))) =
    (n • (identityGenerator (𝟙 (Spec (.of k)))).cycle)
      (identityGenerator (𝟙 (Spec (.of k)))) at h
  simpa using h.symm

end Cor

end Motivic

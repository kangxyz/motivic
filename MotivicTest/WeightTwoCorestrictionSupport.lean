/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionSupport
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual corestriction support morphism

The degree-one source is the original integral support, and the target is the
literal finite-image generator. No reduction, separability, or generic-degree
hypothesis is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic WeightTwoCorestriction

universe u

namespace MotivicTest.WeightTwoCorestrictionSupport

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
variable (q : ℕ)
variable (A : FiniteCorrespondenceGenerator (source E 1).hom (target E q).hom)

/-- The original support maps finitely and surjectively to its actual image. -/
theorem actual_support_map :
    IsFinite (supportMap (k := k) 1 q A) ∧
      Function.Surjective (supportMap (k := k) 1 q A) :=
  ⟨inferInstance, supportMap_surjective 1 q A⟩

/-- The inclusion square is the original square of scheme morphisms. -/
theorem actual_inclusion_square :
    supportMap (k := k) 1 q A ≫ (imageGenerator (k := k) 1 q A).inclusion =
      A.inclusion ≫ ambientMap (k := k) (E := E) 1 q :=
  supportMap_inclusion 1 q A

/-- The projection square keeps the canonical scalar projection. -/
theorem actual_projection_square :
    supportMap (k := k) 1 q A ≫ (imageGenerator (k := k) 1 q A).projection =
      A.projection ≫ sourceMap (k := k) (E := E) 1 :=
  supportMap_projection 1 q A

/-- The generic degree belongs to the original support and embedded generic point. -/
theorem actual_generic_degree :
    (supportMap (k := k) 1 q A).residueDegree (genericPoint A.scheme) =
      (ambientMap (k := k) (E := E) 1 q).residueDegree A.point :=
  supportMap_residueDegree 1 q A

open Lean in
run_cmd do
  for name in #[``supportMap, ``supportMap_inclusion, ``supportMap_projection,
      ``supportMap_isFinite, ``supportMap_surjective, ``supportMap_isSurjective,
      ``supportMap_genericPoint, ``supportMap_residueDegree,
      ``actual_support_map, ``actual_inclusion_square, ``actual_projection_square,
      ``actual_generic_degree] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The actual corestriction support map uses only standard foundations."

end MotivicTest.WeightTwoCorestrictionSupport

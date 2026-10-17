/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Components
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceCycle
public import Motivic.AlgebraicGeometry.Correspondences.Category

/-!
# Whole finite-flat schemes as finite correspondences

A finite flat source map and an arbitrary map to a separated finite-type target
define a genuine finite correspondence. Every generic component contributes its
original local length times its actual finite-image residue degree. The source
may be disconnected, and the finite scheme and its fibers may be nonreduced.
The map into the product need not be a closed immersion or injective on generic
components. No dominance or correspondence-admissibility hypothesis is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteFlatCorrespondence

variable {S X Y D : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
  [IsSeparated q] [LocallyOfFiniteType q]
  (f : D ⟶ X) [IsFinite f] [Flat f]
  (j : D ⟶ pullback p q) (hj : j ≫ pullback.fst p q = f)

include hj in
omit [LocallyOfFiniteType q] [Flat f] in
/-- The actual product map is finite because its first projection is finite
and the target is separated over the common base. -/
theorem isFinite_productMap : IsFinite j := by
  have : IsFinite (j ≫ pullback.fst p q) := hj ▸ inferInstance
  exact IsFinite.of_comp j (pullback.fst p q)

variable [IsFinite j]

/-- A component of the whole finite-flat source gives its literal admissible
finite image, even when the source base has several components. -/
def componentGenerator (z : genericPoints D) : FiniteCorrespondenceGenerator p q := by
  let C := IntegralClosedSubscheme.pointClosure z.val
  let e := C.val.subschemeι ≫ j
  have : IsFinite (e ≫ pullback.fst p q) := by
    dsimp only [e]
    rw [Category.assoc, hj]
    infer_instance
  refine ⟨(C.finiteImage j).val, (C.finiteImage j).property,
    isFinite_image_projection e (pullback.fst p q), ?_⟩
  change Set.range (e.imageι ≫ pullback.fst p q) ∈ irreducibleComponents X
  rw [range_image_projection]
  change Set.range ((C.val.subschemeι ≫ j) ≫ pullback.fst p q) ∈ _
  rw [Category.assoc, hj]
  change Set.range (f ∘ C.val.subschemeι) ∈ _
  rw [Set.range_comp, C.val.range_subschemeι]
  exact f.image_closure_mem_irreducibleComponents_of_finite_flat z.val z.property

/-- Forgetting admissibility preserves the exact finite-image ideal. -/
@[simp]
theorem toIntegralClosedSubscheme_componentGenerator (z : genericPoints D) :
    (componentGenerator f j hj z).toIntegralClosedSubscheme =
      (IntegralClosedSubscheme.pointClosure z.val).finiteImage j := rfl

variable [IsNoetherian D]

/-- Arbitrary signed generic coefficients assemble with their actual residue
degrees. Components with a common image are added rather than identified. -/
def cycleAssembly : (genericPoints D → ℤ) →+ FiniteCorrespondence p q := by
  classical
  letI := IntegralCycle.genericPointFintype D
  exact
    { toFun := fun c => ∑ z, Finsupp.single (componentGenerator f j hj z)
        (c z * (j.residueDegree z.val : ℤ))
      map_zero' := by simp
      map_add' := by intro c d; simp [add_mul, Finsupp.single_add, Finset.sum_add_distrib] }

open Classical in
/-- All original components with the same image contribute to its coefficient. -/
theorem cycleAssembly_coefficient (c : genericPoints D → ℤ)
    (V : FiniteCorrespondenceGenerator p q) :
    cycleAssembly f j hj c V =
      letI := IntegralCycle.genericPointFintype D
      ∑ z, if componentGenerator f j hj z = V then
        c z * (j.residueDegree z.val : ℤ) else 0 := by
  let := IntegralCycle.genericPointFintype D
  change (∑ z, Finsupp.single (componentGenerator f j hj z)
    (c z * (j.residueDegree z.val : ℤ))) V = _
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

/-- The assembly retains the literal finite pushforward of the original
component cycle, including collisions of distinct component images. -/
theorem toIntegralCycle_cycleAssembly (c : genericPoints D → ℤ) :
    FiniteCorrespondence.toIntegralCycle (cycleAssembly f j hj c) =
      IntegralCycle.finitePushforward j (IntegralCycle.ofGenericCoefficients D c) := by
  classical
  let := IntegralCycle.genericPointFintype D
  rw [IntegralCycle.ofGenericCoefficients_eq_sum, map_sum]
  change FiniteCorrespondence.toIntegralCycle
    (∑ z, Finsupp.single (componentGenerator f j hj z)
      (c z * (j.residueDegree z.val : ℤ))) = _
  rw [map_sum]
  simp only [FiniteCorrespondence.toIntegralCycle_single,
    toIntegralClosedSubscheme_componentGenerator, IntegralCycle.finitePushforward_single,
    IntegralClosedSubscheme.point_pointClosure]

/-- The whole finite-flat scheme, with every original generic local length,
defines an actual finite correspondence. -/
def fundamentalCorrespondence : FiniteCorrespondence p q :=
  cycleAssembly f j hj (fun z => (genericMultiplicity z : ℤ))

/-- The faithful underlying cycle is exactly the whole fundamental-cycle
pushforward. No reducedness or componentwise injectivity is required. -/
theorem toIntegralCycle_fundamentalCorrespondence :
    FiniteCorrespondence.toIntegralCycle (fundamentalCorrespondence f j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle D) := by
  rw [fundamentalCorrespondence, toIntegralCycle_cycleAssembly,
    IntegralCycle.ofGenericCoefficients_genericMultiplicity]

/-- Empty finite-flat supports define the zero correspondence. -/
@[simp]
theorem fundamentalCorrespondence_eq_zero_of_isEmpty [IsEmpty D] :
    fundamentalCorrespondence f j hj = 0 := by
  classical
  simp [fundamentalCorrespondence, cycleAssembly]

end Motivic.FiniteFlatCorrespondence

namespace Motivic.Cor

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ X.left) [IsFinite f] [Flat f]
  (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom)

/-- The literal finite-flat span defines a morphism in the existing `Cor`
category, with no irreducibility requirement on the smooth source. -/
def ofFiniteFlatSpan : Cor.mk X ⟶ Cor.mk Y := by
  have : IsNoetherian D := isNoetherian_of_finiteType f
  have : IsFinite (pullback.lift f g h) :=
    FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
  exact FiniteFlatCorrespondence.fundamentalCorrespondence f (pullback.lift f g h)
    (pullback.lift_fst _ _ _)

/-- The actual `Cor` morphism retains the entire finite scheme's fundamental
cycle under its canonical map to the source-target product. -/
theorem toIntegralCycle_ofFiniteFlatSpan :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      (ofFiniteFlatSpan f g h) =
      letI : IsFinite (pullback.lift f g h) :=
        FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
      letI : IsNoetherian D := isNoetherian_of_finiteType f
      IntegralCycle.finitePushforward (pullback.lift f g h) (fundamentalCycle D) := by
  have : IsNoetherian D := isNoetherian_of_finiteType f
  have : IsFinite (pullback.lift f g h) :=
    FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
  exact FiniteFlatCorrespondence.toIntegralCycle_fundamentalCorrespondence f _ _

end Motivic.Cor

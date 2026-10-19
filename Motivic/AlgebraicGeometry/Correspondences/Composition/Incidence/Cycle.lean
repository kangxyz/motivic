/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericCoefficients

public import Motivic.AlgebraicGeometry.Correspondences.Support.ComponentDominance
public import Motivic.AlgebraicGeometry.Correspondences.Support.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.CorrespondenceCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalCycle
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.ResidueDegree

/-!
# Finite-cycle assembly on genuine correspondence incidence

Integer coefficients on the finitely many generic points of the actual
incidence scheme assemble additively into finite correspondences. Each term
uses the proved admissible finite image and the actual residue-field degree
of the incidence map. Several components may have the same image; their
weighted coefficients are added, rather than choosing one component.

The faithful forgetful map identifies this assembly with actual finite
pushforward of the corresponding integral component cycle. Applying it to
the incidence scheme's generic local lengths recovers the pushforward of its
ordinary fundamental cycle. Neither arbitrary input coefficients nor these
ordinary local lengths are identified here with derived-intersection
multiplicities. Correspondence composition and its laws remain separate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic


namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable (k : Type u) [Field k]
  {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Smooth source finiteness makes the genuine incidence Noetherian. -/
instance isNoetherian_smoothIncidence : IsNoetherian (A.incidence B) := by
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (A.incidenceSource B)

/-- The actual incidence generic points are finite, by finite type over the smooth source. -/
theorem finite_incidence_genericPoints : (genericPoints (A.incidence B)).Finite :=
  genericPoints.finite finite_irreducibleComponents_of_isNoetherian

/-- Forgetting admissibility retains the literal integral finite image. -/
@[simp]
theorem toIntegralClosedSubscheme_smoothIncidenceComponentGenerator
    (x : genericPoints (A.incidence B)) :
    (A.smoothIncidenceComponentGenerator k B x).toIntegralClosedSubscheme =
      (IntegralClosedSubscheme.pointClosure x.val).finiteImage (A.incidenceMap B) := by
  apply Subtype.ext
  exact A.smoothIncidenceComponentGenerator_val k B x

/-- Additive finite-image assembly for arbitrary integer coefficients on actual incidence
components. The coefficients are inputs, not assertions of intersection multiplicities. -/
noncomputable def incidenceCycleAssembly :
    (genericPoints (A.incidence B) → ℤ) →+ FiniteCorrespondence X.hom Z.hom := by
  classical
  letI := IntegralCycle.genericPointFintype (A.incidence B)
  exact
    { toFun := fun c => ∑ x, Finsupp.single (A.smoothIncidenceComponentGenerator k B x)
        (c x * ((A.incidenceMap B).residueDegree x.val : ℤ))
      map_zero' := by simp
      map_add' := by intro c d; simp [add_mul, Finsupp.single_add, Finset.sum_add_distrib] }

/-- The assembly is the sum of the actual degree-weighted finite images. -/
theorem incidenceCycleAssembly_eq_sum (c : genericPoints (A.incidence B) → ℤ) :
    A.incidenceCycleAssembly k B c =
      letI := IntegralCycle.genericPointFintype (A.incidence B)
      ∑ x, Finsupp.single (A.smoothIncidenceComponentGenerator k B x)
        (c x * ((A.incidenceMap B).residueDegree x.val : ℤ)) := rfl

open Classical in
/-- All components with a common image contribute to that image's coefficient. -/
theorem incidenceCycleAssembly_coefficient (c : genericPoints (A.incidence B) → ℤ)
    (V : FiniteCorrespondenceGenerator X.hom Z.hom) :
    A.incidenceCycleAssembly k B c V =
      letI := IntegralCycle.genericPointFintype (A.incidence B)
      ∑ x, if A.smoothIncidenceComponentGenerator k B x = V then
        c x * ((A.incidenceMap B).residueDegree x.val : ℤ) else 0 := by
  rw [incidenceCycleAssembly_eq_sum, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

/-- Every degree appearing in the assembly is a positive finite extension degree. -/
theorem incidence_residueDegree_pos (x : genericPoints (A.incidence B)) :
    0 < (A.incidenceMap B).residueDegree x.val := residueDegree_pos _ _

/-- The actual correspondence assembly is exactly finite pushforward under the faithful
forgetful map, without an injectivity assumption on the component-image function. -/
theorem toIntegralCycle_incidenceCycleAssembly (c : genericPoints (A.incidence B) → ℤ) :
    FiniteCorrespondence.toIntegralCycle (A.incidenceCycleAssembly k B c) =
      IntegralCycle.finitePushforward (A.incidenceMap B)
        (IntegralCycle.ofGenericCoefficients (A.incidence B) c) := by
  classical
  let := IntegralCycle.genericPointFintype (A.incidence B)
  rw [incidenceCycleAssembly_eq_sum, IntegralCycle.ofGenericCoefficients_eq_sum,
    map_sum, map_sum]
  simp only [FiniteCorrespondence.toIntegralCycle_single,
    toIntegralClosedSubscheme_smoothIncidenceComponentGenerator,
    IntegralCycle.finitePushforward_single, IntegralClosedSubscheme.point_pointClosure]

/-- Equality of assembled correspondences can be checked by their actual integral pushforwards. -/
theorem incidenceCycleAssembly_eq_iff (c d : genericPoints (A.incidence B) → ℤ) :
    A.incidenceCycleAssembly k B c = A.incidenceCycleAssembly k B d ↔
      IntegralCycle.finitePushforward (A.incidenceMap B)
        (IntegralCycle.ofGenericCoefficients (A.incidence B) c) =
      IntegralCycle.finitePushforward (A.incidenceMap B)
        (IntegralCycle.ofGenericCoefficients (A.incidence B) d) := by
  rw [← toIntegralCycle_incidenceCycleAssembly, ← toIntegralCycle_incidenceCycleAssembly]
  exact FiniteCorrespondence.toIntegralCycle_injective.eq_iff.symm

/-- The ordinary incidence fundamental cycle gives a genuine finite correspondence. -/
noncomputable def incidenceFundamentalCorrespondence : FiniteCorrespondence X.hom Z.hom :=
  A.incidenceCycleAssembly k B (fun x => (genericMultiplicity x : ℤ))

/-- Its forgotten cycle is exactly the finite pushforward of the genuine, possibly
nonreduced incidence fundamental cycle. This is not a derived-intersection comparison. -/
theorem toIntegralCycle_incidenceFundamentalCorrespondence :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (A.incidenceFundamentalCorrespondence k B) =
      IntegralCycle.finitePushforward (A.incidenceMap B) (fundamentalCycle (A.incidence B)) := by
  rw [incidenceFundamentalCorrespondence, toIntegralCycle_incidenceCycleAssembly,
    IntegralCycle.ofGenericCoefficients_genericMultiplicity]

end FiniteCorrespondenceGenerator

end Motivic

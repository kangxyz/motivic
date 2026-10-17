/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleIncidenceTor
public import Motivic.AlgebraicGeometry.Correspondences.TripleGenericDominance
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceCycle

/-!
# The actual canonical triple-incidence total Tor cycle

Generic coefficients are the categorical Tor lengths of the original exterior
support and actual combined two-diagonal source in the six-factor ambient.
The genuine finite triple-incidence map assembles them into a finite
correspondence, with actual residue degrees and all colliding images summed.
This constructs the common target for a future comparison of the two
parenthesizations; no such comparison or associativity is an input or conclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- Actual triple incidence is Noetherian because it is finite over the smooth source. -/
instance isNoetherian_smoothTripleIncidence : IsNoetherian (F.tripleIncidence G H) := by
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (F.tripleIncidenceSource G H)

/-- Every actual generic triple component gives its genuine admissible finite image. -/
def smoothTripleIncidenceComponentGenerator (x : genericPoints (F.tripleIncidence G H)) :
    FiniteCorrespondenceGenerator X.hom W.hom := by
  let C := IntegralClosedSubscheme.pointClosure x.val
  have hfin : IsFinite
      (correspondenceProjection X.hom W.hom (C.finiteImage (F.tripleIncidenceMap G H)).val) := by
    have : IsFinite ((C.val.subschemeι ≫ F.tripleIncidenceMap G H) ≫
        pullback.fst X.hom W.hom) := by
      simpa only [Category.assoc, tripleIncidenceMap_fst] using
        (inferInstance : IsFinite (C.val.subschemeι ≫ F.tripleIncidenceSource G H))
    exact isFinite_image_projection (C.val.subschemeι ≫ F.tripleIncidenceMap G H)
      (pullback.fst X.hom W.hom)
  refine ⟨(C.finiteImage (F.tripleIncidenceMap G H)).val,
    (C.finiteImage (F.tripleIncidenceMap G H)).property, hfin, ?_⟩
  change Set.range ((C.val.subschemeι ≫ F.tripleIncidenceMap G H).imageι ≫
    pullback.fst X.hom W.hom) ∈ irreducibleComponents X.left
  rw [range_image_projection]
  simp only [Category.assoc, tripleIncidenceMap_fst]
  change Set.range ((F.tripleIncidenceSource G H) ∘ C.val.subschemeι) ∈ _
  rw [Set.range_comp, C.val.range_subschemeι]
  change (F.tripleIncidenceSource G H) '' closure ({x.val} : Set (F.tripleIncidence G H)) ∈ _
  rw [← (F.tripleIncidenceSource G H).isClosedMap.closure_image_eq_of_continuous
    (F.tripleIncidenceSource G H).continuous, Set.image_singleton]
  exact F.tripleIncidenceSource_mem_genericPoints k G H x.val x.property

/-- The new admissibility proof leaves the literal finite-image ideal sheaf unchanged. -/
@[simp]
theorem toIntegralClosedSubscheme_smoothTripleIncidenceComponentGenerator
    (x : genericPoints (F.tripleIncidence G H)) :
    (F.smoothTripleIncidenceComponentGenerator k G H x).toIntegralClosedSubscheme =
      (IntegralClosedSubscheme.pointClosure x.val).finiteImage (F.tripleIncidenceMap G H) := by
  apply Subtype.ext
  rfl

/-- All actual triple generic coefficients assemble with their own residue degrees. -/
def tripleIncidenceCycleAssembly :
    (genericPoints (F.tripleIncidence G H) → ℤ) →+ FiniteCorrespondence X.hom W.hom := by
  classical
  letI := IntegralCycle.genericPointFintype (F.tripleIncidence G H)
  exact
    { toFun := fun c => ∑ x, Finsupp.single (F.smoothTripleIncidenceComponentGenerator k G H x)
        (c x * ((F.tripleIncidenceMap G H).residueDegree x.val : ℤ))
      map_zero' := by simp
      map_add' := by intro c d; simp [add_mul, Finsupp.single_add, Finset.sum_add_distrib] }

/-- The actual degree-weighted finite sum retains every source generic point. -/
theorem tripleIncidenceCycleAssembly_eq_sum (c : genericPoints (F.tripleIncidence G H) → ℤ) :
    F.tripleIncidenceCycleAssembly k G H c =
      letI := IntegralCycle.genericPointFintype (F.tripleIncidence G H)
      ∑ x, Finsupp.single (F.smoothTripleIncidenceComponentGenerator k G H x)
        (c x * ((F.tripleIncidenceMap G H).residueDegree x.val : ℤ)) := rfl

/-- The genuine triple assembly forgets to actual integral-cycle finite pushforward. -/
theorem toIntegralCycle_tripleIncidenceCycleAssembly
    (c : genericPoints (F.tripleIncidence G H) → ℤ) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
      (F.tripleIncidenceCycleAssembly k G H c) =
      IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
        (IntegralCycle.ofGenericCoefficients (F.tripleIncidence G H) c) := by
  classical
  let := IntegralCycle.genericPointFintype (F.tripleIncidence G H)
  rw [tripleIncidenceCycleAssembly_eq_sum, IntegralCycle.ofGenericCoefficients_eq_sum,
    map_sum, map_sum]
  simp only [FiniteCorrespondence.toIntegralCycle_single,
    toIntegralClosedSubscheme_smoothTripleIncidenceComponentGenerator,
    IntegralCycle.finitePushforward_single, IntegralClosedSubscheme.point_pointClosure]

/-- The canonical total Tor cycle on the full scheme-theoretic triple incidence. -/
def tripleIncidenceTorCycle : IntegralCycle (F.tripleIncidence G H) :=
  IntegralCycle.ofGenericCoefficients (F.tripleIncidence G H)
    (F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H)

/-- The canonical total Tor correspondence is the genuine finite image of that cycle. -/
def tripleTorCorrespondence : FiniteCorrespondence X.hom W.hom :=
  F.tripleIncidenceCycleAssembly k G H (F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H)

/-- The canonical total correspondence has exactly the actual finite-pushforward cycle. -/
theorem toIntegralCycle_tripleTorCorrespondence :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
      (F.tripleTorCorrespondence k G H) =
      IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
        (F.tripleIncidenceTorCycle k G H) :=
  F.toIntegralCycle_tripleIncidenceCycleAssembly k G H _

open Classical in
/-- Distinct source components with the same output image contribute separately
with their canonical total Tor coefficients and actual residue-field degrees. -/
theorem tripleTorCorrespondence_coefficient
    (V : FiniteCorrespondenceGenerator X.hom W.hom) :
    F.tripleTorCorrespondence k G H V =
      letI := IntegralCycle.genericPointFintype (F.tripleIncidence G H)
      ∑ x, if F.smoothTripleIncidenceComponentGenerator k G H x = V then
        F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H x *
          ((F.tripleIncidenceMap G H).residueDegree x.val : ℤ) else 0 := by
  rw [tripleTorCorrespondence, tripleIncidenceCycleAssembly_eq_sum, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

end Motivic.FiniteCorrespondenceGenerator

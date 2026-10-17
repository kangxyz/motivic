/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyNisnevichOverlapLift
public import Motivic.Cohomology.RelativeSheafCohomologyComposition

/-! # Killing the actual overlap boundary by an étale-leg refinement -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w t u
namespace Motivic.SheafCohomology
variable {S : Scheme.{u}}
  {U X V V' : SmoothSite S} (j : U ⟶ X) (p : V ⟶ X) [IsOpenImmersion j.left]

/-- The actual pullback square, not an abstract replacement diagram. -/
abbrev ordinaryPullbackSquare : Square (SmoothSite S) where
  f₁₂ := pullback.fst j p
  f₁₃ := pullback.snd j p
  f₂₄ := j
  f₃₄ := p
  fac := pullback.condition

/-- The unchanged overlap map induced by a refinement of the étale leg. -/
def ordinaryOverlapMap (r : V' ⟶ V) : pullback j (r ≫ p) ⟶ pullback j p :=
  pullback.lift (pullback.fst j (r ≫ p)) (pullback.snd j (r ≫ p) ≫ r)
    (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)] theorem ordinaryOverlapMap_fst (r : V' ⟶ V) :
    ordinaryOverlapMap j p r ≫ pullback.fst j p = pullback.fst j (r ≫ p) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem ordinaryOverlapMap_snd (r : V' ⟶ V) :
    ordinaryOverlapMap j p r ≫ pullback.snd j p = pullback.snd j (r ≫ p) ≫ r :=
  pullback.lift_snd _ _ _

variable
  [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t})]
  {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range j.left)ᶜ)

local instance : Mono j := (SmoothSite.forgetScheme S).mono_of_mono_map (by
  change Mono j.left
  infer_instance)

include hcomp in
/-- A geometric refinement that kills the lifted overlap class kills the original
ordinary class. Both excision isomorphisms come from the actual Nisnevich squares. -/
theorem ordinary_eq_zero_of_overlap_refinement
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ)
    (e : H (SmoothSite.nisnevichTopology S) F (n + 1) X)
    (q : relativeH (SmoothSite.nisnevichTopology S) j F (n + 1))
    (f : H (SmoothSite.nisnevichTopology S) F n (pullback j p))
    (hq : relativeForget (SmoothSite.nisnevichTopology S) j F (n + 1) q = e)
    (hf : relativeRestriction (SmoothSite.nisnevichTopology S)
      (pullback.snd j p) j (pullback.fst j p) p pullback.condition.symm F (n + 1) q =
        relativeBoundary (SmoothSite.nisnevichTopology S) (pullback.snd j p) F n f)
    (r : V' ⟶ V) [Etale (r ≫ p).left]
    [IsIso (pullback.snd (r ≫ p).left z)]
    (hz : (presheaf (SmoothSite.nisnevichTopology S) F n).map
      (ordinaryOverlapMap j p r).op f = 0) : e = 0 := by
  let J := SmoothSite.nisnevichTopology S
  let a := ordinaryOverlapMap j p r
  have h : pullback.snd j (r ≫ p) ≫ r = a ≫ pullback.snd j p :=
    (ordinaryOverlapMap_snd j p r).symm
  have h' : pullback.snd j p ≫ p = pullback.fst j p ≫ j := pullback.condition.symm
  have h'' : pullback.snd j (r ≫ p) ≫ (r ≫ p) = (a ≫ pullback.fst j p) ≫ j := by
    rw [ordinaryOverlapMap_fst]
    exact pullback.condition.symm
  have hiso : IsIso (relativeRestriction J (pullback.snd j (r ≫ p)) j
      (a ≫ pullback.fst j p) (r ≫ p) h'' F (n + 1)) := by
    simpa only [a, ordinaryOverlapMap_fst] using
      isIso_relativeRestriction_nisnevich (ordinaryPullbackSquare j (r ≫ p))
        (IsPullback.of_hasPullback _ _) z hcomp F (n + 1)
  have hqzero := relative_eq_zero_of_boundary_refinement J
    (pullback.snd j (r ≫ p)) (pullback.snd j p) j a r h
    (pullback.fst j p) p h' h'' F n q f hf hz
  rw [← hq, hqzero, map_zero]

end Motivic.SheafCohomology

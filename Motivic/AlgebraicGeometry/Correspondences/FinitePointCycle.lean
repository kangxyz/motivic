/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FiniteSupport
public import Motivic.AlgebraicGeometry.Cycles.FundamentalSupport
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlat

/-!
# Actual finite point-cycle correspondence assembly

Each original integral support is mapped through the retained open and pushed
to its literal finite image. The original coefficient and residue degree are
retained, including additive collisions. Geometric consumers prove the support
finiteness and component dominance; flatness is not required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FinitePointCycleCorrespondence

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {C V : Scheme.{u}} (q : C ⟶ X.left) (j : V ⟶ C) [IsOpenImmersion j]
  (c : FiniteSupportCycle C)
  (hretained : ∀ x : c.support,
    Set.range (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ⊆ Set.range j)
  (hfinite : ∀ x : c.support,
    IsFinite ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q))
  (hdominant : ∀ x : c.support,
    Set.range ((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q) ∈
      irreducibleComponents X.left)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

/-- The original integral point closure, before taking any finite image. -/
abbrev supportScheme (x : c.support) : Scheme.{u} :=
  (IntegralClosedSubscheme.pointClosure x.val).val.subscheme

/-- The original support maps through the retained open into the target product. -/
def productMap (x : c.support) : supportScheme c x ⟶ pullback X.hom Y.hom := by
  let d := (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι
  let a := IsOpenImmersion.lift j d (hretained x)
  have ha : a ≫ j = d := IsOpenImmersion.lift_fac j d _
  exact pullback.lift (d ≫ q) (a ≫ g) (by
    rw [← ha]
    simp only [Category.assoc, hbase])

@[simp]
theorem productMap_fst (x : c.support) :
    productMap q j c hretained g hbase x ≫ pullback.fst X.hom Y.hom =
      (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ q :=
  pullback.lift_fst _ _ _

include hfinite in
/-- Finiteness follows from the original whole support over the source. -/
theorem productMap_isFinite (x : c.support) :
    IsFinite (productMap q j c hretained g hbase x) := by
  have := hfinite x
  exact FiniteFlatCorrespondence.isFinite_productMap _ _
    (productMap_fst q j c hretained g hbase x)

/-- The literal finite-image generator retains the proved component image. -/
def generator (x : c.support) : FiniteCorrespondenceGenerator X.hom Y.hom := by
  let e := productMap q j c hretained g hbase x
  have : IsFinite e := productMap_isFinite q j c hretained hfinite g hbase x
  have : IsFinite (e ≫ pullback.fst X.hom Y.hom) := by
    rw [productMap_fst]
    exact hfinite x
  refine ⟨e.ker, isIntegral_finiteImage e,
    isFinite_image_projection e (pullback.fst X.hom Y.hom), ?_⟩
  change Set.range (e.imageι ≫ pullback.fst X.hom Y.hom) ∈ _
  rw [range_image_projection, productMap_fst]
  exact hdominant x

/-- The signed correspondence is the actual weighted pushforward of the cycle. -/
def correspondence : Cor.mk X ⟶ Cor.mk Y := by
  classical
  exact ∑ x : c.support,
    Finsupp.single (generator q j c hretained hfinite hdominant g hbase x)
      (c x.val * ((productMap q j c hretained g hbase x).residueDegree
        (genericPoint (supportScheme c x)) : ℤ))

open Classical in
/-- Distinct original supports contributing to the same image are summed with
 their original coefficients and actual residue degrees. -/
theorem correspondence_coefficient (W : FiniteCorrespondenceGenerator X.hom Y.hom) :
    (show FiniteCorrespondence X.hom Y.hom from
      correspondence q j c hretained hfinite hdominant g hbase) W =
      ∑ x : c.support,
        if generator q j c hretained hfinite hdominant g hbase x = W then
          c x.val * ((productMap q j c hretained g hbase x).residueDegree
            (genericPoint (supportScheme c x)) : ℤ)
        else 0 := by
  change (∑ x : c.support,
    Finsupp.single (generator q j c hretained hfinite hdominant g hbase x)
      (c x.val * ((productMap q j c hretained g hbase x).residueDegree
        (genericPoint (supportScheme c x)) : ℤ))) W = _
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

end Motivic.FinitePointCycleCorrespondence

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Product

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.Product.Ideals
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Product zero cycles with the original finite-flat multiplicities -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cycles.Divisors.Product
open _root_.Motivic

/-- Product additivity for the exact finite-flat spans, with their original
source and target maps. No finiteness assumption is imposed on the ambient
curve-to-product map. -/
theorem ofFiniteFlatSpan_product {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {D E F C : Scheme.{u}}
    (i : D ⟶ C) (j : E ⟶ C) (l : F ⟶ C)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion l]
    (p : C ⟶ X.left) (g : C ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)
    [IsFinite (i ≫ p)] [IsFinite (j ≫ p)] [IsFinite (l ≫ p)]
    [Flat (i ≫ p)] [Flat (j ≫ p)] [Flat (l ≫ p)]
    (heq : ∀ x : C, p x ∈ genericPoints X.left →
      ∃ a b : C.presheaf.stalk x, b ∈ nonZeroDivisors (C.presheaf.stalk x) ∧
        i.ker.stalk x = Ideal.span {a} ∧ j.ker.stalk x = Ideal.span {b} ∧
        l.ker.stalk x = Ideal.span {a * b}) :
    Cor.ofFiniteFlatSpan (X := X) (Y := Y) (l ≫ p) (l ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun z => l ≫ z) h) =
      Cor.ofFiniteFlatSpan (X := X) (Y := Y) (i ≫ p) (i ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun z => i ≫ z) h) +
      Cor.ofFiniteFlatSpan (X := X) (Y := Y) (j ≫ p) (j ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun z => j ≫ z) h) := by
  let : IsNoetherian D := isNoetherian_of_finiteType (i ≫ p)
  let : IsNoetherian E := isNoetherian_of_finiteType (j ≫ p)
  let : IsNoetherian F := isNoetherian_of_finiteType (l ≫ p)
  have hc := congrArg (fun z => FiniteSupportCycle.residuePushforward
      (pullback.lift p g h) (IntegralCycle.toPoints z))
    (fundamentalCycle_product i j l p heq)
  simp only [map_add, IntegralCycle.toPoints_finitePushforward_apply] at hc
  apply FiniteCorrespondence.toIntegralCycle_injective
  apply IntegralCycle.toPoints_injective
  simp only [map_add, Cor.toIntegralCycle_ofFiniteFlatSpan,
    IntegralCycle.toPoints_finitePushforward_apply]
  have hi : pullback.lift (i ≫ p) (i ≫ g)
      (by simpa only [Category.assoc] using congrArg (fun z => i ≫ z) h) =
      i ≫ pullback.lift p g h := by apply pullback.hom_ext <;> simp
  have hj : pullback.lift (j ≫ p) (j ≫ g)
      (by simpa only [Category.assoc] using congrArg (fun z => j ≫ z) h) =
      j ≫ pullback.lift p g h := by apply pullback.hom_ext <;> simp
  have hl : pullback.lift (l ≫ p) (l ≫ g)
      (by simpa only [Category.assoc] using congrArg (fun z => l ≫ z) h) =
      l ≫ pullback.lift p g h := by apply pullback.hom_ext <;> simp
  simpa only [hi, hj, hl, FiniteSupportCycle.residuePushforward_comp,
    AddMonoidHom.comp_apply] using hc

open Scheme.Modules Scheme.Modules.Invertible

/-- The zero correspondence of the actual tensor product of regular line-bundle
sections is the sum of the two original zero correspondences. All three zero
schemes and their source and target maps are retained, including nilpotents.
There is no caller-supplied local cycle or product-ideal equation. -/
theorem ofFiniteFlatSpan_productSection {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
    (L M : LineBundle C)
    (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono a] [Mono b]
    (p : C ⟶ X.left) (g : C ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)
    [IsFinite (Hom.zeroInclusion a ≫ p)] [Flat (Hom.zeroInclusion a ≫ p)]
    [IsFinite (Hom.zeroInclusion b ≫ p)] [Flat (Hom.zeroInclusion b ≫ p)]
    [IsFinite (Hom.zeroInclusion (Hom.productSection a b) ≫ p)]
    [Flat (Hom.zeroInclusion (Hom.productSection a b) ≫ p)] :
    Cor.ofFiniteFlatSpan (X := X) (Y := Y)
        (Hom.zeroInclusion (Hom.productSection a b) ≫ p)
        (Hom.zeroInclusion (Hom.productSection a b) ≫ g)
        (by simpa only [Category.assoc] using
          congrArg (fun z => Hom.zeroInclusion (Hom.productSection a b) ≫ z) h) =
      Cor.ofFiniteFlatSpan (X := X) (Y := Y)
        (Hom.zeroInclusion a ≫ p) (Hom.zeroInclusion a ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun z => Hom.zeroInclusion a ≫ z) h) +
      Cor.ofFiniteFlatSpan (X := X) (Y := Y)
        (Hom.zeroInclusion b ≫ p) (Hom.zeroInclusion b ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun z => Hom.zeroInclusion b ≫ z) h) :=
  ofFiniteFlatSpan_product (Hom.zeroInclusion a) (Hom.zeroInclusion b)
    (Hom.zeroInclusion (Hom.productSection a b)) p g h
    (fun x _ => Hom.productSection_stalk_equations L M a b x)

end AlgebraicGeometry.Scheme.Cycles.Divisors.Product

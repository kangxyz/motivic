/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProductSectionIdeals
public import Motivic.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient
public import Motivic.AlgebraicGeometry.Cycles.GenericFiniteFiber
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlat
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Product zero cycles with the original finite-flat multiplicities -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ProductZeroCycles

/-- At a point over a generic base point, the actual closed-source coefficient
is the finite ambient quotient length. -/
theorem coefficient_and_finiteness {D C X : Scheme.{u}} [IsNoetherian D]
    (j : D ⟶ C) [IsClosedImmersion j] (p : C ⟶ X)
    [LocallyQuasiFinite (j ≫ p)] (x : C) (hx : p x ∈ genericPoints X) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle D)) x =
      ((Module.length (C.presheaf.stalk x)
        ((C.presheaf.stalk x) ⧸ j.ker.stalk x)).toNat : ℤ) ∧
    Module.length (C.presheaf.stalk x)
      ((C.presheaf.stalk x) ⧸ j.ker.stalk x) ≠ ⊤ := by
  classical
  rw [IntegralCycle.toPoints_finitePushforward_apply, toPoints_fundamentalCycle,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain j (fundamentalPointCycle D) x = _ ∧ _
  by_cases h : x ∈ Set.range j
  · obtain ⟨z, rfl⟩ := h
    have hz : z ∈ genericPoints D := mem_genericPoints_of_image_generic (j ≫ p) z hx
    rw [Finsupp.mapDomain_apply_of_injective j.isEmbedding.injective,
      fundamentalPointCycle_apply, dite_eq_left hz, j.ker_stalk]
    have hl : Module.length (C.presheaf.stalk (j z))
        ((C.presheaf.stalk (j z)) ⧸ RingHom.ker (j.stalkMap z).hom) =
        Module.length (D.presheaf.stalk z) (D.presheaf.stalk z) :=
      (Module.length_eq_of_surjective
        (Ideal.Quotient.mk_surjective (I := RingHom.ker (j.stalkMap z).hom))).trans
          (ringLength_eq_of_ringEquiv (stalkQuotientKerEquiv j z))
    rw [hl]
    exact ⟨rfl, stalk_length_ne_top_of_mem_genericPoints z hz⟩
  · rw [Finsupp.mapDomain_of_notMem_range _ _ h]
    have : Subsingleton ((C.presheaf.stalk x) ⧸ j.ker.stalk x) :=
      Ideal.Quotient.subsingleton_iff.mpr (closedImmersion_ker_stalk_eq_top j h)
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, ne_eq,
      ENat.zero_ne_top, not_false_eq_true, and_self]

/-- Flat source components cannot contribute above nongeneric base points. -/
theorem coefficient_zero {D C X : Scheme.{u}} [IsNoetherian D]
    (j : D ⟶ C) [IsClosedImmersion j] (p : C ⟶ X) [Flat (j ≫ p)]
    (x : C) (hx : p x ∉ genericPoints X) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward j (fundamentalCycle D)) x = 0 := by
  classical
  rw [IntegralCycle.toPoints_finitePushforward_apply, toPoints_fundamentalCycle,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  change Finsupp.mapDomain j (fundamentalPointCycle D) x = 0
  by_cases h : x ∈ Set.range j
  · obtain ⟨z, rfl⟩ := h
    rw [Finsupp.mapDomain_apply_of_injective j.isEmbedding.injective,
      fundamentalPointCycle_apply, dite_eq_right]
    exact fun hz => hx (mem_genericPoints_of_generalizing (j ≫ p)
      (Flat.generalizingMap (j ≫ p)) z hz)
  · exact Finsupp.mapDomain_of_notMem_range _ _ h

/-- Local product equations imply equality of the actual pushed fundamental
cycles. The equations concern original stalk ideals, not their radicals. -/
theorem fundamentalCycle_product {D E F C X : Scheme.{u}}
    [IsNoetherian D] [IsNoetherian E] [IsNoetherian F]
    (i : D ⟶ C) (j : E ⟶ C) (l : F ⟶ C)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion l]
    (p : C ⟶ X)
    [LocallyQuasiFinite (i ≫ p)] [LocallyQuasiFinite (j ≫ p)]
    [LocallyQuasiFinite (l ≫ p)] [Flat (i ≫ p)] [Flat (j ≫ p)] [Flat (l ≫ p)]
    (heq : ∀ x : C, p x ∈ genericPoints X →
      ∃ a b : C.presheaf.stalk x, b ∈ nonZeroDivisors (C.presheaf.stalk x) ∧
        i.ker.stalk x = Ideal.span {a} ∧ j.ker.stalk x = Ideal.span {b} ∧
        l.ker.stalk x = Ideal.span {a * b}) :
    IntegralCycle.finitePushforward l (fundamentalCycle F) =
      IntegralCycle.finitePushforward i (fundamentalCycle D) +
        IntegralCycle.finitePushforward j (fundamentalCycle E) := by
  apply IntegralCycle.toPoints_injective
  ext x
  simp only [map_add, Finsupp.add_apply]
  by_cases hx : p x ∈ genericPoints X
  · obtain ⟨a, b, hb, ha, hj, hl⟩ := heq x hx
    obtain ⟨hi, hif⟩ := coefficient_and_finiteness i p x hx
    obtain ⟨hhj, hjf⟩ := coefficient_and_finiteness j p x hx
    obtain ⟨hhl, -⟩ := coefficient_and_finiteness l p x hx
    rw [hi, hhj, hhl, ha, hj, hl]
    rw [ha] at hif
    rw [hj] at hjf
    change ((Ring.ord (C.presheaf.stalk x) (a * b)).toNat : ℤ) = _
    rw [Ring.ord_mul _ hb]
    simp only [Ring.ord, ENat.toNat_add hif hjf, Nat.cast_add]
  · rw [coefficient_zero l p x hx, coefficient_zero i p x hx,
      coefficient_zero j p x hx, add_zero]

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

end Motivic.ProductZeroCycles

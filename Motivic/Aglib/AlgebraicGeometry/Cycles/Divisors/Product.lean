/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalCycle
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.StalkKernel
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Products of divisors
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cycles.Divisors.Product
open _root_.AlgebraicGeometry.Scheme.Hom

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


end AlgebraicGeometry.Scheme.Cycles.Divisors.Product

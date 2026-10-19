/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.ComponentDecomposition
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Fundamental cycles under arbitrary flat base change

The actual generic stalk length of a flat pullback is the original generic
length times its actual closed-fiber length. Every length is proved finite
before passing to natural or integer multiplicities. The resulting cycle is
the finite sum of the fundamental cycles of the unreduced component exteriors.
No finite-type assumption on the flat test map is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators TensorProduct

universe u v

namespace IsLocalRing

/-- Flat local extension of the regular module retains the full closed fiber. -/
theorem length_self_of_flat {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (g : A →+* B) [IsLocalHom g] (hg : g.Flat) :
    Module.length B B = Module.length A A *
      Module.length B (B ⧸ (maximalIdeal A).map g) := by
  let := g.toAlgebra
  have : Module.Flat A B := hg
  rw [← (TensorProduct.AlgebraTensorModule.rid A B B).length_eq]
  exact length_baseChange A B A

end IsLocalRing

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

namespace Flat

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- All lengths in the generic flat local formula are finite. The closed fiber
is the actual quotient of the new stalk and can have nilpotents. -/
theorem generic_stalk_lengths_ne_top (x : genericPoints X) :
    Module.length (Y.presheaf.stalk (f x.1)) (Y.presheaf.stalk (f x.1)) ≠ ⊤ ∧
      Module.length (X.presheaf.stalk x.1) (X.presheaf.stalk x.1) ≠ ⊤ ∧
      Module.length (X.presheaf.stalk x.1)
        (_root_.ChainComplex.Koszul.coefficientClosedFiber (f.stalkMap x.1).hom) ≠ ⊤ := by
  have hx := _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_generalizing f
      (Flat.generalizingMap f) x.1 x.2
  exact ⟨stalk_length_ne_top_of_mem_genericPoints _ hx,
    stalk_length_ne_top_of_mem_genericPoints _ x.2,
    stalk_module_length_ne_top_of_mem_genericPoints _ x.2 _⟩

/-- Generic multiplicity under an arbitrary flat morphism is the old
multiplicity times the full actual local closed-fiber multiplicity. -/
theorem genericMultiplicity_eq_mul_closedFiber (x : genericPoints X) :
    genericMultiplicity x =
      genericMultiplicity
        ⟨f x.1, _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_generalizing f
            (Flat.generalizingMap f) x.1 x.2⟩ *
      (Module.length (X.presheaf.stalk x.1)
        (_root_.ChainComplex.Koszul.coefficientClosedFiber (f.stalkMap x.1).hom)).toNat := by
  obtain ⟨hsource, htarget, hfiber⟩ := generic_stalk_lengths_ne_top f x
  apply ENat.natCast_inj.mp
  simp only [Nat.cast_mul, genericMultiplicity, ENat.natCast_toNat hsource,
    ENat.natCast_toNat htarget, ENat.natCast_toNat hfiber]
  exact IsLocalRing.length_self_of_flat (f.stalkMap x.1).hom (Flat.stalkMap f x.1)

end Flat

open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

variable {P S T : Scheme.{u}} (p : P ⟶ S) (t : T ⟶ S)
  [Flat t] [IsNoetherian P] [IsNoetherian (pullback p t : Scheme.{u})]

/-- The whole-open coefficient uses the literal flat pullback projection. -/
theorem genericMultiplicity_componentGeneric_mul_closedFiber
    (U : (pullback p t : Scheme.{u}).Opens) [IsNoetherian U.toScheme]
    (w : genericPoints U.toScheme) :
    (genericMultiplicity w : ℤ) =
      (genericMultiplicity (componentGeneric p t U w) : ℤ) *
        closedFiberMultiplicity p t U w := by
  have h := Flat.genericMultiplicity_eq_mul_closedFiber (pullback.fst p t)
    (originalGeneric p t U w)
  have hopen : genericMultiplicity (originalGeneric p t U w) = genericMultiplicity w := by
    exact congrArg ENat.toNat (stalk_length_eq_of_isOpenImmersion U.ι w.1)
  rw [hopen] at h
  simpa only [closedFiberMultiplicity,
      _root_.HomologicalComplex.ModuleLengthEuler.integerLength, componentGeneric,
    originalGeneric, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) h

/-- The whole-open fundamental cycle splits into every actual original
component exterior, retaining its nonreduced local multiplicities. -/
theorem fundamentalCycle_open_eq_component_sum
    (U : (pullback p t : Scheme.{u}).Opens) [IsNoetherian U.toScheme] :
    let := IntegralCycle.genericPointFintype P
    fundamentalCycle U.toScheme =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward (componentInclusion p t U z)
          (fundamentalCycle (componentOpen p t U z)) := by
  classical
  let := IntegralCycle.genericPointFintype P
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity]
  convert ofGenericCoefficients_eq_component_sum p t U
    (fun z => (genericMultiplicity z : ℤ)) using 1
  congr 1
  funext w
  exact genericMultiplicity_componentGeneric_mul_closedFiber p t U w

omit [Flat t] [IsNoetherian P] in
/-- Removing a top-open wrapper preserves the actual component fundamental cycle. -/
theorem finitePushforward_top_component_fundamentalCycle (z : genericPoints P) :
    let : IsNoetherian (⊤ : (pullback p t : Scheme.{u}).Opens).toScheme :=
      isNoetherian_of_finiteType (Scheme.topIso (pullback p t)).hom
    let : IsNoetherian (componentExterior p t z) :=
      isNoetherian_of_finiteType (componentExteriorInclusion p t z)
    IntegralCycle.finitePushforward (Scheme.topIso (pullback p t)).hom
      (IntegralCycle.finitePushforward (componentInclusion p t ⊤ z)
        (fundamentalCycle (componentOpen p t ⊤ z))) =
      IntegralCycle.finitePushforward (componentExteriorInclusion p t z)
        (fundamentalCycle (componentExterior p t z)) := by
  let : IsNoetherian (⊤ : (pullback p t : Scheme.{u}).Opens).toScheme :=
    isNoetherian_of_finiteType (Scheme.topIso (pullback p t)).hom
  let : IsNoetherian (componentExterior p t z) :=
    isNoetherian_of_finiteType (componentExteriorInclusion p t z)
  dsimp only
  let b := componentExteriorInclusion p t z
  have : IsIso (b ⁻¹ᵁ (⊤ : (pullback p t : Scheme.{u}).Opens)).ι := by
    rw [Scheme.Hom.preimage_top]
    exact (Scheme.topIso _).isIso_hom
  have hmap : componentInclusion p t ⊤ z ≫ (Scheme.topIso (pullback p t)).hom =
      (b ⁻¹ᵁ (⊤ : (pullback p t : Scheme.{u}).Opens)).ι ≫ b :=
    componentInclusion_ambient p t ⊤ z
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  have hcongr {D E : Scheme.{u}} (f g : D ⟶ E) (hf : IsFinite f) (hg : IsFinite g)
      (h : f = g) (c : IntegralCycle D) :
      @IntegralCycle.finitePushforward D E f hf c =
        @IntegralCycle.finitePushforward D E g hg c := by
    cases h
    rfl
  refine (hcongr _ _ inferInstance inferInstance hmap _).trans ?_
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]

/-- Flat pullback of a fundamental cycle is the sum of the full fundamental
cycles of the original reduced component supports' actual pullbacks. These
pullbacks are not reduced, and the test morphism need not be of finite type. -/
theorem fundamentalCycle_pullback_eq_component_sum :
    let := IntegralCycle.genericPointFintype P
    let : ∀ z : genericPoints P, IsNoetherian (componentExterior p t z) :=
      fun z => isNoetherian_of_finiteType (componentExteriorInclusion p t z)
    fundamentalCycle (pullback p t) =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward (componentExteriorInclusion p t z)
          (fundamentalCycle (componentExterior p t z)) := by
  classical
  let := IntegralCycle.genericPointFintype P
  let : ∀ z : genericPoints P, IsNoetherian (componentExterior p t z) :=
    fun z => isNoetherian_of_finiteType (componentExteriorInclusion p t z)
  let : IsNoetherian (⊤ : (pullback p t : Scheme.{u}).Opens).toScheme :=
    isNoetherian_of_finiteType (Scheme.topIso (pullback p t)).hom
  rw [← finitePushforward_fundamentalCycle (Scheme.topIso (pullback p t)).hom,
    fundamentalCycle_open_eq_component_sum p t ⊤, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, finitePushforward_top_component_fundamentalCycle p t z]

end AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

variable {P S T : Scheme.{u}} (p : P ⟶ S) (t : T ⟶ S)

/-- The unreduced pullback of an original component of the second factor. -/
abbrev componentExteriorSnd (z : genericPoints T) : Scheme.{u} :=
  pullback p ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ t)

/-- The actual second-factor component inclusion, expressed through the
canonical product swaps and the existing Cartesian component inclusion. -/
def componentExteriorSndInclusion (z : genericPoints T) :
    componentExteriorSnd p t z ⟶ pullback p t :=
  (pullbackSymmetry p ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ t)).hom ≫
    componentExteriorInclusion t p z ≫ (pullbackSymmetry t p).hom

instance componentExteriorSndInclusion_isClosedImmersion (z : genericPoints T) :
    IsClosedImmersion (componentExteriorSndInclusion p t z) := by
  unfold componentExteriorSndInclusion
  infer_instance

/-- The swapped construction is exactly the canonical Cartesian product map. -/
theorem componentExteriorSndInclusion_eq_map (z : genericPoints T) :
    componentExteriorSndInclusion p t z =
      pullback.map _ _ _ _ (𝟙 P) (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
        (𝟙 S) (by simp) (by simp) := by
  apply pullback.hom_ext <;>
    simp [componentExteriorSndInclusion, componentExteriorInclusion,
      IntegralClosedSubscheme.exteriorInclusion, pullback.map, Category.assoc]

/-- The same flat fundamental-cycle decomposition using the second projection. -/
theorem fundamentalCycle_pullback_eq_second_component_sum
    [Flat p] [IsNoetherian T] [IsNoetherian (pullback p t : Scheme.{u})] :
    letI := IntegralCycle.genericPointFintype T
    letI : ∀ z : genericPoints T, IsNoetherian (componentExteriorSnd p t z) :=
      fun z => isNoetherian_of_finiteType (componentExteriorSndInclusion p t z)
    fundamentalCycle (pullback p t) =
      ∑ z : genericPoints T, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward (componentExteriorSndInclusion p t z)
          (fundamentalCycle (componentExteriorSnd p t z)) := by
  classical
  let := IntegralCycle.genericPointFintype T
  let : IsNoetherian (pullback t p : Scheme.{u}) :=
    isNoetherian_of_finiteType (pullbackSymmetry t p).hom
  let : ∀ z : genericPoints T, IsNoetherian (componentExterior t p z) :=
    fun z => isNoetherian_of_finiteType (componentExteriorInclusion t p z)
  let : ∀ z : genericPoints T, IsNoetherian (componentExteriorSnd p t z) :=
    fun z => isNoetherian_of_finiteType (componentExteriorSndInclusion p t z)
  rw [← finitePushforward_fundamentalCycle (pullbackSymmetry t p).hom,
    fundamentalCycle_pullback_eq_component_sum t p, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul]
  congr 1
  simp only [componentExteriorSndInclusion, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, finitePushforward_fundamentalCycle]

/-- Product of the original reduced component supports. The product itself is
left unreduced, including all inseparable or nonreduced branches. -/
abbrev componentPairExterior (a : genericPoints P) (b : genericPoints T) : Scheme.{u} :=
  pullback ((IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫ p)
    ((IntegralClosedSubscheme.pointClosure b.1).val.subschemeι ≫ t)

/-- The literal inclusion of a component pair into the whole product. -/
def componentPairExteriorInclusion (a : genericPoints P) (b : genericPoints T) :
    componentPairExterior p t a b ⟶ pullback p t :=
  componentExteriorSndInclusion
      ((IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫ p) t b ≫
    componentExteriorInclusion p t a

instance componentPairExteriorInclusion_isClosedImmersion
    (a : genericPoints P) (b : genericPoints T) :
    IsClosedImmersion (componentPairExteriorInclusion p t a b) := by
  unfold componentPairExteriorInclusion
  infer_instance

/-- Both coordinates are the original reduced-support immersions. -/
theorem componentPairExteriorInclusion_eq_map (a : genericPoints P) (b : genericPoints T) :
    componentPairExteriorInclusion p t a b =
      pullback.map _ _ _ _ (IntegralClosedSubscheme.pointClosure a.1).val.subschemeι
        (IntegralClosedSubscheme.pointClosure b.1).val.subschemeι (𝟙 S)
        (by simp) (by simp) := by
  apply pullback.hom_ext <;>
    simp [componentPairExteriorInclusion, componentExteriorSndInclusion_eq_map,
      componentExteriorInclusion, IntegralClosedSubscheme.exteriorInclusion,
      pullback.map, Category.assoc]

variable {K : Type u} [Field K] {P T : Scheme.{u}}
  (p : P ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))
  [IsNoetherian P] [IsNoetherian T] [IsNoetherian (pullback p t : Scheme.{u})]

/-- Over any field, the whole product fundamental cycle is the finite double
sum weighted by the two ORIGINAL generic lengths. Only the original component
supports are reduced; their actual product fundamental cycles retain every
local multiplicity. No geometric integrality or separability is assumed. -/
theorem fundamentalCycle_product_eq_component_pair_sum :
    letI := IntegralCycle.genericPointFintype P
    letI := IntegralCycle.genericPointFintype T
    letI : ∀ a : genericPoints P, ∀ b : genericPoints T,
        IsNoetherian (componentPairExterior p t a b) :=
      fun a b => isNoetherian_of_finiteType (componentPairExteriorInclusion p t a b)
    fundamentalCycle (pullback p t) =
      ∑ a : genericPoints P, ∑ b : genericPoints T,
        ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) •
          IntegralCycle.finitePushforward (componentPairExteriorInclusion p t a b)
            (fundamentalCycle (componentPairExterior p t a b)) := by
  classical
  let := IntegralCycle.genericPointFintype P
  let := IntegralCycle.genericPointFintype T
  let : Subsingleton (Spec (.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let : ∀ a : genericPoints P, IsNoetherian (componentExterior p t a) :=
    fun a => isNoetherian_of_finiteType (componentExteriorInclusion p t a)
  let : ∀ a : genericPoints P, ∀ b : genericPoints T,
      IsNoetherian (componentPairExterior p t a b) :=
    fun a b => isNoetherian_of_finiteType (componentPairExteriorInclusion p t a b)
  rw [fundamentalCycle_pullback_eq_component_sum p t]
  apply Finset.sum_congr rfl
  intro a _
  rw [fundamentalCycle_pullback_eq_second_component_sum
    ((IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫ p) t, map_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_zsmul, smul_smul]
  simp only [componentPairExteriorInclusion, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply]


end AlgebraicGeometry

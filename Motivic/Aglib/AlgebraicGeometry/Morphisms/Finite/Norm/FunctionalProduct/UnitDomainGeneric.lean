/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.UnitDomain
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio
/-! # The original good open contains the generic point

Regular original functionals are units on the entire finite generic fiber.
The source may be disconnected or nonreduced; no source function field is used.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.UnitDomainGeneric`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.NormalizedUnit`, `Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- Every point over the actual generic-point morphism lies in the original
functional's unit locus, by invertibility on the whole generic finite algebra. -/
theorem preimage_genericPoint_range_subset_zeroSupportUnitOpen
    {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
    (L : LineBundle C) (φ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] :
    f ⁻¹' Set.range (T.fromSpecStalk (genericPoint T)) ⊆
      (zeroSupportUnitOpen L φ : Set C) := by
  let p := pullback.fst f (T.fromSpecStalk (genericPoint T))
  have hi : IsIso ((Modules.pullback p).map φ ≫ (pullbackUnitIso p).hom) :=
    genericFiberLineMap_isIso f L φ
  let := IsIso.of_isIso_comp_right ((Modules.pullback p).map φ) (pullbackUnitIso p).hom
  rw [← Scheme.Pullback.range_fst]
  exact range_subset_zeroSupportUnitOpen_of_pullback_isIso L φ p

/-- The exact norm-product domain is nonempty for the same regular functionals
already used to define its canonical generic ratio. -/
theorem genericPoint_mem_functionalNormProductUnitDomain
    {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
    (N M : LineBundle C)
    (n : N.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono n]
    (d : M.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono d]
    (L K : LineBundle T)
    (a : L.val ⟶ SheafOfModules.unit T.ringCatSheaf) [Mono a]
    (c : K.val ⟶ SheafOfModules.unit T.ringCatSheaf) [Mono c] :
    genericPoint T ∈ functionalNormProductUnitDomain f N M n d L K a c := by
  have hη : genericPoint T ∈ Set.range (T.fromSpecStalk (genericPoint T)) :=
    ⟨IsLocalRing.closedPoint T.functionField, T.fromSpecStalk_closedPoint⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact preimage_genericPoint_range_subset_zeroSupportUnitOpen (𝟙 T) L a hη
  · exact preimage_genericPoint_range_subset_zeroSupportUnitOpen (𝟙 T) K c hη
  · exact f.subset_finiteDescentOpen
      (zeroSupportUnitOpen N n ⊓ zeroSupportUnitOpen M d)
      (Set.range (T.fromSpecStalk (genericPoint T)))
      (fun _ hx => ⟨preimage_genericPoint_range_subset_zeroSupportUnitOpen f N n hx,
        preimage_genericPoint_range_subset_zeroSupportUnitOpen f M d hx⟩) hη

/-- Nonemptiness is a consequence of the original regularity assumptions, not
an additional assumption about the constructed open or its boundary. -/
theorem functionalNormProductUnitDomain_nonempty
    {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
    (N M : LineBundle C)
    (n : N.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono n]
    (d : M.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono d]
    (L K : LineBundle T)
    (a : L.val ⟶ SheafOfModules.unit T.ringCatSheaf) [Mono a]
    (c : K.val ⟶ SheafOfModules.unit T.ringCatSheaf) [Mono c] :
    Nonempty (functionalNormProductUnitDomain f N M n d L K a c) :=
  ⟨⟨genericPoint T, genericPoint_mem_functionalNormProductUnitDomain f N M n d L K a c⟩⟩

end AlgebraicGeometry.Scheme

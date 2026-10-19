/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Open.FiniteMarkedOpenDescent
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpenPullback
/-! # The unchanged domain of a functional norm product

The domain is the target pair's unit locus intersected with finite descent of
both source unit loci. It need not be affine. Every chart in it retains the
whole finite inverse image. No section, boundary frame or coefficient base is
changed after forming this open.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.UnitDomain`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`FunctionalProduct.Unit`, `FunctionalProduct.UnitDomainGeneric`,
`Correction.FunctionalUnitBoundary`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

variable {C T : Scheme.{u}} (f : C ⟶ T) [IsFinite f]
  (N M : LineBundle C) (n : N.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (d : M.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (L K : LineBundle T) (a : L.val ⟶ SheafOfModules.unit T.ringCatSheaf)
  (c : K.val ⟶ SheafOfModules.unit T.ringCatSheaf)

/-- The actual good open for the original target quotient times the source norm. -/
def functionalNormProductUnitDomain : T.Opens :=
  (zeroSupportUnitOpen L a ⊓ zeroSupportUnitOpen K c) ⊓
    f.finiteDescentOpen (zeroSupportUnitOpen N n ⊓ zeroSupportUnitOpen M d)

/-- Every point above the good open lies in both original source unit loci. -/
theorem preimage_functionalNormProductUnitDomain_le :
    f ⁻¹ᵁ functionalNormProductUnitDomain f N M n d L K a c ≤
      zeroSupportUnitOpen N n ⊓ zeroSupportUnitOpen M d := by
  intro x hx
  exact f.preimage_finiteDescentOpen_le _ hx.2

/-- Full inverse-boundary containment, not a selected lift, retains the boundary. -/
theorem range_subset_functionalNormProductUnitDomain
    {E : Scheme.{u}} (b : E ⟶ T)
    [IsIso ((Modules.pullback b).map a)] [IsIso ((Modules.pullback b).map c)]
    (hn : f ⁻¹' Set.range b ⊆ (zeroSupportUnitOpen N n : Set C))
    (hd : f ⁻¹' Set.range b ⊆ (zeroSupportUnitOpen M d : Set C)) :
    Set.range b ⊆ (functionalNormProductUnitDomain f N M n d L K a c : Set T) := by
  intro x hx
  refine ⟨⟨range_subset_zeroSupportUnitOpen_of_pullback_isIso L a b hx,
    range_subset_zeroSupportUnitOpen_of_pullback_isIso K c b hx⟩, ?_⟩
  exact f.subset_finiteDescentOpen
    (zeroSupportUnitOpen N n ⊓ zeroSupportUnitOpen M d) (Set.range b)
    (fun _ h => ⟨hn h, hd h⟩) hx

/-- The original, possibly nonreduced boundary factors through this exact open. -/
def functionalNormProductBoundaryFactor
    {E : Scheme.{u}} (b : E ⟶ T)
    [IsIso ((Modules.pullback b).map a)] [IsIso ((Modules.pullback b).map c)]
    (hn : f ⁻¹' Set.range b ⊆ (zeroSupportUnitOpen N n : Set C))
    (hd : f ⁻¹' Set.range b ⊆ (zeroSupportUnitOpen M d : Set C)) :
    E ⟶ (functionalNormProductUnitDomain f N M n d L K a c).toScheme :=
  IsOpenImmersion.lift (functionalNormProductUnitDomain f N M n d L K a c).ι b (by
    simpa only [Opens.range_ι] using
      range_subset_functionalNormProductUnitDomain f N M n d L K a c b hn hd)

/-- Factoring through the open does not replace the boundary morphism. -/
theorem functionalNormProductBoundaryFactor_fac
    {E : Scheme.{u}} (b : E ⟶ T)
    [IsIso ((Modules.pullback b).map a)] [IsIso ((Modules.pullback b).map c)]
    (hn : f ⁻¹' Set.range b ⊆ (zeroSupportUnitOpen N n : Set C))
    (hd : f ⁻¹' Set.range b ⊆ (zeroSupportUnitOpen M d : Set C)) :
    functionalNormProductBoundaryFactor f N M n d L K a c b hn hd ≫
      (functionalNormProductUnitDomain f N M n d L K a c).ι = b :=
  by
    unfold functionalNormProductBoundaryFactor
    exact IsOpenImmersion.lift_fac _ _ _

/-- On every map into this open, both original target functionals are units. -/
theorem functionalNormProductUnitDomain_target_isIso
    {W : Scheme.{u}} (w : W ⟶ T)
    (hw : Set.range w ⊆ (functionalNormProductUnitDomain f N M n d L K a c : Set T)) :
    IsIso (pullbackUnitMap w a) ∧ IsIso (pullbackUnitMap w c) := by
  constructor
  · exact isIso_pullbackUnitMap_of_range_subset_unitOpen L a w (fun _ h => (hw h).1.1)
  · exact isIso_pullbackUnitMap_of_range_subset_unitOpen K c w (fun _ h => (hw h).1.2)

/-- The complete inverse image of every target chart has both source units. -/
theorem functionalNormProductUnitDomain_source_isIso
    {W : Scheme.{u}} (w : W ⟶ T)
    (hw : Set.range w ⊆ (functionalNormProductUnitDomain f N M n d L K a c : Set T)) :
    IsIso (pullbackUnitMap (pullback.fst f w) n) ∧
      IsIso (pullbackUnitMap (pullback.fst f w) d) := by
  have hsource : Set.range (pullback.fst f w) ⊆
      (zeroSupportUnitOpen N n ⊓ zeroSupportUnitOpen M d : C.Opens) := by
    rintro x ⟨y, rfl⟩
    apply preimage_functionalNormProductUnitDomain_le f N M n d L K a c
    change f ((pullback.fst f w) y) ∈
      (functionalNormProductUnitDomain f N M n d L K a c : T.Opens)
    have he := congrArg (fun g => g y) (pullback.condition (f := f) (g := w))
    change f ((pullback.fst f w) y) = w ((pullback.snd f w) y) at he
    rw [he]
    exact hw ⟨(pullback.snd f w) y, rfl⟩
  exact ⟨isIso_pullbackUnitMap_of_range_subset_unitOpen N n _ (fun _ h => (hsource h).1),
    isIso_pullbackUnitMap_of_range_subset_unitOpen M d _ (fun _ h => (hsource h).2)⟩

end AlgebraicGeometry.Scheme

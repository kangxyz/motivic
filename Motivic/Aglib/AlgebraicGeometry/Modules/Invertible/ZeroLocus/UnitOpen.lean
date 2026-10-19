/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts
public import Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange

/-! # The unit open of the original line-bundle functional

The complement of the whole zero support is an actual open on which the same
functional is invertible. Every morphism on which its pullback is invertible
lands in this open, without assumptions on reducedness or on the boundary.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpen`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteUnitNeighborhood`,
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpenPullback`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} (L : LineBundle X)
    (φ : (show X.Modules from L.val) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- The actual complement of the original functional's whole zero support. -/
def zeroSupportUnitOpen : X.Opens := (Hom.imageIdealData φ).support.compl

/-- A unit chart coefficient makes the original restricted map an isomorphism. -/
theorem isIso_restrict_of_chart_coefficient_isUnit (W : X.Opens)
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (B : X.Opens) (hBW : B ≤ W)
    (hu : IsUnit (X.presheaf.map (homOfLE hBW).op
      (φ.app W (chartGenerator X L.val W e)))) :
    IsIso ((Modules.restrictFunctor B.ι).map φ) := by
  let ψ := (Modules.restrictFunctor B.ι).map φ
  have happ (V : B.toScheme.Opens) : Function.Bijective (ψ.app V) := by
    let U := B.ι ''ᵁ V
    have hUB : U ≤ B := B.ι_image_le V
    have huU : IsUnit (X.presheaf.map (homOfLE (hUB.trans hBW)).op
        (φ.app W (chartGenerator X L.val W e))) := by
      have h := hu.map (X.presheaf.map (homOfLE hUB).op).hom
      rw [← Functor.map_comp_apply] at h
      convert h using 1
    change Function.Bijective (φ.app U)
    have hbij := (IsUnit.isUnit_iff_mulRight_bijective.mp huU).comp
      (chartSectionEquiv X L.val W e U (hUB.trans hBW)).bijective
    constructor
    · intro m n hmn
      apply hbij.injective
      exact (lineBundleMap_chart_general L φ W e U (hUB.trans hBW) m).symm.trans
        (hmn.trans (lineBundleMap_chart_general L φ W e U (hUB.trans hBW) n))
    · intro r
      obtain ⟨m, hm⟩ := hbij.surjective r
      exact ⟨m, (lineBundleMap_chart_general L φ W e U (hUB.trans hBW) m).trans hm⟩
  have : ∀ V, IsIso (((Modules.toPresheaf B.toScheme).map ψ).app V) := by
    intro V
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (happ V.unop)
  have : IsIso ((Modules.toPresheaf B.toScheme).map ψ) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso ψ (Modules.toPresheaf B.toScheme)

/-- Outside the whole zero support, the same functional is invertible on a
basic-open neighborhood, with no reducedness assumption. -/
theorem exists_isIso_restrict_of_not_mem_zero_support (x : X)
    (hx : x ∉ (Hom.imageIdealData φ).support) :
    ∃ B : X.Opens, x ∈ B ∧ IsIso ((Modules.restrictFunctor B.ι).map φ) := by
  let := lineBundle_isLocallyFree X L
  obtain ⟨W, hxW, ⟨e⟩⟩ :=
    (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let c : Γ(X, U) :=
    X.presheaf.map (homOfLE hUW).op (φ.app W (chartGenerator X L.val W e))
  have hxc : x ∈ X.basicOpen c := by
    by_contra hnot
    apply hx
    apply (Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := Hom.imageIdealData φ) (U := ⟨U, hU⟩) hxU).mpr
    rw [Hom.imageIdealData_eq φ (Hom.imageIdealLocalizes_of_isQuasicoherent φ),
      sectionImageIdeal_eq_span_chart L φ W e U hUW,
      Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    exact hnot
  refine ⟨X.basicOpen c, hxc, ?_⟩
  apply isIso_restrict_of_chart_coefficient_isUnit L φ W e (X.basicOpen c)
    ((X.basicOpen_le c).trans hUW)
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le c)).op c) :=
    X.toRingedSpace.isUnit_res_basicOpen c
  dsimp [c] at hu
  rw [← Functor.map_comp_apply] at hu
  convert hu using 1

/-- The original functional is invertible on its actual zero-support complement. -/
theorem isIso_restrict_zeroSupportUnitOpen :
    IsIso ((Modules.restrictFunctor (zeroSupportUnitOpen L φ).ι).map φ) := by
  apply moduleSheaf_isIso_restrict_of_stalks
  intro x
  obtain ⟨B, hxB, hB⟩ := exists_isIso_restrict_of_not_mem_zero_support L φ x.1 x.2
  let y : B.toScheme := ⟨x.1, hxB⟩
  have : IsIso ((Modules.stalkFunctor B.toScheme y).map
      ((Modules.restrictFunctor B.ι).map φ)) := inferInstance
  exact (NatIso.isIso_map_iff (Modules.restrictStalkNatIso B.ι y) φ).mp this

/-- The same statement for the native geometric pullback, not a chosen replacement map. -/
theorem isIso_pullback_zeroSupportUnitOpen :
    IsIso ((Modules.pullback (zeroSupportUnitOpen L φ).ι).map φ) := by
  have := isIso_restrict_zeroSupportUnitOpen L φ
  exact (NatIso.isIso_map_iff
    (Modules.restrictFunctorIsoPullback (zeroSupportUnitOpen L φ).ι) φ).mp this

/-- Any supplied boundary on which the actual pulled functional is invertible
lies in this same unit open. No closedness assumption on the boundary is used. -/
theorem range_subset_zeroSupportUnitOpen_of_pullback_isIso {Y : Scheme.{u}}
    (b : Y ⟶ X) [IsIso ((Modules.pullback b).map φ)] :
    Set.range b ⊆ (zeroSupportUnitOpen L φ : Set X) := by
  let := lineBundle_isLocallyFree X L
  have : IsIso (Hom.pullbackToUnit φ b) := by
    unfold Hom.pullbackToUnit
    infer_instance
  have := Hom.isEmpty_pullback_zeroInclusion φ b
  rintro x ⟨y, rfl⟩ hx
  have hz : b y ∈ Set.range (Hom.zeroInclusion φ) := by
    change b y ∈ Set.range (Hom.imageIdealData φ).subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨z, hz⟩ := hz
  have hp : z ∈ Set.range (Limits.pullback.snd b (Hom.zeroInclusion φ)) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨y, hz.symm⟩
  obtain ⟨w, _⟩ := hp
  exact isEmptyElim w

end AlgebraicGeometry.Scheme.Modules.Invertible

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.HomogeneousSectionUnitOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Evaluation
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts

/-! # Whole boundary containment in the actual twist-section unit open

A unit restriction implies containment, rather than assuming a support condition.
The proof uses the original dual section's zero scheme and actual chart image ideals.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.TwistSectionBoundaryUnitOpen`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.PeriodicBoundaryAffineNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ)

private theorem framedSectionDual_imageIdeal
    (X : Scheme.{u}) (L : LineBundle X) (U : X.Opens)
    (e : L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(L.val, ⊤)) :
    Hom.sectionImageIdeal (sectionDualFunctional X L
      ((unitHomGlobalSectionsEquiv X L.val).symm s)) U =
      Ideal.span {chartSectionEquiv X L.val U e U le_rfl
        (L.val.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s)} := by
  let t : Γ(L.val, U) := L.val.val.map (homOfLE le_top).op s
  let c := chartSectionEquiv X L.val U e U le_rfl t
  let g := chartGenerator X L.val U e
  have ht : c • g = t := by
    apply (chartSectionEquiv X L.val U e U le_rfl).injective
    change (chartSectionEquiv X L.val U e U le_rfl)
      (c • (chartSectionEquiv X L.val U e U le_rfl).symm 1) = c
    rw [(chartSectionEquiv X L.val U e U le_rfl).map_smul,
      LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have happ (d : (dualLineBundle X L).val.val.obj (op U)) :
      (sectionDualFunctional X L ((unitHomGlobalSectionsEquiv X L.val).symm s)).val.app
        (op U) d = d.val.app (op (Over.mk (𝟙 U))) t := by
    rw [sectionDualFunctional_apply]
    change d.val.app (op (Over.mk (𝟙 U)))
      (Hom.app ((unitHomGlobalSectionsEquiv X L.val).symm s) U (1 : Γ(X, U))) = _
    rw [unitHomGlobalSectionsEquiv_symm_app, one_smul]
    rfl
  apply le_antisymm
  · rintro x ⟨d, rfl⟩
    change (sectionDualFunctional X L ((unitHomGlobalSectionsEquiv X L.val).symm s)).val.app
      (op U) d ∈ Ideal.span {c}
    rw [happ, ← ht]
    change (show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) (c • g)) ∈
      (Ideal.span {c} : Ideal Γ(X, U))
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨(show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) g), ?_⟩
    have hd := d.property (op (Over.mk (𝟙 U))) c g
    change (show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) (c • g)) =
      c * (show Γ(X, U) from d.val.app (op (Over.mk (𝟙 U))) g) at hd
    exact (mul_comm _ _).trans hd.symm
  · apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    let d : (dualLineBundle X L).val.val.obj (op U) :=
      (InternalHom.sectionHomEquiv X L.val (SheafOfModules.unit X.ringCatSheaf) U).symm e.hom
    refine ⟨d, ?_⟩
    change (sectionDualFunctional X L ((unitHomGlobalSectionsEquiv X L.val).symm s)).val.app
      (op U) d = c
    rw [happ]
    rfl

/-- The dual functional of the original section has its literal coefficient ideal. -/
theorem twistSectionDual_imageIdeal
    (s : Γ(twistingSheaf R ι (n : ℤ), ⊤)) (i : ι) :
    Hom.sectionImageIdeal
      (sectionDualFunctional _ (twistingLineBundle R ι (n : ℤ))
        ((unitHomGlobalSectionsEquiv _ _).symm s)) (coordinateOpen R ι i) =
      Ideal.span {twistingSectionsEquiv R ι (n : ℤ) i le_rfl
        ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op s)} := by
  exact framedSectionDual_imageIdeal (ProjectiveSpace R ι)
    (twistingLineBundle R ι (n : ℤ)) (coordinateOpen R ι i)
    (twistingLocalIso R ι (n : ℤ) i) s

/-- A boundary on which the actual section is a unit lies in its actual unit open.
No reducedness or closedness assumption on the boundary is needed here. -/
theorem range_subset_twistSectionUnitOpen_of_pullback_isIso {Z : Scheme.{u}}
    (z : Z ⟶ ProjectiveSpace R ι)
    (s : Γ(twistingSheaf R ι (n : ℤ), ⊤))
    [IsIso (pullbackSectionMap z ((unitHomGlobalSectionsEquiv _
      (twistingLineBundle R ι (n : ℤ)).val).symm s))] :
    Set.range z ⊆ twistSectionUnitOpen R ι n s := by
  let X := ProjectiveSpace R ι
  let L := twistingLineBundle R ι (n : ℤ)
  let σ := (unitHomGlobalSectionsEquiv X L.val).symm s
  let φ := sectionDualFunctional X L σ
  let := lineBundle_isLocallyFree X (dualLineBundle X L)
  have : IsIso (pullbackSectionMap z σ) := by
    dsimp [σ, L, X]
    infer_instance
  have := sectionDualFunctional_boundary_isEmpty z L σ
  rintro x ⟨y, rfl⟩
  by_contra hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show z y ∈ ⨆ i, coordinateOpen R ι i by rw [iSup_coordinateOpen_eq_top]; trivial)
  have hnot : z y ∉ X.basicOpen (twistingSectionsEquiv R ι (n : ℤ) i le_rfl
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op s)) :=
    fun hm => hx (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hm⟩)
  have hz : z y ∈ Set.range (Hom.zeroInclusion φ) := by
    change z y ∈ Set.range (Hom.imageIdealData φ).subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι]
    apply (Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := Hom.imageIdealData φ)
      (U := ⟨coordinateOpen R ι i, isAffineOpen_coordinateOpen R ι i⟩) hi).mpr
    rw [Hom.imageIdealData_eq φ (Hom.imageIdealLocalizes_of_isQuasicoherent φ),
      twistSectionDual_imageIdeal R ι n s i, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    exact hnot
  obtain ⟨w, hw⟩ := hz
  have hw' : w ∈ Set.range (CategoryTheory.Limits.pullback.snd z (Hom.zeroInclusion φ)) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨y, hw.symm⟩
  obtain ⟨v, _⟩ := hw'
  exact isEmptyElim v

end AlgebraicGeometry.ProjectiveSpace

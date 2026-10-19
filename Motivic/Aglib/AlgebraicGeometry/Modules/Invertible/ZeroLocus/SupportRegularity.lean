/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts

/-! # Regularity from a neighborhood of the whole zero support

A functional on a line bundle is injective away from its own zero support:
its original coefficient is a unit on its basic open. Consequently monicity
on an open neighborhood of the whole zero support implies global monicity.
No integrality, reducedness, or flatness of the zero scheme is assumed.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.SupportRegularity`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.SerreDivisorRegularity`.
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

/-- Outside the whole zero support, the original chart coefficient is a unit
on an actual basic-open neighborhood, and the original map is injective there. -/
theorem exists_app_injective_of_not_mem_zero_support (x : X)
    (hx : x ∉ (Hom.imageIdealData φ).support) (V : X.Opens) (hxV : x ∈ V) :
    ∃ B : X.Opens, x ∈ B ∧ B ≤ V ∧ Function.Injective (φ.app B) := by
  let := lineBundle_isLocallyFree X L
  obtain ⟨W, hxW, ⟨e⟩⟩ :=
    (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  obtain ⟨U, hU, hxU, hUle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ W ⊓ V from ⟨hxW, hxV⟩)
  let hUW : U ≤ W := hUle.trans inf_le_left
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
  refine ⟨X.basicOpen c, hxc, (X.basicOpen_le c).trans (hUle.trans inf_le_right), ?_⟩
  apply (app_injective_iff_chart_regular L φ W e (X.basicOpen c)
    ((X.basicOpen_le c).trans hUW)).mpr
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le c)).op c) :=
    X.toRingedSpace.isUnit_res_basicOpen c
  have he : X.presheaf.map (homOfLE ((X.basicOpen_le c).trans hUW)).op
      (φ.app W (chartGenerator X L.val W e)) =
      X.presheaf.map (homOfLE (X.basicOpen_le c)).op c := by
    dsimp [c]
    rw [← Functor.map_comp_apply]
    rfl
  rw [he]
  exact hu.isSMulRegular Γ(X, X.basicOpen c)

/-- If an open immersion contains the whole zero support and the pullback of
the original line-bundle functional is mono there, that same functional is mono
globally. The hypothesis is not replaced by regularity of another section. -/
theorem mono_of_zero_support_subset_range {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j]
    (hsupport : ((Hom.imageIdealData φ).support : Set X) ⊆ Set.range j)
    [Mono ((Scheme.Modules.pullback j).map φ)] : Mono φ := by
  have : Mono ((Scheme.Modules.restrictFunctor j).map φ) :=
    mono_of_mono_fac ((Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality φ)
  apply moduleHom_mono_of_app_injective
  intro V s t hst
  have hc : Presheaf.equalizerSieve (F := L.val.val.presheaf) s t ∈
      (Opens.grothendieckTopology X) V := by
    intro x hxV
    have hn (B : X.Opens) (hBV : B ≤ V) :
        φ.app B (L.val.val.map (homOfLE hBV).op s) =
          φ.app B (L.val.val.map (homOfLE hBV).op t) :=
      (PresheafOfModules.naturality_apply φ.val (homOfLE hBV).op s).trans
        ((congrArg (X.presheaf.map (homOfLE hBV).op) hst).trans
          (PresheafOfModules.naturality_apply φ.val (homOfLE hBV).op t).symm)
    by_cases hx : x ∈ (Hom.imageIdealData φ).support
    · obtain ⟨y, rfl⟩ := hsupport hx
      let B := j ''ᵁ (j ⁻¹ᵁ V)
      have hBV : B ≤ V := j.image_preimage_le V
      refine ⟨B, homOfLE hBV, ?_, ?_⟩
      · apply moduleHom_app_injective ((Scheme.Modules.restrictFunctor j).map φ)
          (j ⁻¹ᵁ V)
        exact hn B hBV
      · exact ⟨y, hxV, rfl⟩
    · obtain ⟨B, hxB, hBV, hinj⟩ :=
        exists_app_injective_of_not_mem_zero_support L φ x hx V hxV
      exact ⟨B, homOfLE hBV, hinj (hn B hBV), hxB⟩
  apply L.val.isSheaf.isSeparated V _ hc
  intro W k hk
  exact hk

end AlgebraicGeometry.Scheme.Modules.Invertible

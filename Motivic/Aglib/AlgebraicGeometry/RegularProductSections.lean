/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProductSectionIdeals
public import Mathlib.RingTheory.Flat.Basic

/-! # Products of actual regular line-bundle sections are regular -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
open scoped TensorProduct

universe u
namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- On an affine chart with flat second factor, the original tensor-to-unit map is injective. -/
theorem tensorToUnit_app_injective {X : Scheme.{u}} {L M : X.Modules}
    [L.IsQuasicoherent] [M.IsQuasicoherent]
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono a]
    (U : X.Opens) (hU : IsAffineOpen U) [Module.Flat Γ(X, U) Γ(M, U)] :
    Function.Injective (((tensorToUnit a).app M).app U) := by
  let f : Γ(L, U) →ₗ[Γ(X, U)] Γ(X, U) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map a).hom
  have hf : Function.Injective f := moduleHom_app_injective a U
  have ht := Module.Flat.rTensor_preserves_injective_linearMap (M := Γ(M, U)) f hf
  have he (v : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) :
      ((tensorToUnit a).app M).app U (moduleTensorSectionLinear X L M U v) =
        (TensorProduct.lid Γ(X, U) Γ(M, U)) (f.rTensor Γ(M, U) v) := by
    induction v using TensorProduct.inductionOn with
    | tmul s t =>
      change ((tensorToUnit a).app M).app U (moduleTensorSection X L M U s t) = _
      rw [tensorToUnit_section]
      rfl
    | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw
  intro s t hst
  obtain ⟨v, rfl⟩ := (moduleTensorSectionLinear_bijective_of_isAffine L M U hU).2 s
  obtain ⟨w, rfl⟩ := (moduleTensorSectionLinear_bijective_of_isAffine L M U hU).2 t
  rw [he, he] at hst
  exact congrArg (moduleTensorSectionLinear X L M U)
    (ht ((TensorProduct.lid Γ(X, U) Γ(M, U)).injective hst))

/-- Tensoring a regular section with an actual line bundle preserves its monomorphism. -/
theorem tensorToUnit_mono {X : Scheme.{u}} (L M : LineBundle X)
    (a : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono a] :
    Mono ((tensorToUnit a).app M.val) := by
  let := lineBundle_isLocallyFree X L
  let := lineBundle_isLocallyFree X M
  let φ := (tensorToUnit a).app M.val
  apply moduleHom_mono_of_app_injective φ
  intro V s t hst
  have hc : Presheaf.equalizerSieve
      (F := (tensorSheaf X L.val M.val).val.presheaf) s t ∈
      (Opens.grothendieckTopology X) V := by
    intro x hxV
    obtain ⟨W, hxW, ⟨e⟩⟩ :=
      (isLocallyRankOne_iff_local_unit X M.val).mp M.property x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ W ⊓ V from ⟨hxW, hxV⟩) (W ⊓ V).isOpen
    let j : U ⟶ V := homOfLE (hUle.trans inf_le_right)
    refine ⟨U, j, ?_, hxU⟩
    let : Module.Flat Γ(X, U) Γ(M.val, U) :=
      Module.Flat.of_linearEquiv (chartSectionEquiv X M.val W e U
        (hUle.trans inf_le_left))
    apply tensorToUnit_app_injective a U hU
    exact (PresheafOfModules.naturality_apply φ.val j.op s).trans
      ((congrArg (M.val.val.map j.op) hst).trans
        (PresheafOfModules.naturality_apply φ.val j.op t).symm)
  apply (tensorSheaf X L.val M.val).isSheaf.isSeparated V _ hc
  intro W j hj
  exact hj

/-- The canonical product section itself is regular, not merely its support. -/
theorem productSection_mono {X : Scheme.{u}} (L M : LineBundle X)
    (a : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono a] [Mono b] :
    Mono (productSection a b) := by
  let := tensorToUnit_mono L M a
  unfold productSection
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Hom

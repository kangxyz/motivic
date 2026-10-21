/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Stalk
public import Aglib.AlgebraicGeometry.Modules.Tensor.AffineSections
public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts

/-! # Literal product ideals of line-bundle sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
universe u

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- The literal product map of two dual sections. -/
def productSection {X : Scheme.{u}} {L M : X.Modules}
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (show X.Modules from tensorSheaf X L M) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  (tensorToUnit a).app M ≫ b

/-- On pure sections, the product is the product of the original coefficients. -/
theorem productSection_tensor {X : Scheme.{u}} {L M : X.Modules}
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)) :
    (productSection a b).app U (moduleTensorSection X L M U s t) =
      (show Γ(X, U) from a.app U s) * (show Γ(X, U) from b.app U t) := by
  change b.app U (((tensorToUnit a).app M).app U _) = _
  rw [tensorToUnit_section, Hom.app_smul]
  rfl

/-- The actual product zero scheme has the product ideal, before taking radicals. -/
theorem sectionImageIdeal_product {X : Scheme.{u}} {L M : X.Modules}
    [L.IsQuasicoherent] [M.IsQuasicoherent]
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (hU : IsAffineOpen U) :
    sectionImageIdeal (productSection a b) U =
      sectionImageIdeal a U * sectionImageIdeal b U := by
  apply le_antisymm
  · rintro z ⟨m, rfl⟩
    obtain ⟨v, rfl⟩ := (moduleTensorSectionLinear_bijective_of_isAffine L M U hU).2 m
    induction v using TensorProduct.inductionOn with
    | tmul s t =>
      change (productSection a b).app U (moduleTensorSection X L M U s t) ∈ _
      rw [productSection_tensor]
      exact Ideal.mul_mem_mul (I := sectionImageIdeal a U)
        (J := sectionImageIdeal b U) ⟨s, rfl⟩ ⟨t, rfl⟩
    | add v w hv hw =>
      simpa only [map_add] using (sectionImageIdeal a U * sectionImageIdeal b U).add_mem hv hw
  · apply Ideal.mul_le.mpr
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨moduleTensorSection X L M U s t, productSection_tensor a b U s t⟩

/-- The kernel stalk of the actual product inclusion is the literal product
of the two original kernel stalk ideals. -/
theorem zeroInclusion_product_stalk {X : Scheme.{u}} {L M : X.Modules}
    [L.IsQuasicoherent] [M.IsQuasicoherent]
    (a : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    (zeroInclusion (productSection a b)).ker.stalk x =
      (zeroInclusion a).ker.stalk x * (zeroInclusion b).ker.stalk x := by
  let : (tensorSheaf X L M).IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor L M
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top x)
  rw [Scheme.IdealSheafData.stalk_eq_map _ ⟨U, hU⟩ hx,
    Scheme.IdealSheafData.stalk_eq_map _ ⟨U, hU⟩ hx,
    Scheme.IdealSheafData.stalk_eq_map _ ⟨U, hU⟩ hx]
  simp only [Scheme.Hom.ker_apply]
  rw [zeroInclusion_kernel (productSection a b)
      (imageIdealLocalizes_of_isQuasicoherent _) ⟨U, hU⟩,
    zeroInclusion_kernel a (imageIdealLocalizes_of_isQuasicoherent _) ⟨U, hU⟩,
    zeroInclusion_kernel b (imageIdealLocalizes_of_isQuasicoherent _) ⟨U, hU⟩,
    sectionImageIdeal_product a b U hU, Ideal.map_mul]

/-- A regular line-bundle section generates its original zero ideal at every
stalk by a regular element. -/
theorem exists_regular_stalk_generator {X : Scheme.{u}} (L : LineBundle X)
    (a : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono a] (x : X) :
    ∃ c : X.presheaf.stalk x, c ∈ nonZeroDivisors (X.presheaf.stalk x) ∧
      (zeroInclusion a).ker.stalk x = Ideal.span {c} := by
  obtain ⟨W, hxW, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  let c : Γ(X, U) := X.presheaf.map (homOfLE hUW).op (Hom.app a W (chartGenerator X L.val W e))
  let r := (X.presheaf.germ U x hxU).hom
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := r.toAlgebra
  let := hU.isLocalization_stalk ⟨x, hxU⟩
  let : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
    IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hc : IsSMulRegular Γ(X, U) c :=
    (app_injective_iff_chart_regular L a W e U hUW).mp (moduleHom_app_injective a U)
  have hr : IsSMulRegular (X.presheaf.stalk x) (r c) := hc.of_flat
  refine ⟨r c, ?_, ?_⟩
  · exact ⟨fun z hz => hr (by simpa using hz),
      fun z hz => hr (by simpa [mul_comm] using hz)⟩
  · rw [Scheme.IdealSheafData.stalk_eq_map _ ⟨U, hU⟩ hxU, Scheme.Hom.ker_apply,
      zeroInclusion_kernel_eq_span_chart L a W e ⟨U, hU⟩ hUW, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl

/-- Actual regular line-bundle sections supply the simultaneous principal
stalk equations used by product zero-cycle additivity. -/
theorem productSection_stalk_equations {X : Scheme.{u}} (L M : LineBundle X)
    (a : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono a] [Mono b] (x : X) :
    ∃ c d : X.presheaf.stalk x, d ∈ nonZeroDivisors (X.presheaf.stalk x) ∧
      (zeroInclusion a).ker.stalk x = Ideal.span {c} ∧
      (zeroInclusion b).ker.stalk x = Ideal.span {d} ∧
      (zeroInclusion (productSection a b)).ker.stalk x = Ideal.span {c * d} := by
  let := lineBundle_isLocallyFree X L
  let := lineBundle_isLocallyFree X M
  obtain ⟨c, -, hc⟩ := exists_regular_stalk_generator L a x
  obtain ⟨d, hd, hdi⟩ := exists_regular_stalk_generator M b x
  refine ⟨c, d, hd, hc, hdi, ?_⟩
  rw [zeroInclusion_product_stalk, hc, hdi, Ideal.span_singleton_mul_span_singleton]

end AlgebraicGeometry.Scheme.Modules.Hom

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafProducts.ObjectwiseExact

/-! # Actual product sequences for sectionwise-surjective ordinary sheaf maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.Sheaf.Products
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {I : Type v} (D : I → ShortComplex (Sheaf J AddCommGrpCat.{max u v}))

/-- The original product maps form the ordinary sheaf short complex. -/
def productComplex : ShortComplex (Sheaf J AddCommGrpCat.{max u v}) :=
  ShortComplex.mk (Limits.Pi.map fun i => (D i).f) (Limits.Pi.map fun i => (D i).g) (by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc,
      ShortComplex.zero, comp_zero, zero_comp])

/-- Kernel exactness of products uses only their universal property. -/
theorem productComplex_exact (hD : ∀ i, (D i).ShortExact) :
    (productComplex J D).Exact := by
  have (i : I) : Mono (D i).f := (hD i).mono_f
  have : Mono (productComplex J D).f := inferInstanceAs
    (Mono (Limits.Pi.map fun i => (D i).f))
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro W k hk
  have hc (i : I) : (k ≫ Limits.Pi.π (fun i => (D i).X₂) i) ≫ (D i).g = 0 := by
    have hh := congrArg (fun a => a ≫ Limits.Pi.π (fun i => (D i).X₃) i) hk
    simpa only [productComplex, Category.assoc, Limits.Pi.map_π,
      zero_comp] using hh
  let l (i : I) := (hD i).exact.fIsKernel.lift
    (KernelFork.ofι (k ≫ Limits.Pi.π (fun i => (D i).X₂) i) (hc i))
  refine ⟨Limits.Pi.lift l, ?_⟩
  apply Limits.Pi.hom_ext
  intro i
  change (Limits.Pi.lift l ≫ Limits.Pi.map (fun i => (D i).f)) ≫ _ = _
  rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc]
  exact (hD i).exact.fIsKernel.fac _ WalkingParallelPair.zero

/-- Products are short exact under the stronger, explicit presheaf-surjectivity condition. -/
theorem productComplex_shortExact (hD : ∀ i, (D i).ShortExact)
    [∀ i, Epi (D i).g.hom] : (productComplex J D).ShortExact := by
  have (i : I) : Mono (D i).f := (hD i).mono_f
  exact
    { exact := productComplex_exact J D hD
      mono_f := inferInstanceAs (Mono (Limits.Pi.map fun i => (D i).f))
      epi_g := epi_piMap_of_presheaf_epi J _ _ (fun i => (D i).g) }

end CategoryTheory.Sheaf.Products

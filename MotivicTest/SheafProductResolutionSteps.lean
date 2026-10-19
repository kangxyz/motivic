/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafProducts.ShortExact
public import Motivic.Aglib.CategoryTheory.Abelian.Ext.ResolutionSteps
public import Lean.Util.CollectAxioms

/-! Products use sectionwise surjectivity, while Ext uses explicit ordinary injective steps. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace MotivicTest.SheafProductResolutionSteps
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {I : Type v} (D : I → ShortComplex (Sheaf J AddCommGrpCat.{max u v}))

/-- No arbitrary-product exactness assumption on the sheaf category is made. -/
theorem actual_product_shortExact (hD : ∀ i, (D i).ShortExact)
    [∀ i, Epi (D i).g.hom] : (Sheaf.Products.productComplex J D).ShortExact :=
  Sheaf.Products.productComplex_shortExact J D hD

open Lean in
run_cmd do
  for name in #[``actual_product_shortExact,
      ``_root_.CategoryTheory.Sheaf.Products.presheaf_epi_piMap_of_presheaf_epi,
      ``_root_.CategoryTheory.Sheaf.Products.productComplex_exact,
      ``_root_.CategoryTheory.Ext.ext_eq_zero_of_resolution_steps] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Sectionwise products and explicit ordinary Ext steps: standard foundations only."

end MotivicTest.SheafProductResolutionSteps

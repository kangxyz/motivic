/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafProductShortExact
public import Motivic.Cohomology.ExtAcyclicResolutionSteps
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
    [∀ i, Epi (D i).g.hom] : (Motivic.SheafProduct.productComplex J D).ShortExact :=
  Motivic.SheafProduct.productComplex_shortExact J D hD

open Lean in
run_cmd do
  for name in #[``actual_product_shortExact,
      ``Motivic.SheafProduct.presheaf_epi_piMap_of_presheaf_epi,
      ``Motivic.SheafProduct.productComplex_exact,
      ``Motivic.Cohomology.ext_eq_zero_of_resolution_steps] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Sectionwise products and explicit ordinary Ext steps: standard foundations only."

end MotivicTest.SheafProductResolutionSteps

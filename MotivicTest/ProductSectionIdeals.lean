import Motivic.Aglib.AlgebraicGeometry.ProductSectionIdeals

/-! Direct checks of the literal tensor product and regular stalk generators. -/

open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible

example {X : Scheme} (L M : LineBundle X)
    (a : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono a] [Mono b] (x : X) :
    ∃ c d : X.presheaf.stalk x, d ∈ nonZeroDivisors (X.presheaf.stalk x) ∧
      (Hom.zeroInclusion a).ker.stalk x = Ideal.span {c} ∧
      (Hom.zeroInclusion b).ker.stalk x = Ideal.span {d} ∧
      (Hom.zeroInclusion (Hom.productSection a b)).ker.stalk x = Ideal.span {c * d} :=
  Hom.productSection_stalk_equations L M a b x

set_option linter.hashCommand false
#print axioms Hom.productSection_stalk_equations
#print axioms Hom.zeroInclusion_product_stalk

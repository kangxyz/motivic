module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.PushforwardTensorComposition

/-! Direct-image tensor composition uses the native composition comparison, without hypotheses. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u

example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : X.Modules) :=
  pushforwardTensorMap_comp f g M N

#print axioms pushforwardTensorMap_comp

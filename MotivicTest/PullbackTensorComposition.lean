module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.PullbackTensorComposition
/-! # The exact native pullback tensor comparison composes with the native pullback functor -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (pullback f).map (pullbackTensorMap g M N) ≫
      pullbackTensorMap f ((pullback g).obj M) ((pullback g).obj N) ≫
      tensorSheafMap X ((pullbackComp f g).hom.app M) ((pullbackComp f g).hom.app N) =
    (pullbackComp f g).hom.app (tensorSheaf Z M N) ≫
      pullbackTensorMap (f ≫ g) M N := pullbackTensorMap_comp f g M N

open Lean in
run_cmd do
  for name in #[``pullbackTensorMap_comp, ``pullbackTensorComposition_unit] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original tensor pullback composition uses only standard foundations."

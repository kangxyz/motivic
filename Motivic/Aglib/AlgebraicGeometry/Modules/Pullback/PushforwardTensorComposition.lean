/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Basic

/-! # Composition of the actual direct-image tensor comparisons -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical direct-image tensor maps respect the actual composition comparison. -/
@[reassoc] theorem pushforwardTensorMap_comp (M N : X.Modules) :
    pushforwardTensorMap g ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N) ≫
      (Scheme.Modules.pushforward g).map (pushforwardTensorMap f M N) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (tensorSheaf X M N) =
    tensorSheafMap Z ((Scheme.Modules.pushforwardComp f g).hom.app M)
        ((Scheme.Modules.pushforwardComp f g).hom.app N) ≫
      pushforwardTensorMap (f ≫ g) M N := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 Z.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change (pushforwardTensorMap f M N).val.app (op (g ⁻¹ᵁ U.unop))
      ((pushforwardTensorMap g ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N)).val.app U
        ((tensorSheafUnit Z
          ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
          ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj N))).app U
            (m ⊗ₜ n))) =
    (pushforwardTensorMap (f ≫ g) M N).val.app U
      ((tensorSheafMap Z ((Scheme.Modules.pushforwardComp f g).hom.app M)
        ((Scheme.Modules.pushforwardComp f g).hom.app N)).val.app U
        ((tensorSheafUnit Z
          ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
          ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj N))).app U
            (m ⊗ₜ n)))
  have h₁ := pushforwardTensorMap_tmul g ((Scheme.Modules.pushforward f).obj M)
    ((Scheme.Modules.pushforward f).obj N) U m n
  have h₂ := pushforwardTensorMap_tmul f M N (op (g ⁻¹ᵁ U.unop)) m n
  have h₃ := tensorSheafMap_tmul Z ((Scheme.Modules.pushforwardComp f g).hom.app M)
    ((Scheme.Modules.pushforwardComp f g).hom.app N) U m n
  have h₄ := pushforwardTensorMap_tmul (f ≫ g) M N U m n
  exact ((congrArg (fun z ↦
      (pushforwardTensorMap f M N).val.app (op (g ⁻¹ᵁ U.unop)) z) h₁).trans h₂).trans
    (((congrArg (fun z ↦ (pushforwardTensorMap (f ≫ g) M N).val.app U z) h₃).trans h₄).symm)

end AlgebraicGeometry.Scheme.Modules

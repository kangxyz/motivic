/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.FunctionalQuotientAffineChart
/-! # The original generic ratio norm under the identity pullback

The identity compactification map in an actual two-term norm diagram still
pulls the original functionals literally. Canonical pullback composition shows
that its ratio norm is the unchanged original ratio norm. The finite source
need not be integral, connected, reduced, or free.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.LineRatioIdentity`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeCorrectionTransferAction`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The literal identity pullback retains regularity of the original functional. -/
theorem pullbackUnitMap_id_mono {C : Scheme.{u}} {M : C.Modules}
    (a : M ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono a] :
    Mono (pullbackUnitMap (𝟙 C) a) := by
  dsimp only [pullbackUnitMap]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme
open Modules Modules.Invertible

/-- The compact identity leg preserves the exact original generic ratio norm,
not merely its divisor or its induced presheaf action. -/
theorem genericFiberLineRatioNorm_pullback_id
    {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
    (L : LineBundle C) (a c : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [Mono a] [Mono c] :
    let := pullbackUnitMap_id_mono a
    let := pullbackUnitMap_id_mono c
    genericFiberLineRatioNorm f (pullbackLineBundle (𝟙 C) L)
        (pullbackUnitMap (𝟙 C) a) (pullbackUnitMap (𝟙 C) c) =
      genericFiberLineRatioNorm f L a c := by
  let := pullbackUnitMap_id_mono a
  let := pullbackUnitMap_id_mono c
  let G := Limits.pullback f (T.fromSpecStalk (genericPoint T))
  let n := pullback.fst f (T.fromSpecStalk (genericPoint T))
  let : IsIso (pullbackUnitMap n c) := genericFiberLineMap_isIso f L c
  let : IsIso (pullbackUnitMap (n ≫ 𝟙 C) c) := by
    exact (congrArg (fun w : G ⟶ C => IsIso (pullbackUnitMap w c))
      (Category.comp_id n)).mpr inferInstance
  let : IsIso (pullbackUnitMap n (pullbackUnitMap (𝟙 C) c)) :=
    genericFiberLineMap_isIso f (pullbackLineBundle (𝟙 C) L) (pullbackUnitMap (𝟙 C) c)
  have hquot (w : G ⟶ C) (hw : w = n) [IsIso (pullbackUnitMap w c)] :
      inv (pullbackUnitMap w c) ≫ pullbackUnitMap w a =
        inv (pullbackUnitMap n c) ≫ pullbackUnitMap n a := by
    subst w
    rfl
  have hθ : inv (pullbackUnitMap n (pullbackUnitMap (𝟙 C) c)) ≫
      pullbackUnitMap n (pullbackUnitMap (𝟙 C) a) =
      inv (pullbackUnitMap n c) ≫ pullbackUnitMap n a := by
    exact (functionalQuotient_comp (𝟙 C) n a c).trans (hquot _ (Category.comp_id n))
  have hu : (genericFiberLineRatioUnit f (pullbackLineBundle (𝟙 C) L)
        (pullbackUnitMap (𝟙 C) a) (pullbackUnitMap (𝟙 C) c)).val =
      (genericFiberLineRatioUnit f L a c).val := by
    change (show Γ(G, ⊤) from Modules.Hom.app
      (inv (pullbackUnitMap n (pullbackUnitMap (𝟙 C) c)) ≫
        pullbackUnitMap n (pullbackUnitMap (𝟙 C) a)) ⊤ (1 : Γ(G, ⊤))) =
      (show Γ(G, ⊤) from Modules.Hom.app
        (inv (pullbackUnitMap n c) ≫ pullbackUnitMap n a) ⊤ (1 : Γ(G, ⊤)))
    exact congrArg (fun θ : (SheafOfModules.unit G.ringCatSheaf : G.Modules) ⟶
        SheafOfModules.unit G.ringCatSheaf =>
      (show Γ(G, ⊤) from Modules.Hom.app θ ⊤ (1 : Γ(G, ⊤)))) hθ
  let : Algebra T.functionField Γ(G, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
  exact congrArg (Algebra.norm T.functionField) hu

end AlgebraicGeometry.Scheme

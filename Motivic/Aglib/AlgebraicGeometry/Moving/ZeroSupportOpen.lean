/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange
/-! # Original whole zero schemes retain their support under an open restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Moving

/-- The full pulled-back zero scheme maps to the original full zero scheme. -/
def zeroPullbackToOriginal {C X : Scheme.{u}} {M : C.Modules}
    (a : M ⟶ SheafOfModules.unit C.ringCatSheaf) [M.IsQuasicoherent] (j : X ⟶ C) :
    Hom.zeroScheme (Hom.pullbackToUnit a j) ⟶ Hom.zeroScheme a :=
  (Hom.zeroSchemePullbackIso a j).hom ≫ pullback.snd _ _

@[reassoc] theorem zeroPullbackToOriginal_inclusion {C X : Scheme.{u}} {M : C.Modules}
    (a : M ⟶ SheafOfModules.unit C.ringCatSheaf) [M.IsQuasicoherent] (j : X ⟶ C) :
    zeroPullbackToOriginal a j ≫ Hom.zeroInclusion a =
      Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j := by
  simp only [zeroPullbackToOriginal, Category.assoc, ← pullback.condition,
    Hom.zeroSchemePullbackIso_hom_fst_assoc]

/-- No reduction or pointwise replacement of the zero scheme is involved: its
literal open lift exists because the original entire zero support lies there. -/
theorem zeroSupport_restrict {C X V : Scheme.{u}} {M : C.Modules}
    (a : M ⟶ SheafOfModules.unit C.ringCatSheaf) [M.IsQuasicoherent]
    (j : X ⟶ C) [IsOpenImmersion j] (w : V ⟶ X)
    (h : Set.range (Hom.zeroInclusion a) ⊆ Set.range (w ≫ j)) :
    Set.range (Hom.zeroInclusion (Hom.pullbackToUnit a j)) ⊆ Set.range w := by
  rintro _ ⟨x, rfl⟩
  have hx : j ((Hom.zeroInclusion (Hom.pullbackToUnit a j)) x) ∈
      Set.range (Hom.zeroInclusion a) := by
    refine ⟨zeroPullbackToOriginal a j x, ?_⟩
    exact congrArg (fun f => f x) (zeroPullbackToOriginal_inclusion a j)
  obtain ⟨v, hv⟩ := h hx
  refine ⟨v, j.isOpenEmbedding.injective ?_⟩
  exact hv

end AlgebraicGeometry.Scheme.Moving

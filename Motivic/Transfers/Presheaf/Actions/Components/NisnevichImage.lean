/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Sheafification.Image
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
/-! # Reassemble original image actions from the actual component cover

Only the separated image of the original sheafification unit is used here.
No arbitrary transfer-presheaf restriction is cancelled. Empty covers are
included: the covering-sieve separatedness argument also handles empty sources.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Componentwise action identities on a genuine cover determine the action on
its entire original source, specifically for the separated original image. -/
theorem nisnevichImage_transfer_eq_of_cover
    (P : PresheafWithTransfers.{u + 1} k)
    {X T : SmoothSite (Spec (.of k))} {I : Type*}
    (Y : I → SmoothSite (Spec (.of k))) (f : ∀ i, Y i ⟶ X)
    (hcover : Sieve.ofArrows Y f ∈ SmoothSite.nisnevichTopology (Spec (.of k)) X)
    (c d : Cor.mk X ⟶ Cor.mk T)
    (h : ∀ i, (nisnevichImage P).transfer ((Cor.graphFunctor k).map (f i) ≫ c) =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map (f i) ≫ d)) :
    (nisnevichImage P).transfer c = (nisnevichImage P).transfer d := by
  ext x
  apply nisnevichImage_isSeparated P X (Sieve.ofArrows Y f) hcover
  intro W g hg
  obtain ⟨i, a, rfl⟩ := Sieve.ofArrows.exists hg
  let F := (toPresheaf k).obj (nisnevichImage P)
  have hi := h i
  rw [transfer_comp, transfer_comp] at hi
  have hx := ConcreteCategory.congr_hom hi x
  change F.map (f i).op ((nisnevichImage P).transfer c x) =
    F.map (f i).op ((nisnevichImage P).transfer d x) at hx
  change F.map (a ≫ f i).op ((nisnevichImage P).transfer c x) =
    F.map (a ≫ f i).op ((nisnevichImage P).transfer d x)
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact congrArg (fun y => F.map a.op y) hx

/-- Use the actual scheme open cover, in particular the canonical domain-stalk
component cover. Neither finiteness nor nonemptiness is imposed for detection. -/
theorem nisnevichImage_transfer_eq_of_openCover
    (P : PresheafWithTransfers.{u + 1} k)
    {X T : SmoothSite (Spec (.of k))} (C : X.left.OpenCover)
    (c d : Cor.mk X ⟶ Cor.mk T)
    (h : ∀ i,
      (nisnevichImage P).transfer
        ((Cor.graphFunctor k).map
          (SmoothSite.homMk (C.f i) rfl : SmoothSite.mk (C.f i ≫ X.hom) ⟶ X) ≫ c) =
      (nisnevichImage P).transfer
        ((Cor.graphFunctor k).map
          (SmoothSite.homMk (C.f i) rfl : SmoothSite.mk (C.f i ≫ X.hom) ⟶ X) ≫ d)) :
    (nisnevichImage P).transfer c = (nisnevichImage P).transfer d := by
  let Y (i : C.I₀) : SmoothSite (Spec (.of k)) := SmoothSite.mk (C.f i ≫ X.hom)
  let f (i : C.I₀) : Y i ⟶ X := SmoothSite.homMk (C.f i) rfl
  have hcover : Sieve.ofArrows Y f ∈ SmoothSite.nisnevichTopology (Spec (.of k)) X := by
    apply (SmoothSite.mem_nisnevichTopology_iff).mpr
    refine ⟨Presieve.ofArrows Y f, ?_, Sieve.le_generate _⟩
    change (Presieve.ofArrows Y f).map (SmoothSite.forgetScheme _) ∈
      Nisnevich.precoverage X.left
    rw [Presieve.map_ofArrows]
    exact Nisnevich.zariskiPrecoverage_le_precoverage _ C.mem₀
  exact nisnevichImage_transfer_eq_of_cover P Y f hcover c d h

end Motivic.PresheafWithTransfers

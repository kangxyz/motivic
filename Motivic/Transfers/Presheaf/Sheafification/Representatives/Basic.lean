/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Sheafification.Image


/-!
# Genuine Nisnevich covers representing sections in the unit image

The actual correspondence topology has a basis of singleton graph covers.
Local representability for its canonical sheafification unit therefore gives
one genuine smooth Nisnevich cover on which a given section lifts to the unit
image. Its two restrictions agree over every test object mapping to the cover
over the same base map, since that image embeds in the sheafification.

Applied to an original cylinder, this retains the entire cylinder as the cover's
base. It does not glue the image section on that cover to a section on the whole
cylinder, even after shrinking the base. No homotopy invariance is needed here.
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

/-- A section of the actual sheafification is represented on a genuine singleton
Nisnevich cover by a section of the actual unit image, with all original-map
matching equations. This is cover representability, not descent for the image. -/
theorem exists_nisnevichImage_representing_cover
    (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k)))
    (g : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk X)) :
    ∃ (V : SmoothSite (Spec (.of k))) (q : V ⟶ X),
      Cor.IsNisnevichCover k q ∧
      ∃ t : (nisnevichImage P).sections (Cor.mk V),
        (nisnevichImageι P).hom.app (op (Cor.mk V)) t =
          ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map q) g ∧
        ∀ (W : SmoothSite (Spec (.of k))) (a b : W ⟶ V), a ≫ q = b ≫ q →
          (nisnevichImage P).transfer ((Cor.graphFunctor k).map a) t =
            (nisnevichImage P).transfer ((Cor.graphFunctor k).map b) t := by
  let η := toNisnevichSheafify k P
  have : Presheaf.IsLocallySurjective (Cor.nisnevichTopology k) η.hom := by
    change Presheaf.IsLocallySurjective (Cor.nisnevichTopology k)
      (toSheafify (Cor.nisnevichTopology k) P.obj)
    infer_instance
  obtain ⟨V, q, hq, p, hp⟩ := (Cor.mem_nisnevichTopology_iff k).mp
    (Presheaf.imageSieve_mem (Cor.nisnevichTopology k) η.hom g)
  let t := (toNisnevichImage P).hom.app (op (Cor.mk V)) p
  have ht : (nisnevichImageι P).hom.app (op (Cor.mk V)) t =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map q) g := by
    have he := congrArg (fun f : P ⟶ ((nisnevichSheafify k).obj P).obj =>
      f.hom.app (op (Cor.mk V))) (toNisnevichImage_ι P)
    have he' := ConcreteCategory.congr_hom he p
    exact he'.trans hp
  refine ⟨V, q, hq, t, ht, ?_⟩
  intro W a b hab
  apply (AddCommGrpCat.mono_iff_injective
    ((nisnevichImageι P).hom.app (op (Cor.mk W)))).mp inferInstance
  have hn (c : W ⟶ V) :
      (nisnevichImageι P).hom.app (op (Cor.mk W))
        ((nisnevichImage P).transfer ((Cor.graphFunctor k).map c) t) =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map c)
        ((nisnevichImageι P).hom.app (op (Cor.mk V)) t) :=
    (nisnevichImageι P).hom.naturality_apply ((Cor.graphFunctor k).map c).op t
  rw [hn a, hn b, ht]
  have he := congrArg (fun f : W ⟶ X =>
    ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map f) g) hab
  simpa only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] using he

end Motivic.PresheafWithTransfers

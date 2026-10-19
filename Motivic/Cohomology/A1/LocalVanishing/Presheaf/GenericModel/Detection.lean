/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.DenseOpen.Detection
public import Motivic.Cohomology.A1.LocalVanishing.Presheaf.Model.GenericZero
public import Motivic.Transfers.Presheaf.NisnevichLocalZero

/-! # Generic-model vanishing detects the actual Nisnevich sheafification

The generic object is the existing filtered colimit over actual opens of an
integral smooth model. Equality in that colimit gives an original open-zero
witness. Over an infinite field, affine component neighborhoods then cover every
smooth object by original zero restrictions. Only the sheafification is asserted
to be zero; the original homotopy-invariant presheaf is not replaced by a sheaf.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Zero in the actual generic-neighborhood colimit has an actual open-zero
representative. No field replacement or restriction/sheafification exchange is used. -/
theorem exists_generic_open_zero_of_genericModelGerm_eq_zero
    (P : PresheafWithTransfers.{u + 1} k) (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (hG : ∀ s : genericModelGerm.{0, u} P X, s = 0)
    (s : P.sections (Cor.mk X)) :
    ∃ V : X.left.Opens, genericPoint X.left ∈ V ∧
      P.transfer ((Cor.graphFunctor k).map (SmoothSite.openInclusion X V)) s = 0 := by
  let D := (OpenNhds.inclusion (genericPoint X.left)).op ⋙ modelOpenPresheaf.{0, u} P X
  let U : (OpenNhds (genericPoint X.left))ᵒᵖ := op ⟨⊤, by trivial⟩
  let t : D.obj U := P.transfer ((Cor.graphFunctor k).map (SmoothSite.openInclusion X ⊤)) s
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have he : colimit.ι D U t = colimit.ι D U 0 := by
    rw [map_zero]
    exact hG _
  obtain ⟨V, i, hz⟩ := ((colimit.isColimit D).eq_iff' t 0).mp he
  let j : V.unop.val ⟶ (⊤ : X.left.Opens) := i.unop
  have hi : (SmoothSite.opensFunctor X).map j ≫ SmoothSite.openInclusion X ⊤ =
      SmoothSite.openInclusion X V.unop.val := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.homOfLE_ι X.left j.le
  change P.transfer ((Cor.graphFunctor k).map ((SmoothSite.opensFunctor X).map j)) t =
    P.transfer ((Cor.graphFunctor k).map ((SmoothSite.opensFunctor X).map j)) 0 at hz
  refine ⟨V.unop.val, V.unop.property, ?_⟩
  rw [← hi, Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]
  simpa only [map_zero] using hz

variable [Infinite k]

/-- Integral affine component neighborhoods detect zero at every point of every
smooth object. The input ranges only over genuine integral affine smooth models. -/
theorem exists_zero_neighborhood_of_genericModelGerm_eq_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
      (s : genericModelGerm.{0, u} P T), s = 0)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)) (x : X.left) :
    ∃ O : X.left.Opens, x ∈ O ∧ smoothAffineZeroOpen P X s O := by
  let C := SmoothSite.integralAffineCover k X
  obtain ⟨i, t, ht⟩ := C.exists_eq x
  let T : SmoothSite (Spec (.of k)) := SmoothSite.mk (C.f i ≫ X.hom)
  let f : T ⟶ X := SmoothSite.homMk (C.f i) rfl
  have : IsAffine T.left := inferInstanceAs (IsAffine (C.X i))
  have : IsIntegral T.left := inferInstanceAs (IsIntegral (C.X i))
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (C.f i))
  let v := P.transfer ((Cor.graphFunctor k).map f) s
  obtain ⟨V, hV, hzV⟩ := P.exists_generic_open_zero_of_genericModelGerm_eq_zero T (hG T) v
  let A := (SmoothSite.opensFunctor T).obj V
  have : Nonempty A.left := ⟨⟨genericPoint T.left, hV⟩⟩
  have : IsOpenImmersion (SmoothSite.openInclusion T V).left :=
    inferInstanceAs (IsOpenImmersion V.ι)
  obtain ⟨O, hO, htO, hzO⟩ := P.exists_zero_neighborhood_of_integral_affine
    (SmoothSite.openInclusion T V) hP v hzV t
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ T.hom)
  let o : S ⟶ T := SmoothSite.homMk O.ι rfl
  let g := o ≫ f
  have : IsAffine S.left := hO
  have : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ C.f i))
  have hg : P.transfer ((Cor.graphFunctor k).map g) s = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hzO
  exact ⟨g.left.opensRange, ⟨⟨t, htO⟩, ht⟩,
    isAffineOpen_opensRange g.left, P.zero_on_open_image_general g s hg⟩

/-- The original zero restrictions cover in the actual smooth Nisnevich topology. -/
theorem zeroSieve_mem_of_genericModelGerm_eq_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
      (s : genericModelGerm.{0, u} P T), s = 0)
    (X : SmoothSite (Spec (.of k))) (s : ((toPresheaf k).obj P).obj (op X)) :
    Presheaf.equalizerSieve s 0 ∈ SmoothSite.nisnevichTopology (Spec (.of k)) X := by
  choose O hx hO using
    fun x => P.exists_zero_neighborhood_of_genericModelGerm_eq_zero hP hG X s x
  let U (x : X.left) := SmoothSite.mk ((O x).ι ≫ X.hom)
  let f (x : X.left) : U x ⟶ X := SmoothSite.homMk (O x).ι rfl
  let (x : X.left) : IsOpenImmersion (f x).left :=
    inferInstanceAs (IsOpenImmersion (O x).ι)
  apply SmoothSite.mem_nisnevichTopology_iff.mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · apply (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun _ => inferInstance, fun x => ⟨x, ⟨x, hx x⟩, rfl, inferInstance⟩⟩
  · rw [Presieve.ofArrows_le_iff]
    intro x
    change P.transfer ((Cor.graphFunctor k).map (f x)) s =
      P.transfer ((Cor.graphFunctor k).map (f x)) 0
    rw [map_zero]
    exact (hO x).2

/-- Infinite-field generic detection kills the genuine transfer sheafification of
the original HI presheaf, with no presheaf sheafness or strict-invariance premise. -/
theorem isZero_nisnevichSheafify_of_genericModelGerm_eq_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
      (s : genericModelGerm.{0, u} P T), s = 0) :
    IsZero ((nisnevichSheafify k).obj P) :=
  P.isZero_nisnevichSheafify_of_locally_zero
    (P.zeroSieve_mem_of_genericModelGerm_eq_zero hP hG)

end Motivic.PresheafWithTransfers

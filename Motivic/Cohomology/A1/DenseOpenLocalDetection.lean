/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.IntegralAffineDetection
public import Motivic.Cohomology.A1.GeneralOpenImageVanishing
public import Motivic.AlgebraicGeometry.SmoothSiteIntegralAffineSheafIso
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks

/-! # Genuine dense-open local detection for arbitrary smooth schemes

The actual integral affine component cover is used, not an integrality assumption
on all smooth objects. The conclusion is local zero for an arbitrary HI presheaf;
no sheaf separatedness or field-continuity assertion is implicit.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k] [Infinite k]

/-- An affine open of the original smooth object on which the original section vanishes. -/
def smoothAffineZeroOpen (P : PresheafWithTransfers.{w} k)
    (X : SmoothSite (Spec (.of k))) (v : P.sections (Cor.mk X)) (O : X.left.Opens) : Prop :=
  IsAffineOpen O ∧ P.transfer ((Cor.graphFunctor k).map
    (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0

/-- Vanishing on an original dense open implies vanishing on an affine Zariski
neighborhood of each original point, for any HI presheaf with transfers. -/
theorem exists_zero_neighborhood_of_dense_open
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left) :
    ∃ (O : X.left.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 := by
  let C := SmoothSite.integralAffineCover k X
  obtain ⟨i, t, ht⟩ := C.exists_eq x
  let T := SmoothSite.mk (C.f i ≫ X.hom)
  let f : T ⟶ X := SmoothSite.homMk (C.f i) rfl
  have : IsAffine T.left := inferInstanceAs (IsAffine (C.X i))
  have : IsIntegral T.left := inferInstanceAs (IsIntegral (C.X i))
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (C.f i))
  let B := SmoothSite.etalePullback a f
  let j : B ⟶ T := SmoothSite.etalePullbackSnd a f
  let b : B ⟶ A := SmoothSite.etalePullbackFst a f
  have : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd a.left f.left))
  have : Nonempty B.left := by
    obtain ⟨y, ⟨t', ht'⟩, hy⟩ := ha.inter_open_nonempty
      (Set.range f.left) f.left.isOpenEmbedding.isOpen_range ⟨f.left t, t, rfl⟩
    have hm : t' ∈ Set.range (pullback.snd a.left f.left) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      change f.left t' ∈ Set.range a.left
      rwa [ht']
    obtain ⟨v, _⟩ := hm
    exact ⟨v⟩
  have hj : j ≫ f = b ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm
  have hv' : P.transfer ((Cor.graphFunctor k).map j)
      (P.transfer ((Cor.graphFunctor k).map f) v) = 0 := by
    have he := ConcreteCategory.congr_hom
      (congrArg P.transfer (congrArg (Cor.graphFunctor k).map hj)) v
    simpa only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply, hv, map_zero] using he
  obtain ⟨O, hO, htO, hz⟩ :=
    P.exists_zero_neighborhood_of_integral_affine j hP
      (P.transfer ((Cor.graphFunctor k).map f) v) hv' t
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ T.hom)
  let o : S ⟶ T := SmoothSite.homMk O.ι rfl
  let g := o ≫ f
  have : IsAffine S.left := hO
  have : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ C.f i))
  have hg : P.transfer ((Cor.graphFunctor k).map g) v = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hz
  refine ⟨g.left.opensRange, isAffineOpen_opensRange g.left, ?_,
    P.zero_on_open_image_general g v hg⟩
  exact ⟨⟨t, htO⟩, ht⟩

/-- The actual affine zero-neighborhoods cover an arbitrary smooth object, including
disconnected and empty objects. Dense-open vanishing is only used locally. -/
theorem iSup_zero_opens_of_dense_open
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    (⨆ O : {O : X.left.Opens // smoothAffineZeroOpen P X v O}, O.val) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨O, hO, hxO, hz⟩ := P.exists_zero_neighborhood_of_dense_open a ha hP v hv x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨O, hO, hz⟩, hxO⟩

end Motivic.PresheafWithTransfers

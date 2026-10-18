/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafGenericModelDetection
public import Motivic.Cohomology.A1.BoundaryCokernelSheaf
public import Motivic.AlgebraicGeometry.SmoothSiteSectionDetection
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleNisnevich
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Original coefficient detection from an explicit local-zero input

The input is Zariski-local zero for the unchanged HI presheaf with transfers,
not separatedness or strict invariance. The consumers retain literal graph
restrictions, the ordinary coefficient map and small-site sheafification.
No finite-field local-zero producer is asserted by these conditional results.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace Motivic.PresheafWithTransfers

/-- The original integral-affine local-zero contract for arbitrary HI presheaves.
This explicit input is not a typeclass or an asserted finite-field theorem. -/
def IntegralAffineLocalZero (k : Type u) [Field k] : Prop :=
  ∀ {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsIntegral X.left]
    [Nonempty A.left] (a : A ⟶ X) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{u + 1} k) (_hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (_hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left),
    ∃ (O : X.left.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0

variable {k : Type u} [Field k]

/-- The original dense-open restriction has affine zero neighborhoods from the input. -/
theorem exists_zero_neighborhood_of_dense_open_of_integralAffineLocalZero
    (hD : IntegralAffineLocalZero k)
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
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
    hD j P hP
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

/-- Generic-model zero gives original zero neighborhoods without a field-size premise. -/
theorem exists_zero_neighborhood_of_genericModelGerm_eq_zero_of_integralAffineLocalZero
    (hD : IntegralAffineLocalZero k)
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
  obtain ⟨O, hO, htO, hzO⟩ := hD (SmoothSite.openInclusion T V) P hP v hzV t
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

end Motivic.PresheafWithTransfers

namespace Motivic.SheafWithTransfers
open PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Separatedness is used only for the original Nisnevich sheaf coefficient. -/
theorem section_eq_zero_of_dense_open_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k) {X A : SmoothSite (Spec (.of k))}
    (a : A ⟶ X) [IsOpenImmersion a.left] (ha : DenseRange a.left)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (s : F.obj.sections (Cor.mk X))
    (hs : F.obj.transfer ((Cor.graphFunctor k).map a) s = 0) : s = 0 := by
  classical
  have hlocal := exists_zero_neighborhood_of_dense_open_of_integralAffineLocalZero
    hD a ha F.obj hF s hs
  choose O hO hx hz using hlocal
  exact SmoothSite.section_eq_zero_of_residue_splitting_family
    ((SheafWithTransfers.toSheaf k).obj F)
    (fun x => SmoothSite.mk ((O x).ι ≫ X.hom))
    (fun x => SmoothSite.homMk (O x).ι rfl)
    (fun x => inferInstanceAs (Etale (O x).ι))
    (fun x => ⟨x, ⟨x, hx x⟩, rfl,
      inferInstanceAs (IsIso ((O x).ι.residueFieldMap ⟨x, hx x⟩))⟩) s hz

end Motivic.SheafWithTransfers

namespace Motivic.FiniteEtaleSite
open PresheafWithTransfers
variable {k : Type u} [Field k]

/-- The literal coefficient restriction is monic, tested on actual etale objects. -/
theorem restrictionToDirectImage_mono_of_dense_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (hj : DenseRange j.left) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F) j) := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro V
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  let a := (restrictionProjection j).app V.unop
  let : IsOpenImmersion a.left :=
    inferInstanceAs (IsOpenImmersion (pullback.fst V.unop.hom j.left))
  have ha : DenseRange a.left := by
    change Dense (Set.range (pullback.fst V.unop.hom j.left))
    rw [IsOpenImmersion.range_pullbackFst]
    exact hj.preimage V.unop.hom.isOpenMap
  exact SheafWithTransfers.section_eq_zero_of_dense_open_of_integralAffineLocalZero
    hD a ha F hF s hs

/-- Original zero neighborhoods form a covering sieve on each small-site object. -/
theorem zeroSieve_mem_of_genericModelGerm_eq_zero_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
      (s : PresheafWithTransfers.genericModelGerm.{0, u} P T), s = 0)
    (X : SmoothSite (Spec (.of k))) (T : FiniteEtaleSite X.left)
    (s : ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj P).obj (op T)) :
    Presheaf.equalizerSieve s 0 ∈ nisnevichTopology X.left T := by
  choose O hx hO using fun x =>
    exists_zero_neighborhood_of_genericModelGerm_eq_zero_of_integralAffineLocalZero
      hD P hP hG ((toSmoothSite X).obj T) s x
  have : IsNoetherian T.left :=
    inferInstanceAs (IsNoetherian ((toSmoothSite X).obj T).left)
  let (x : T.left) : IsAffine (O x).toScheme := (hO x).1
  let U (x : T.left) : FiniteEtaleSite X.left :=
    MorphismProperty.Over.mk ⊤ ((O x).ι ≫ T.hom)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let f (x : T.left) : U x ⟶ T := MorphismProperty.Over.homMk (O x).ι rfl
  let (x : T.left) : IsOpenImmersion (f x).left :=
    inferInstanceAs (IsOpenImmersion (O x).ι)
  apply Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun _ => inferInstance, fun x => ⟨x, ⟨x, hx x⟩, rfl, inferInstance⟩⟩
  · rw [Presieve.ofArrows_le_iff]
    intro x
    let A := SmoothSite.mk ((O x).ι ≫ (T.hom ≫ X.hom))
    let a : A ⟶ (toSmoothSite X).obj T := SmoothSite.homMk (O x).ι rfl
    let e : (toSmoothSite X).obj (U x) ⟶ A :=
      SmoothSite.homMk (𝟙 _) (by simp [A, U, toSmoothSite, Category.assoc])
    have he : e ≫ a = (toSmoothSite X).map (f x) := by
      apply MorphismProperty.Over.Hom.ext
      exact Category.id_comp _
    change P.transfer ((Cor.graphFunctor k).map ((toSmoothSite X).map (f x))) s =
      P.transfer ((Cor.graphFunctor k).map ((toSmoothSite X).map (f x))) 0
    rw [map_zero, ← he, Functor.map_comp, PresheafWithTransfers.transfer_comp]
    have hz : P.transfer ((Cor.graphFunctor k).map a) s = 0 := (hO x).2
    rw [ConcreteCategory.comp_apply, hz, map_zero]

/-- The literal small-site sheafification of the restricted original HI presheaf
is zero. This is a separate local-cover proof, not a sheafification comparison. -/
theorem isZero_sheafify_of_genericModelGerm_eq_zero_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
      (s : PresheafWithTransfers.genericModelGerm.{0, u} P T), s = 0)
    (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}).obj
      ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj P)) :=
  Presheaf.isZero_sheafify_of_locally_zero _ _
    (zeroSieve_mem_of_genericModelGerm_eq_zero_of_integralAffineLocalZero hD P hP hG X)

end Motivic.FiniteEtaleSite

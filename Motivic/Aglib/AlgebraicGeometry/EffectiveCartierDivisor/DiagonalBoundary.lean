/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Diagonal
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism

/-! # Actual Cartesian boundary graph of an étale neighborhood -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The image of the original ideal inclusion is exactly the original closed ideal. -/
theorem imageIdealData_idealInclusion {D X : Scheme.{u}} (i : D ⟶ X) [QuasiCompact i]
    [(idealModule i).IsQuasicoherent] :
    Hom.imageIdealData (idealInclusion i) = i.ker := by
  ext U x
  rw [Hom.imageIdealData_eq _ (Hom.imageIdealLocalizes_of_isQuasicoherent _) U]
  rw [i.ker_apply U]
  constructor
  · rintro ⟨m, rfl⟩
    exact congrArg (fun v ↦ v.val.app (op U.val) m) (idealInclusion_structureMap i)
  · intro hx
    refine ⟨(idealSectionsEquiv i U.val).symm ⟨x, hx⟩, ?_⟩
    exact (idealSectionsEquiv_val i U.val _).symm.trans
      (congrArg Subtype.val ((idealSectionsEquiv i U.val).apply_symm_apply ⟨x, hx⟩))

/-- A monic equation factoring through a closed ideal is its actual ideal
isomorphism when the affine section images are that ideal. -/
theorem idealFactor_isIso {D X : Scheme.{u}} {M : X.Modules}
    (i : D ⟶ X) (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ]
    (v : M ⟶ idealModule i) (hv : v ≫ idealInclusion i = φ)
    (hk : ∀ U : X.affineOpens, RingHom.ker (i.app U.val).hom =
      Hom.sectionImageIdeal φ U.val) : IsIso v := by
  have hb (U : X.affineOpens) : IsIso (v.app U.val) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro m n hmn
      have he := congrArg ((idealInclusion i).app U.val) hmn
      have hf (m : Γ(M,U.val)) :
          (idealInclusion i).app U.val (v.app U.val m) =
            φ.app U.val m :=
        congrArg (fun ψ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦
          ψ.app U.val m) hv
      have hm : φ.app U.val m = φ.app U.val n := (hf m).symm.trans (he.trans (hf n))
      let ev : X.Modules ⥤ ModuleCat Γ(X,U) := SheafOfModules.evaluation X.ringCatSheaf (op U.val)
      have : PreservesLimits ev := inferInstanceAs
        (PreservesLimits (SheafOfModules.evaluation X.ringCatSheaf (op U.val)))
      exact (ModuleCat.mono_iff_injective (ev.map φ)).mp inferInstance hm
    · intro a
      have ha := (idealSectionsEquiv i U.val a).property
      have ha' : ((idealSectionsEquiv i U.val a) : Γ(X,U)) ∈
          Hom.sectionImageIdeal φ U.val :=
        (congrArg (fun I : Ideal Γ(X,U) ↦
          ((idealSectionsEquiv i U.val a) : Γ(X,U)) ∈ I)
          (hk U)).mp ha
      obtain ⟨m, hm⟩ := ha'
      refine ⟨m, ?_⟩
      apply (idealSectionsEquiv i U.val).injective
      apply Subtype.ext
      rw [idealSectionsEquiv_val, idealSectionsEquiv_val]
      have hf := congrArg (fun ψ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦
        ψ.app U.val m) hv
      exact hf.trans (hm.trans (idealSectionsEquiv_val i U.val a))
  let ψ : (SheafOfModules.toSheaf X.ringCatSheaf).obj M ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (idealModule i) :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map v
  have : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : X.affineOpens ↦ U.val) (by simpa using X.isBasis_affineOpens) hb
  have : IsIso ((Scheme.Modules.toPresheaf X).map v) :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map ψ))
  exact isIso_of_reflects_iso v (Scheme.Modules.toPresheaf X)

/-- Flat ambient base change preserves the specified original ideal map.
This uses flatness of the actual base-change morphism, not flatness of the quotient. -/
theorem idealPullbackMap_isIso_of_flat_ambient {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (H : IsPullback a i' i b)
    [IsClosedImmersion i] [IsClosedImmersion i'] [Flat b]
    [(idealModule i).IsQuasicoherent] : IsIso (idealPullbackMap i i' b a h) := by
  let φ := Hom.pullbackToUnit (idealInclusion i) b
  have : Mono φ := by dsimp [φ, Hom.pullbackToUnit]; infer_instance
  have hk : i'.ker = i.ker.comap b := by
    rw [← H.flip.isoPullback_hom_fst]
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i b
  have hφ : Hom.imageIdealData φ = i'.ker := by
    rw [Hom.imageIdealData_pullbackToUnit_of_isQuasicoherent,
      imageIdealData_idealInclusion, hk]
  apply idealFactor_isIso i' φ (idealPullbackMap i i' b a h)
  · exact idealPullbackMap_inclusion i i' b a h
  · intro U
    rw [← i'.ker_apply U, ← hφ]
    exact Hom.imageIdealData_eq φ (Hom.imageIdealLocalizes_of_isQuasicoherent φ) U

variable {S X Y Z : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z)

/-- The original full-boundary graph in the source product. -/
def boundaryGraphSource : Z ⟶ pullback (p ≫ q) (z ≫ q) :=
  pullback.lift s (𝟙 Z) (by simp [← h])

/-- The coordinate graph in the base product. -/
def boundaryGraphTarget : Z ⟶ pullback q (z ≫ q) :=
  pullback.lift z (𝟙 Z) (by simp)

/-- The actual product map, without replacing the boundary by its reduction. -/
def boundaryProductMap : pullback (p ≫ q) (z ≫ q) ⟶ pullback q (z ≫ q) :=
  pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
    (by simpa only [Category.assoc] using pullback.condition (f := p ≫ q) (g := z ≫ q))

/-- The product map is the actual change of base of the original morphism. -/
theorem boundaryProductMap_isPullback :
    IsPullback (pullback.fst (p ≫ q) (z ≫ q)) (boundaryProductMap q p z)
      p (pullback.fst q (z ≫ q)) where
  w := by simp [boundaryProductMap]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t ↦ by
    have hc : t.fst ≫ (p ≫ q) = (t.snd ≫ pullback.snd q (z ≫ q)) ≫ (z ≫ q) := by
      rw [← Category.assoc, t.condition, Category.assoc, pullback.condition,
        ← Category.assoc]
    refine ⟨pullback.lift t.fst (t.snd ≫ pullback.snd q (z ≫ q)) hc,
      pullback.lift_fst _ _ _, ?_, ?_⟩
    · apply pullback.hom_ext
      · simpa [boundaryProductMap] using t.condition
      · simp [boundaryProductMap]
    · intro v hv hw
      apply pullback.hom_ext (f := p ≫ q) (g := z ≫ q)
      · simpa using hv
      · have he := congrArg (fun r ↦ r ≫ pullback.snd q (z ≫ q)) hw
        simpa [boundaryProductMap] using he)⟩

instance boundaryProductMap_flat [Flat p] : Flat (boundaryProductMap q p z) :=
  MorphismProperty.of_isPullback (boundaryProductMap_isPullback q p z) inferInstance

/-- A cover which is an isomorphism on the full boundary gives the literal
Cartesian square of boundary graphs. -/
theorem boundaryGraph_isPullback (H : IsPullback s (𝟙 Z) p z) :
    IsPullback (𝟙 Z) (boundaryGraphSource q p z s h)
      (boundaryGraphTarget q z) (boundaryProductMap q p z) where
  w := by
    apply pullback.hom_ext <;> simp [boundaryGraphSource, boundaryGraphTarget,
      boundaryProductMap, h]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t ↦ by
    have hc : (t.snd ≫ pullback.fst (p ≫ q) (z ≫ q)) ≫ p = t.fst ≫ z := by
      have ht := congrArg (fun v ↦ v ≫ pullback.fst q (z ≫ q)) t.condition
      simpa [boundaryGraphTarget, boundaryProductMap] using ht.symm
    have hy : t.fst ≫ s = t.snd ≫ pullback.fst (p ≫ q) (z ≫ q) := by
      have he := H.lift_snd (t.snd ≫ pullback.fst (p ≫ q) (z ≫ q)) t.fst hc
      simp only [Category.comp_id] at he
      rw [← he]
      exact H.lift_fst _ _ hc
    refine ⟨t.fst, by simp, ?_, ?_⟩
    · apply pullback.hom_ext
      · simpa [boundaryGraphSource] using hy
      · have ht := congrArg (fun v ↦ v ≫ pullback.snd q (z ≫ q)) t.condition
        simpa [boundaryGraphSource, boundaryGraphTarget, boundaryProductMap] using ht
    · intro v hv _
      simpa using hv)⟩

/-- The full boundary graph retains the specified ideal comparison under an
étale (indeed flat) neighborhood, with no reducedness assumption. -/
theorem boundaryGraph_idealPullbackMap_isIso (H : IsPullback s (𝟙 Z) p z)
    [Flat p] [IsClosedImmersion (boundaryGraphTarget q z)]
    [IsClosedImmersion (boundaryGraphSource q p z s h)]
    [(idealModule (boundaryGraphTarget q z)).IsQuasicoherent] :
    IsIso (idealPullbackMap (boundaryGraphTarget q z) (boundaryGraphSource q p z s h)
      (boundaryProductMap q p z) (𝟙 Z) (boundaryGraph_isPullback q p z s h H).w) :=
  idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _ (boundaryGraph_isPullback q p z s h H)

end AlgebraicGeometry.Scheme.Hom

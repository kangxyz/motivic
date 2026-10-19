/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.WeilRefinement
public import Motivic.Transfers.Presheaf.FiniteScalarEtaleCorrection
public import Motivic.Cohomology.A1.Boundary.Presheaf.FiniteSeparableDescent
public import Motivic.Cohomology.A1.Boundary.Presheaf.GeometricRefinement

/-! # Original boundary descent through a constructed affine Weil refinement

Actual extended affine correction witnesses remain explicit inputs. The common
original ambient, its direct puncture, both evaluations and correction bundles
are constructed; the conclusion concerns the original presheaf and base arrow.
This is not a finite-field correction producer or an unconditional Epi theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace Motivic.FiniteEtaleSite.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k L₁ L₂ A T : Type u} [Field k] [Field L₁] [Field L₂]
variable [Algebra k L₁] [Algebra k L₂]
variable [Module.Finite k L₁] [Module.Finite k L₂]
variable [Algebra.IsSeparable k L₁] [Algebra.IsSeparable k L₂]
variable [CommRing A] [CommRing T] [Algebra k A] [Algebra A T]
variable (X : SmoothSite (Spec (.of k))) (P : PresheafWithTransfers.{u + 1} k)
variable (V : EtaleSeparatedFiniteType X.left)
variable {W : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left}
variable (W₀ : SmoothSite (Spec (.of k)))


variable (q₀ : W₀ ⟶ SmoothSite.a1Cylinder (.of k) ((toSmoothSite X).obj V)) [Etale q₀.left]
variable (z₀ : ((toSmoothSite X).obj V) ⟶ W₀) (hz₀ : z₀ ≫ q₀ = SmoothSite.a1Section (.of k)
  ((toSmoothSite X).obj V) 0)
variable (e₀ : W₀ ⟶ (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W)
variable (he₀ : e₀.left ≫ W.hom = q₀.left ≫ ((cylinderNeighborhood X).obj V).hom)
variable (v : V ⟶ (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W)
variable (hv : z₀.left ≫ e₀.left =
  v.left ≫ pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left)
variable (e : Spec (.of A) ≅ W₀.left) (he : e.hom ≫ W₀.hom = Spec.algebraMap k A)
variable (d : Spec (.of T) ≅ V.left)
variable (hmark : d.hom ≫ z₀.left = Spec.algebraMap A T ≫ e.hom)


variable (φ₀ : (SmoothSite.etalePullback q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite
  X).obj V))) ⟶ ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj ((baseChange
  (SmoothSite.contractionOpen (.of k) X).left).obj W)))
variable (hφ₁ : φ₀.left ≫ pullback.fst W.hom
  (SmoothSite.contractionOpen (.of k) X).left = (SmoothSite.etalePullbackFst q₀
    (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))).left ≫ e₀.left)
variable (hφ₂ : φ₀.left ≫ pullback.snd W.hom
  (SmoothSite.contractionOpen (.of k) X).left = (SmoothSite.etalePullbackSnd q₀
    (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))).left ≫
    (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left)
variable (s : sections P (Cor.mk ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
  ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W))))

variable {E₁ : SmoothSite (Spec (.of L₁))} [IsAffine E₁.left]
variable (f₁ : E₁ ⟶ (SmoothSite.fieldBaseChange (algebraMap k L₁)).obj W₀) [Etale f₁.left]
variable (t₁ : (SmoothSite.fieldBaseChange (algebraMap k L₁)).obj ((toSmoothSite X).obj V) ⟶ E₁)
  (ht₁ : t₁ ≫ f₁ = (SmoothSite.fieldBaseChange (algebraMap k L₁)).map z₀)
variable (u₁ : sections (finiteSeparableExtension L₁ P)
  (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L₁)).obj (SmoothSite.torusCylinder (.of k)
    ((toSmoothSite X).obj V)))))
variable (c₁ : sections (finiteSeparableExtension L₁ P) (Cor.mk E₁))
variable (h₁ : transfer (finiteSeparableExtension L₁ P) ((Cor.graphFunctor L₁).map
      (SmoothSite.etalePullbackSnd f₁ ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₁)).map (SmoothSite.etalePullbackSnd q₀
        (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))))) u₁ -
    transfer (finiteSeparableExtension L₁ P) ((Cor.graphFunctor L₁).map
      (SmoothSite.etalePullbackFst f₁ ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))))) c₁ =
    transfer (finiteSeparableExtension L₁ P) ((Cor.graphFunctor L₁).map
      (SmoothSite.etalePullbackSnd f₁ ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₁)).map φ₀))
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L₁) ((toSmoothSite
          (SmoothSite.torusCylinder (.of k) X)).obj ((baseChange (SmoothSite.contractionOpen (.of
          k) X).left).obj W)))) s))

variable {E₂ : SmoothSite (Spec (.of L₂))} [IsAffine E₂.left]
variable (f₂ : E₂ ⟶ (SmoothSite.fieldBaseChange (algebraMap k L₂)).obj W₀) [Etale f₂.left]
variable (t₂ : (SmoothSite.fieldBaseChange (algebraMap k L₂)).obj ((toSmoothSite X).obj V) ⟶ E₂)
  (ht₂ : t₂ ≫ f₂ = (SmoothSite.fieldBaseChange (algebraMap k L₂)).map z₀)
variable (u₂ : sections (finiteSeparableExtension L₂ P)
  (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L₂)).obj (SmoothSite.torusCylinder (.of k)
    ((toSmoothSite X).obj V)))))
variable (c₂ : sections (finiteSeparableExtension L₂ P) (Cor.mk E₂))
variable (h₂ : transfer (finiteSeparableExtension L₂ P) ((Cor.graphFunctor L₂).map
      (SmoothSite.etalePullbackSnd f₂ ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₂)).map (SmoothSite.etalePullbackSnd q₀
        (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))))) u₂ -
    transfer (finiteSeparableExtension L₂ P) ((Cor.graphFunctor L₂).map
      (SmoothSite.etalePullbackFst f₂ ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))))) c₂ =
    transfer (finiteSeparableExtension L₂ P) ((Cor.graphFunctor L₂).map
      (SmoothSite.etalePullbackSnd f₂ ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map
        (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
        V)))) ≫ (SmoothSite.fieldBaseChange (algebraMap k L₂)).map φ₀))
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L₂) ((toSmoothSite
          (SmoothSite.torusCylinder (.of k) X)).obj ((baseChange (SmoothSite.contractionOpen (.of
          k) X).left).obj W)))) s))

include hz₀ he₀ hv e he d hmark hφ₁ hφ₂ ht₁ ht₂ h₁ h₂ in
/-- Two actual affine extended correction equations produce the canonical image
witness on the supplied original base arrow. The common refinement is constructed. -/
theorem imageSieve_of_affine_weil_corrections
    (hdegree : (Module.finrank k L₁).Coprime (Module.finrank k L₂)) :
    Presheaf.imageSieve (contractionToBoundary X P).hom
      ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
        (SmoothSite.contractionOpen (.of k) X)
        (SmoothSite.a1Section (.of k) X 0)).app (op W) s) v := by
  obtain ⟨Y, p, z, hz, hY, hp, a₁, a₂, ha₁, ha₂, _, _⟩ :=
    SmoothSite.exists_affine_etale_scalar_pair ((Module.finBasis k L₁).reindex
      (Equiv.ulift.{u}).symm)
      ((Module.finBasis k L₂).reindex (Equiv.ulift.{u}).symm) z₀ e he d hmark f₁ f₂ t₁ t₂ ht₁ ht₂
  let := hY
  let := hp
  let q := p ≫ q₀
  let : Etale q.left := inferInstanceAs (Etale (p.left ≫ q₀.left))
  let O := SmoothSite.etalePullback q (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))
  let αY := SmoothSite.etalePullbackFst q (SmoothSite.contractionOpen (.of k) ((toSmoothSite
    X).obj V))
  let β := SmoothSite.etalePullbackSnd q (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
    V))
  let γ := SmoothSite.etalePullbackRefinement p q₀ (SmoothSite.contractionOpen (.of k)
    ((toSmoothSite X).obj V))
  let ι := geometricRefinementIso X V Y q
  let α := αY ≫ ι.hom
  let p' := ι.inv ≫ p
  have hγα : γ ≫ (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k)
    ((toSmoothSite X).obj V))) = α ≫ p' := by
    simpa only [α, p', Category.assoc, Iso.hom_inv_id_assoc] using
      SmoothSite.etalePullbackRefinement_fst p q₀ (SmoothSite.contractionOpen (.of k)
        ((toSmoothSite X).obj V))
  have hγβ : γ ≫ (SmoothSite.etalePullbackSnd q₀ (SmoothSite.contractionOpen (.of k)
    ((toSmoothSite X).obj V))) = β := SmoothSite.etalePullbackRefinement_snd p q₀
    (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))
  have ha₁' : ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map ι.inv ≫ a₁) ≫ f₁ =
    (SmoothSite.fieldBaseChange (algebraMap k L₁)).map p' := by
    rw [Category.assoc, ha₁, ← Functor.map_comp]
  have ha₂' : ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map ι.inv ≫ a₂) ≫ f₂ =
    (SmoothSite.fieldBaseChange (algebraMap k L₂)).map p' := by
    rw [Category.assoc, ha₂, ← Functor.map_comp]
  let w₁ := FiniteSeparableRefinementCorrection.ofEtalePullback P α β γ
    (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)))
    (SmoothSite.etalePullbackSnd q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)))
    φ₀
    p' hγα hγβ f₁ ((SmoothSite.fieldBaseChange (algebraMap k L₁)).map ι.inv ≫ a₁) ha₁' s u₁ c₁ h₁
  let w₂ := FiniteSeparableRefinementCorrection.ofEtalePullback P α β γ
    (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)))
    (SmoothSite.etalePullbackSnd q₀ (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)))
    φ₀
    p' hγα hγβ f₂ ((SmoothSite.fieldBaseChange (algebraMap k L₂)).map ι.inv ≫ a₂) ha₂' s u₂ c₂ h₂
  have hq : z.left ≫ q.left = (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left := by
    have h : z ≫ q = SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0 := by
      dsimp [q]
      rw [← Category.assoc, hz, hz₀]
    exact congrArg (fun f => f.left) h
  have heY : (p ≫ e₀).left ≫ W.hom =
      q.left ≫ ((cylinderNeighborhood X).obj V).hom := by
    change (p.left ≫ e₀.left) ≫ W.hom =
      (p.left ≫ q₀.left) ≫ ((cylinderNeighborhood X).obj V).hom
    rw [Category.assoc, he₀, Category.assoc]
  let b := geometricRefinementToCylinder X V Y q
  let f := geometricRefinementToOriginal X V Y q (p ≫ e₀) heY
  have hα : α.left = αY.left := by
    change αY.left ≫ 𝟙 Y.left = αY.left
    exact Category.comp_id _
  have H : IsPullback β.left α.left (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj
    V)).left b.left := by
    rw [hα]
    exact (IsPullback.of_hasPullback q.left (SmoothSite.contractionOpen (.of k) ((toSmoothSite
      X).obj V)).left).flip
  have hφ₁' : (γ ≫ φ₀).left ≫ pullback.fst W.hom
      (SmoothSite.contractionOpen (.of k) X).left = α.left ≫ f.left := by
    have hγ : γ.left ≫ (SmoothSite.etalePullbackFst q₀ (SmoothSite.contractionOpen (.of k)
      ((toSmoothSite X).obj V))).left = αY.left ≫ p.left :=
      congrArg (fun f => f.left) (SmoothSite.etalePullbackRefinement_fst p q₀
        (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)))
    change (γ.left ≫ φ₀.left) ≫ _ = α.left ≫ (p.left ≫ e₀.left)
    rw [Category.assoc, hφ₁, ← Category.assoc, hγ, Category.assoc, hα]
  have hφ₂' : (γ ≫ φ₀).left ≫ pullback.snd W.hom
      (SmoothSite.contractionOpen (.of k) X).left = β.left ≫
        (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left := by
    have hγ : γ.left ≫ (SmoothSite.etalePullbackSnd q₀ (SmoothSite.contractionOpen (.of k)
      ((toSmoothSite X).obj V))).left = β.left := congrArg (fun f => f.left) hγβ
    change (γ.left ≫ φ₀.left) ≫ _ = _
    rw [Category.assoc, hφ₂, ← Category.assoc, hγ]
  have hi := imageSieve_of_coprime_finiteSeparable_refinements X P V b z.left hq
    O α β H f (γ ≫ φ₀) hφ₁' hφ₂' s w₁ w₂ hdegree
  have hze : z.left ≫ (p ≫ e₀).left =
      v.left ≫ pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left := by
    have hzp : z.left ≫ p.left = z₀.left := congrArg (fun f => f.left) hz
    change z.left ≫ (p.left ≫ e₀.left) = _
    rw [← Category.assoc, hzp, hv]
  have hv' := geometricRefinement_zero_arrow X V Y q (p ≫ e₀) heY z.left hq v hze
  rw [hv'] at hi
  exact hi

end Motivic.FiniteEtaleSite.OriginalPresheaf

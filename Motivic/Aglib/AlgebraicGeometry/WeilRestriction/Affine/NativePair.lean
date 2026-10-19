/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.ScalarChart
public import Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.ActualPair

/-!
# Constructed common refinements of original native scalar witnesses

The common original ambient, both native scalar evaluations, and the entire
original marked scheme are retained. Only original affine charts are supplied;
the scalar charts and both actual witness coordinate rings are constructed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Module

universe u

namespace AlgebraicGeometry.AffineWeilRestriction

section Transport

variable {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
variable [Algebra R A] [Algebra R B] [Algebra A T]
variable {W V Y : Scheme.{u}}
variable (w : W ⟶ Spec (.of R)) (e : Spec (.of A) ≅ W)
variable (he : e.hom ≫ w = Spec.algebraMap R A)
variable (v : V ⟶ Spec (.of R)) (d : Spec (.of T) ≅ V)
variable (hd : d.hom ≫ v = Spec.algebraMap A T ≫ Spec.algebraMap R A)
variable (p : Y ⟶ Spec (.of A)) (z : Spec (.of T) ⟶ Y)
variable (hz : z ≫ p = Spec.algebraMap A T)
variable (zV : V ⟶ Y) (hdz : d.hom ≫ zV = z)
variable (hv : v = zV ≫ ((p ≫ e.hom) ≫ w))

include hdz in
private theorem nativeMark_chart :
    (relativeAffineScalarChart R A B v d hd).hom ≫
      pullback.map v (Spec.algebraMap R B) ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B)
        zV (𝟙 _) (𝟙 _) (by simpa using hv) (by simp) ≫
      (affineScalarChartPullbackIso R A B w e he p).hom =
    pullback.map (Spec.algebraMap A T) (Spec.algebraMap A (A ⊗[R] B))
      p (Spec.algebraMap A (A ⊗[R] B)) z (𝟙 _) (𝟙 _)
      (by simpa using hz.symm) (by simp) := by
  have hfst : ((relativeAffineScalarChart R A B v d hd).hom ≫
      pullback.map v (Spec.algebraMap R B) ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B)
        zV (𝟙 _) (𝟙 _) (by simpa using hv) (by simp) ≫
      (affineScalarChartPullbackIso R A B w e he p).hom) ≫
        pullback.fst p (Spec.algebraMap A (A ⊗[R] B)) =
      (pullback.map (Spec.algebraMap A T) (Spec.algebraMap A (A ⊗[R] B))
        p (Spec.algebraMap A (A ⊗[R] B)) z (𝟙 _) (𝟙 _)
        (by simpa using hz.symm) (by simp)) ≫
          pullback.fst p (Spec.algebraMap A (A ⊗[R] B)) := by
    simp only [Category.assoc, affineScalarChartPullbackIso_hom_fst,
      pullback.map, pullback.lift_fst, relativeAffineScalarChart_hom_fst_assoc, hdz]
  apply pullback.hom_ext hfst
  apply (cancel_mono (pullbackSpecIso R A B).inv).mp
  simp only [Category.assoc]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst']
    simpa only [Category.assoc, pullback.condition] using congrArg (fun h => h ≫ p) hfst
  · simp only [Category.assoc, pullbackSpecIso_inv_snd]
    rw [affineScalarChartPullbackIso_hom_scalar R A B w e he p]
    simp only [pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
      relativeAffineScalarChart_hom_snd]

include hdz in
private theorem nativeEvaluation_of_relative
    {E : Scheme.{u}} (f : E ⟶ pullback w (Spec.algebraMap R B))
    (t : pullback v (Spec.algebraMap R B) ⟶ E)
    (a : pullback p (Spec.algebraMap A (A ⊗[R] B)) ⟶ E)
    (ha : a ≫ (f ≫ (affineScalarChart R A B w e he).inv) =
      pullback.snd p (Spec.algebraMap A (A ⊗[R] B)))
    (ht : pullback.map (Spec.algebraMap A T) (Spec.algebraMap A (A ⊗[R] B))
      p (Spec.algebraMap A (A ⊗[R] B)) z (𝟙 _) (𝟙 _)
      (by simpa using hz.symm) (by simp) ≫ a =
        (relativeAffineScalarChart R A B v d hd).hom ≫ t) :
    ∃ aN : pullback ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B) ⟶ E,
      aN ≫ f = pullback.map ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B)
        w (Spec.algebraMap R B) (p ≫ e.hom) (𝟙 _) (𝟙 _) (by simp) (by simp) ∧
      pullback.map v (Spec.algebraMap R B) ((p ≫ e.hom) ≫ w) (Spec.algebraMap R B)
        zV (𝟙 _) (𝟙 _) (by simpa using hv) (by simp) ≫ aN = t := by
  refine ⟨(affineScalarChartPullbackIso R A B w e he p).hom ≫ a, ?_, ?_⟩
  · have ha' : a ≫ f = pullback.snd p (Spec.algebraMap A (A ⊗[R] B)) ≫
        (affineScalarChart R A B w e he).hom := by
      apply (cancel_mono (affineScalarChart R A B w e he).inv).mp
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ha
    simp only [Category.assoc, ha']
    exact affineScalarChartPullbackIso_ambient R A B w e he p
  · apply (cancel_epi (relativeAffineScalarChart R A B v d hd).hom).mp
    simpa only [Category.assoc] using
      (congrArg (fun h => h ≫ a)
        (nativeMark_chart (B := B) w e he v d hd p z hz zV hdz hv)).trans ht

end Transport

section Pair

variable {R A L₁ L₂ T : Type u}
variable [CommRing R] [CommRing A] [CommRing L₁] [CommRing L₂] [CommRing T]
variable [Algebra R A] [Algebra R L₁] [Algebra R L₂] [Algebra A T]
variable {κ₁ κ₂ : Type u} [Finite κ₁] [Finite κ₂]
variable (b₁ : Basis κ₁ R L₁) (b₂ : Basis κ₂ R L₂)
variable {W V E₁ E₂ : Scheme.{u}} [IsAffine E₁] [IsAffine E₂]
variable (w : W ⟶ Spec (.of R)) (v : V ⟶ Spec (.of R))
variable (z₀ : V ⟶ W) (hz₀ : v = z₀ ≫ w)
variable (e : Spec (.of A) ≅ W) (he : e.hom ≫ w = Spec.algebraMap R A)
variable (d : Spec (.of T) ≅ V) (hmark : d.hom ≫ z₀ = Spec.algebraMap A T ≫ e.hom)
variable (f₁ : E₁ ⟶ pullback w (Spec.algebraMap R L₁))
variable (f₂ : E₂ ⟶ pullback w (Spec.algebraMap R L₂)) [Etale f₁] [Etale f₂]
variable (t₁ : pullback v (Spec.algebraMap R L₁) ⟶ E₁)
variable (t₂ : pullback v (Spec.algebraMap R L₂) ⟶ E₂)
variable (ht₁ : t₁ ≫ f₁ = pullback.map v (Spec.algebraMap R L₁)
  w (Spec.algebraMap R L₁) z₀ (𝟙 _) (𝟙 _) (by simpa using hz₀) (by simp))
variable (ht₂ : t₂ ≫ f₂ = pullback.map v (Spec.algebraMap R L₂)
  w (Spec.algebraMap R L₂) z₀ (𝟙 _) (𝟙 _) (by simpa using hz₀) (by simp))

include b₁ b₂ e he d hmark ht₁ ht₂ in
/-- Two actual affine étale native scalar witnesses produce one original affine
étale refinement, with both original native scalar evaluations and whole marks. -/
theorem exists_native_affine_etale_pair :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ W) (z : V ⟶ Y) (hz : z ≫ p = z₀),
      IsAffine Y ∧ Etale p ∧
      ∃ (a₁ : pullback (p ≫ w) (Spec.algebraMap R L₁) ⟶ E₁)
        (a₂ : pullback (p ≫ w) (Spec.algebraMap R L₂) ⟶ E₂),
        a₁ ≫ f₁ = pullback.map (p ≫ w) (Spec.algebraMap R L₁)
          w (Spec.algebraMap R L₁) p (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) ∧
        a₂ ≫ f₂ = pullback.map (p ≫ w) (Spec.algebraMap R L₂)
          w (Spec.algebraMap R L₂) p (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) ∧
        pullback.map v (Spec.algebraMap R L₁) (p ≫ w) (Spec.algebraMap R L₁)
          z (𝟙 _) (𝟙 _) ((Category.comp_id v).trans (hz₀.trans
            ((congrArg (fun h => h ≫ w) hz).symm.trans (Category.assoc z p w))))
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ a₁ = t₁ ∧
        pullback.map v (Spec.algebraMap R L₂) (p ≫ w) (Spec.algebraMap R L₂)
          z (𝟙 _) (𝟙 _) ((Category.comp_id v).trans (hz₀.trans
            ((congrArg (fun h => h ≫ w) hz).symm.trans (Category.assoc z p w))))
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ a₂ = t₂ := by
  have hd : d.hom ≫ v = Spec.algebraMap A T ≫ Spec.algebraMap R A := by
    rw [hz₀, ← Category.assoc, hmark, Category.assoc, he]
  let c₁ := affineScalarChart R A L₁ w e he
  let c₂ := affineScalarChart R A L₂ w e he
  let m₁ := relativeAffineScalarChart R A L₁ v d hd
  let m₂ := relativeAffineScalarChart R A L₂ v d hd
  have h₁ : (m₁.hom ≫ t₁) ≫ (f₁ ≫ c₁.inv) = pullback.snd _ _ := by
    rw [Category.assoc, ← Category.assoc t₁, ht₁, ← Category.assoc,
      relativeAffineScalarChart_ambient R A L₁ w e he v d hd z₀ hz₀ hmark]
    simp only [c₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₂ : (m₂.hom ≫ t₂) ≫ (f₂ ≫ c₂.inv) = pullback.snd _ _ := by
    rw [Category.assoc, ← Category.assoc t₂, ht₂, ← Category.assoc,
      relativeAffineScalarChart_ambient R A L₂ w e he v d hd z₀ hz₀ hmark]
    simp only [c₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨Y, p, z, hz, hY, hp, a₁, a₂, ha₁, ha₂, hm₁, hm₂⟩ :=
    exists_affine_etale_pair_of_scalar_sections (b₁.baseChange A) (b₂.baseChange A)
      (f₁ ≫ c₁.inv) (f₂ ≫ c₂.inv) (m₁.hom ≫ t₁) (m₂.hom ≫ t₂) h₁ h₂
  let := hY
  let := hp
  have hzV : (d.inv ≫ z) ≫ (p ≫ e.hom) = z₀ := by
    rw [Category.assoc, ← Category.assoc z, hz, ← hmark, Iso.inv_hom_id_assoc]
  have hv : v = (d.inv ≫ z) ≫ ((p ≫ e.hom) ≫ w) := by
    rw [← Category.assoc, hzV, ← hz₀]
  have hdz : d.hom ≫ (d.inv ≫ z) = z := d.hom_inv_id_assoc z
  obtain ⟨aN₁, hN₁, hmN₁⟩ :=
    nativeEvaluation_of_relative w e he v d hd p z hz (d.inv ≫ z) hdz hv f₁ t₁ a₁ ha₁ hm₁
  obtain ⟨aN₂, hN₂, hmN₂⟩ :=
    nativeEvaluation_of_relative w e he v d hd p z hz (d.inv ≫ z) hdz hv f₂ t₂ a₂ ha₂ hm₂
  exact ⟨Y, p ≫ e.hom, d.inv ≫ z, hzV, inferInstance, inferInstance,
    aN₁, aN₂, hN₁, hN₂, hmN₁, hmN₂⟩

end Pair

end AlgebraicGeometry.AffineWeilRestriction

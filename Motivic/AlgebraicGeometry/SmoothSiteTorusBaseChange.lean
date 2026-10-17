/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteTorus
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteBaseChangeProducts
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Units
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Cartesian coefficient change for the torus and its powers

Arbitrary ring maps give the literal Laurent coefficient pullback square.
The smooth-site comparison retains the scalar projection, Laurent coordinate,
and evaluation-at-one section. All powers use the actual recursive products.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.SmoothSite

variable {R S : CommRingCat.{u}}

/-- The actual Laurent coefficient square is Cartesian for any ring map. -/
theorem torus_isPullback (c : R ⟶ S) :
    IsPullback (Spec.map (laurentMap c)) (laurentProjection S)
      (laurentProjection R) (Spec.map c) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (laurent_isPushout c)).flip

/-- The Laurent torus commutes with arbitrary base change. -/
def torusBaseChangeIso (c : R ⟶ S) :
    (baseChange (Spec.map c)).obj (torus R) ≅ torus S :=
  (MorphismProperty.Over.isoMk (torus_isPullback c).isoPullback
    (torus_isPullback c).isoPullback_hom_snd).symm

/-- The inverse comparison retains the literal coefficient map. -/
@[reassoc (attr := simp)]
theorem torusBaseChangeIso_inv_fst (c : R ⟶ S) :
    (torusBaseChangeIso c).inv.left ≫ pullback.fst (laurentProjection R) (Spec.map c) =
      Spec.map (laurentMap c) :=
  (torus_isPullback c).isoPullback_hom_fst

/-- The inverse comparison retains the new scalar projection. -/
@[reassoc (attr := simp)]
theorem torusBaseChangeIso_inv_snd (c : R ⟶ S) :
    (torusBaseChangeIso c).inv.left ≫ pullback.snd (laurentProjection R) (Spec.map c) =
      laurentProjection S :=
  (torus_isPullback c).isoPullback_hom_snd

/-- The forward comparison retains the literal coefficient map. -/
@[reassoc (attr := simp)]
theorem torusBaseChangeIso_hom_coefficientMap (c : R ⟶ S) :
    (torusBaseChangeIso c).hom.left ≫ Spec.map (laurentMap c) =
      pullback.fst (laurentProjection R) (Spec.map c) :=
  (torus_isPullback c).isoPullback_inv_fst

/-- The forward comparison retains the exact scalar projection. -/
@[reassoc (attr := simp)]
theorem torusBaseChangeIso_hom_projection (c : R ⟶ S) :
    (torusBaseChangeIso c).hom.left ≫ laurentProjection S =
      pullback.snd (laurentProjection R) (Spec.map c) :=
  (torus_isPullback c).isoPullback_inv_snd

/-- Laurent evaluation at one commutes with every coefficient homomorphism. -/
theorem laurentEvalOne_coefficient (c : R ⟶ S) :
    laurentMap c ≫ CommRingCat.ofHom (laurentEvalOne S) =
      CommRingCat.ofHom (laurentEvalOne R) ≫ c := by
  apply CommRingCat.hom_ext
  apply laurent_hom_ext
  · intro r
    change laurentEvalOne S (laurentMap c (LaurentPolynomial.C r)) =
      c (laurentEvalOne R (LaurentPolynomial.C r))
    exact (congrArg (laurentEvalOne S) (laurentMap_C c r)).trans
      ((laurentEvalOne_C S (c r)).trans (congrArg c (laurentEvalOne_C R r)).symm)
  · change laurentEvalOne S (laurentMap c (LaurentPolynomial.T 1)) =
      c (laurentEvalOne R (LaurentPolynomial.T 1))
    exact (congrArg (laurentEvalOne S) (laurentMap_T c 1)).trans
      ((laurentEvalOne_T S 1).trans
        ((congrArg c (laurentEvalOne_T R 1)).trans (map_one c.hom)).symm)

/-- The literal identity section commutes with arbitrary coefficient change. -/
@[reassoc]
theorem laurentOneSection_coefficient (c : R ⟶ S) :
    laurentOneSection S ≫ Spec.map (laurentMap c) =
      Spec.map c ≫ laurentOneSection R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp, laurentEvalOne_coefficient]

/-- The forward comparison retains the genuine Laurent coordinate unit. -/
theorem torusBaseChangeIso_globalUnit (c : R ⟶ S) :
    Units.map (torusBaseChangeIso c).hom.left.appTop.hom.toMonoidHom
      (laurentGlobalUnit S) =
        Units.map (pullback.fst (laurentProjection R) (Spec.map c)).appTop.hom.toMonoidHom
          (laurentGlobalUnit R) := by
  have hc := laurentGlobalUnit_coefficient c
  apply Units.ext
  have h := congrArg (fun f => f.appTop (↑(laurentGlobalUnit R)))
    (torusBaseChangeIso_hom_coefficientMap c)
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  have hu := congrArg Units.val hc
  change (Spec.map (laurentMap c)).appTop (↑(laurentGlobalUnit R)) =
    ↑(laurentGlobalUnit S) at hu
  exact (congrArg (torusBaseChangeIso c).hom.left.appTop hu.symm).trans h

/-- Base change carries the actual identity section to the new identity section. -/
@[reassoc]
theorem torusBaseChangeIso_one (c : R ⟶ S) :
    (baseChange (Spec.map c)).map (torusOne R) ≫ (torusBaseChangeIso c).hom =
      (baseChangeBaseIso (Spec.map c)).hom ≫ torusOne S := by
  apply (cancel_mono (torusBaseChangeIso c).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · calc
      _ = pullback.fst (𝟙 (Spec R)) (Spec.map c) ≫ laurentOneSection R :=
        baseChange_map_fst _ (torusOne R)
      _ = (pullback.snd (𝟙 (Spec R)) (Spec.map c) ≫ Spec.map c) ≫
          laurentOneSection R :=
        congrArg (fun f => f ≫ laurentOneSection R)
          ((Category.comp_id _).symm.trans
            (pullback.condition (f := 𝟙 (Spec R)) (g := Spec.map c)))
      _ = pullback.snd (𝟙 (Spec R)) (Spec.map c) ≫
          laurentOneSection S ≫ Spec.map (laurentMap c) :=
        (Category.assoc _ _ _).trans (congrArg
          (fun f => pullback.snd (𝟙 (Spec R)) (Spec.map c) ≫ f)
            (laurentOneSection_coefficient c).symm)
      _ = _ := Eq.symm ((Category.assoc _ _ _).trans
        (congrArg (fun f => pullback.snd (𝟙 (Spec R)) (Spec.map c) ≫ f)
          ((Category.assoc _ _ _).trans
            (congrArg (fun f => laurentOneSection S ≫ f) (torusBaseChangeIso_inv_fst c)))))
  · exact (MorphismProperty.Over.w ((baseChange (Spec.map c)).map (torusOne R))).trans
      (MorphismProperty.Over.w
        ((baseChangeBaseIso (Spec.map c)).hom ≫ torusOne S ≫
          (torusBaseChangeIso c).inv)).symm

/-- Every torus power is compared by the actual recursive relative products. -/
def torusPowerBaseChangeIso (c : R ⟶ S) : (q : ℕ) →
    (baseChange (Spec.map c)).obj (torusPower R q) ≅ torusPower S q
  | 0 => baseChangeBaseIso (Spec.map c)
  | q + 1 => baseChangeProductIso (Spec.map c) (torus R) (torusPower R q) ≪≫
      productIso (torusBaseChangeIso c) (torusPowerBaseChangeIso c q)

/-- Every original torus coordinate is retained under the power comparison. -/
@[reassoc (attr := simp)]
theorem torusPowerBaseChangeIso_coordinate (c : R ⟶ S) (q : ℕ) (i : Fin q) :
    (torusPowerBaseChangeIso c q).hom ≫ torusCoordinate S q i =
      (baseChange (Spec.map c)).map (torusCoordinate R q i) ≫ (torusBaseChangeIso c).hom := by
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [torusPowerBaseChangeIso, productIso_hom, torusCoordinate_zero]
    · simp [torusPowerBaseChangeIso, productIso_hom, torusCoordinate_succ,
        Category.assoc, ih, Functor.map_comp]

/-- The zero-coordinate projection remains the actual scalar structure map. -/
@[reassoc (attr := simp)]
theorem torusPowerBaseChangeIso_toBase (c : R ⟶ S) (q : ℕ) :
    (torusPowerBaseChangeIso c q).hom ≫ torusPowerToBase S q =
      (baseChange (Spec.map c)).map (torusPowerToBase R q) ≫
        (baseChangeBaseIso (Spec.map c)).hom := by
  apply torusPower_hom_ext S 0
  intro i
  exact Fin.elim0 i

/-- Base change preserves insertion of the identity in every coordinate. -/
@[reassoc]
theorem torusPowerBaseChangeIso_insertOne (c : R ⟶ S) (q : ℕ) (i : Fin (q + 1)) :
    (baseChange (Spec.map c)).map (torusInsertOne R q i) ≫
        (torusPowerBaseChangeIso c (q + 1)).hom =
      (torusPowerBaseChangeIso c q).hom ≫ torusInsertOne S q i := by
  apply torusPower_hom_ext
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp only [Category.assoc, torusPowerBaseChangeIso_coordinate,
      torusInsertOne_coordinate_self, ← Functor.map_comp_assoc,
      torusInsertOne_coordinate_self, Functor.map_comp, Category.assoc,
      torusBaseChangeIso_one, torusPowerBaseChangeIso_toBase_assoc]
  · simp only [Category.assoc, torusPowerBaseChangeIso_coordinate,
      torusInsertOne_coordinate_succAbove, ← Functor.map_comp_assoc,
      torusInsertOne_coordinate_succAbove]

/-- Base change preserves deletion of every torus coordinate as well. -/
@[reassoc]
theorem torusPowerBaseChangeIso_deleteCoordinate (c : R ⟶ S) (q : ℕ)
    (i : Fin (q + 1)) :
    (baseChange (Spec.map c)).map (torusDeleteCoordinate R q i) ≫
        (torusPowerBaseChangeIso c q).hom =
      (torusPowerBaseChangeIso c (q + 1)).hom ≫ torusDeleteCoordinate S q i := by
  apply torusPower_hom_ext
  intro j
  simp only [Category.assoc, torusPowerBaseChangeIso_coordinate,
    torusDeleteCoordinate_coordinate, ← Functor.map_comp_assoc,
    torusDeleteCoordinate_coordinate]

/-- Arbitrary field maps use the same Laurent comparison. -/
def torusFieldBaseChangeIso {K L : Type u} [Field K] [Field L] (c : K →+* L) :
    (fieldBaseChange c).obj (torus (CommRingCat.of K)) ≅ torus (CommRingCat.of L) :=
  torusBaseChangeIso (CommRingCat.ofHom c)

/-- Arbitrary field maps compare all actual torus powers over the new field. -/
def torusPowerFieldBaseChangeIso {K L : Type u} [Field K] [Field L] (c : K →+* L) (q : ℕ) :
    (fieldBaseChange c).obj (torusPower (CommRingCat.of K) q) ≅
      torusPower (CommRingCat.of L) q :=
  torusPowerBaseChangeIso (CommRingCat.ofHom c) q

end Motivic.SmoothSite

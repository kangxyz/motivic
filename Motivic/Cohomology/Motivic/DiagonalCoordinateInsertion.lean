/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCycleSymbols
public import Motivic.Cohomology.Motivic.WeightTwoSteinbergBound

/-!
# Fixed-coordinate insertion on actual reduced-torus homology

Maps of the original transfer presheaves preserve the actual singular boundary
and descend through the proved `C₀ / im(d₁)` comparison. Inserting two varying
coordinates among fixed units respects every original identity axis. Applying
this map to the proved weight-two Steinberg class gives the all-position
Steinberg relation in the actual diagonal group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.DiagonalCoordinateInsertion

open PresheafWithTransfers DiagonalTopDegree DiagonalCycleSymbols WeightOneBoundaryNorm

variable (k : Type u) [Field k]

/-- Any map of the actual reduced transfer presheaves preserves the two-face boundary. -/
theorem coefficientMap_boundary {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n)
    (x : chains k m 1) :
    η.hom.app (op (Cor.simplexProduct (point k) 0)) (boundary k m x) =
      boundary k n (η.hom.app (op (Cor.simplexProduct (point k) 1)) x) := by
  have h := congrArg (fun f => f.hom.app (op (point k)))
    ((singularComplexMap η).comm 1 0)
  exact (ConcreteCategory.congr_hom h x).symm

/-- The map on literal zero-cycle quotients induced by an actual coefficient map. -/
def quotientMap {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n) :
    zeroHomology k m →+ zeroHomology k n :=
  QuotientAddGroup.map (boundary k m).range (boundary k n).range
    (η.hom.app (op (Cor.simplexProduct (point k) 0))).hom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨η.hom.app (op (Cor.simplexProduct (point k) 1)) x,
        (coefficientMap_boundary k η x).symm⟩)

/-- Fixed-coordinate coefficient maps act on the original raw diagonal homology. -/
def rawMap {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n) :
    (motivicRawBaseComplex k m).homology m →+
      (motivicRawBaseComplex k n).homology n :=
  (quotientToRawEquiv k n).toAddMonoidHom.comp
    ((quotientMap k η).comp (quotientToRawEquiv k m).symm.toAddMonoidHom)

/-- The original zero-cycle representative is retained by the descended map. -/
theorem rawMap_singularClass {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n)
    (x : chains k m 0) :
    rawMap k η (singularClass k m x) =
      singularClass k n (η.hom.app (op (Cor.simplexProduct (point k) 0)) x) := by
  rw [← quotientToRawEquiv_mk]
  change quotientToRawEquiv k n (quotientMap k η
    ((quotientToRawEquiv k m).symm (quotientToRawEquiv k m _))) = _
  rw [AddEquiv.symm_apply_apply]
  exact quotientToRawEquiv_mk k n _

/-- A morphism with one identity coordinate factors through the original identity axis. -/
theorem factor_axis {X : SmoothSite (Spec (.of k))} (q : ℕ)
    (φ : X ⟶ SmoothSite.torusPower (.of k) (q + 1)) (i : Fin (q + 1))
    (hi : φ ≫ SmoothSite.torusCoordinate (.of k) (q + 1) i =
      φ ≫ SmoothSite.torusPowerToBase (.of k) (q + 1) ≫ SmoothSite.torusOne (.of k)) :
    φ = (φ ≫ SmoothSite.torusDeleteCoordinate (.of k) q i) ≫
      SmoothSite.torusInsertOne (.of k) q i := by
  apply SmoothSite.torusPower_hom_ext
  intro j
  obtain hji | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · subst j
    rw [Category.assoc, SmoothSite.torusInsertOne_coordinate_self, hi]
    have hb : φ ≫ SmoothSite.torusPowerToBase (.of k) (q + 1) =
        (φ ≫ SmoothSite.torusDeleteCoordinate (.of k) q i) ≫
          SmoothSite.torusPowerToBase (.of k) q := by
      apply SmoothSite.torusPower_hom_ext (.of k) 0
      intro t
      exact Fin.elim0 t
    exact congrArg (fun f => f ≫ SmoothSite.torusOne (.of k)) hb
  · simp only [Category.assoc, SmoothSite.torusInsertOne_coordinate_succAbove,
      SmoothSite.torusDeleteCoordinate_coordinate]

/-- The literal map with two specified varying positions and all other entries fixed. -/
def varyingPair (q : ℕ) (a : Fin q → kˣ) (i j : Fin q) :
    SmoothSite.torusPower (.of k) 2 ⟶ SmoothSite.torusPower (.of k) q :=
  SmoothSite.torusPowerLift (.of k) q (fun t => if t = i then
    SmoothSite.torusCoordinate (.of k) 2 0 else if t = j then
      SmoothSite.torusCoordinate (.of k) 2 1 else
        SmoothSite.torusPowerToBase (.of k) 2 ≫ WeightOnePointNorm.rationalTorusPoint k (a t))

/-- Inserting the tuple's original pair recovers its actual rational graph. -/
@[reassoc]
theorem rationalPair_varyingPair (q : ℕ) (a : Fin q → kˣ) (i j : Fin q) :
    WeightTwoSymbols.rationalPair k (a i) (a j) ≫ varyingPair k q a i j =
      rationalTuple k q a := by
  apply SmoothSite.torusPower_hom_ext
  intro t
  rw [Category.assoc, varyingPair, rationalTuple,
    SmoothSite.torusPowerLift_coordinate, SmoothSite.torusPowerLift_coordinate]
  by_cases hti : t = i
  · subst t
    simp only [ite_true, WeightTwoSymbols.rationalPair, SmoothSite.torusPowerLift_coordinate]
    rfl
  · by_cases htj : t = j
    · subst t
      simp only [hti, ite_false, ite_true, WeightTwoSymbols.rationalPair,
        SmoothSite.torusPowerLift_coordinate]
      rfl
    · simp only [hti, htj, ite_false]
      have hb : WeightTwoSymbols.rationalPair k (a i) (a j) ≫
          SmoothSite.torusPowerToBase (.of k) 2 = 𝟙 _ := by
        apply SmoothSite.torusPower_hom_ext (.of k) 0
        intro t
        exact Fin.elim0 t
      rw [← Category.assoc, hb, Category.id_comp]

/-- Each source identity axis lands in its corresponding actual target identity axis. -/
theorem varyingPair_axis (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) (s : Fin 2) :
    ∃ (t : Fin (q + 1))
      (φ : SmoothSite.torusPower (.of k) 1 ⟶ SmoothSite.torusPower (.of k) q),
      SmoothSite.torusInsertOne (.of k) 1 s ≫ varyingPair k (q + 1) a i j =
        φ ≫ SmoothSite.torusInsertOne (.of k) q t := by
  let ψ := SmoothSite.torusInsertOne (.of k) 1 s ≫ varyingPair k (q + 1) a i j
  let t := if s = 0 then i else j
  refine ⟨t, ψ ≫ SmoothSite.torusDeleteCoordinate (.of k) q t,
    factor_axis k q ψ t ?_⟩
  have hb : ψ ≫ SmoothSite.torusPowerToBase (.of k) (q + 1) =
      SmoothSite.torusPowerToBase (.of k) 1 := by
    apply SmoothSite.torusPower_hom_ext (.of k) 0
    intro r
    exact Fin.elim0 r
  rw [← Category.assoc, hb]
  fin_cases s
  · change (SmoothSite.torusInsertOne (.of k) 1 0 ≫ varyingPair k (q + 1) a i j) ≫
      SmoothSite.torusCoordinate (.of k) (q + 1) i = _
    simp only [Category.assoc, varyingPair, SmoothSite.torusPowerLift_coordinate,
      ite_true, SmoothSite.torusInsertOne_coordinate_self]
  · change (SmoothSite.torusInsertOne (.of k) 1 1 ≫ varyingPair k (q + 1) a i j) ≫
      SmoothSite.torusCoordinate (.of k) (q + 1) j = _
    simp only [Category.assoc, varyingPair, SmoothSite.torusPowerLift_coordinate,
      Ne.symm hij, ite_false, ite_true, SmoothSite.torusInsertOne_coordinate_self]

/-- Inserting fixed coordinates respects all actual reduced-torus relations. -/
def pairInsertion (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) :
    reducedTorus k 2 ⟶ reducedTorus k (q + 1) :=
  reducedTorusDesc k 2
    ((representableLarge k).map ((Cor.graphFunctor k).map (varyingPair k (q + 1) a i j)) ≫
      toReducedTorus k (q + 1)) (by
        intro s
        obtain ⟨t, φ, hφ⟩ := varyingPair_axis k q a i j hij s
        change (representableLarge k).map
          ((Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 1 s)) ≫
            (representableLarge k).map
              ((Cor.graphFunctor k).map (varyingPair k (q + 1) a i j)) ≫ _ = 0
        rw [← Functor.map_comp_assoc, ← Functor.map_comp, hφ, Functor.map_comp,
          Functor.map_comp, Category.assoc]
        change (representableLarge k).map ((Cor.graphFunctor k).map φ) ≫
          (torusIdentityAxis k (q + 1) t ≫ toReducedTorus k (q + 1)) = 0
        rw [torusIdentityAxis_toReducedTorus, comp_zero])

/-- The insertion retains every original signed finite correspondence. -/
theorem pairInsertion_quotient (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) (r : ℕ)
    (α : Cor.simplexProduct (point k) r ⟶ target k 2) :
    (pairInsertion k q a i j hij).hom.app (op (Cor.simplexProduct (point k) r))
      ((toReducedTorus k 2).hom.app _ (ULift.up α)) =
    (toReducedTorus k (q + 1)).hom.app _
      (ULift.up (α ≫ (Cor.graphFunctor k).map (varyingPair k (q + 1) a i j))) := by
  have h : toReducedTorus k 2 ≫ pairInsertion k q a i j hij =
      (representableLarge k).map ((Cor.graphFunctor k).map (varyingPair k (q + 1) a i j)) ≫
        toReducedTorus k (q + 1) := by
    unfold pairInsertion
    apply toReducedTorus_desc
  exact congrArg (fun f => f.hom.app (op (Cor.simplexProduct (point k) r)) (ULift.up α)) h

/-- The raw insertion sends the original weight-two graph symbol to the whole tuple. -/
theorem rawMap_pairSymbol (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) :
    rawMap k (pairInsertion k q a i j hij)
      (WeightTwoSymbols.graphSymbol k (a i) (a j)) = graphSymbol k (q + 1) a := by
  change rawMap k (pairInsertion k q a i j hij)
    (singularClass k 2 ((toReducedTorus k 2).hom.app _
      (ULift.up ((zeroProductIso k).hom ≫
        (Cor.graphFunctor k).map (WeightTwoSymbols.rationalPair k (a i) (a j)))))) = _
  rw [rawMap_singularClass, pairInsertion_quotient]
  have h := congrArg (fun f => (zeroProductIso k).hom ≫ (Cor.graphFunctor k).map f)
    (rationalPair_varyingPair k (q + 1) a i j)
  simp only [Functor.map_comp, ← Category.assoc] at h
  exact congrArg (fun α => singularClass k (q + 1)
    ((toReducedTorus k (q + 1)).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up α))) h

/-- Complementary entries in any two distinct positions give an actual zero class. -/
theorem graphSymbol_steinberg [CharZero k] (q : ℕ) (a : Fin q → kˣ)
    (i j : Fin q) (hij : i ≠ j) (hab : (a i : k) + (a j : k) = 1) :
    graphSymbol k q a = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    rw [← rawMap_pairSymbol k q a i j hij,
      WeightTwoSteinbergBound.graphSymbol_steinberg (a i) (a j)
        (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hab)), map_zero]

end Motivic.DiagonalCoordinateInsertion

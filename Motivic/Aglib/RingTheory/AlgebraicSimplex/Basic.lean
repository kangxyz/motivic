/-
Copyright (c) 2026 Motivic Cohomology Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Coordinate rings of the algebraic simplex

For a commutative ring `R`, `Motivic.AlgebraicSimplex.CoordinateRing R n` is the
canonical quotient `R[t₀, …, tₙ] / (∑ tᵢ - 1)` in every degree `n : ℕ`.
Its universal map `lift` evaluates the barycentric coordinates at any tuple whose
sum is one. The pullback along a map of finite ordinals sends each coordinate to
the sum of the coordinates in its fiber. These maps give a genuine simplicial
commutative ring `simplicialRing R`; its face and degeneracy maps therefore satisfy
all the simplicial identities.

`mapCoefficients` is functorial in arbitrary homomorphisms of commutative rings
and commutes with every simplex pullback. This file constructs coordinate rings
and ring homomorphisms; it does not assert smoothness, a scheme-level tensor
base-change theorem, or a motivic comparison theorem.

## References

* Mazza, Voevodsky, Weibel, *Lecture Notes on Motivic Cohomology*, Definition 3.1.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped BigOperators Simplicial

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The barycentric relation defining the algebraic `n`-simplex. -/
def relation (n : ℕ) : MvPolynomial (Fin (n + 1)) R :=
  (∑ i, MvPolynomial.X i) - 1

/-- The principal ideal of the barycentric relation. -/
def ideal (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span {relation R n}

/-- The canonical coordinate ring `R[t₀, …, tₙ] / (∑ tᵢ - 1)`. -/
abbrev CoordinateRing (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) R ⧸ ideal R n

/-- The canonical polynomial-to-coordinate-ring quotient map. -/
def quotientMap (n : ℕ) : MvPolynomial (Fin (n + 1)) R →+* CoordinateRing R n :=
  Ideal.Quotient.mk (ideal R n)

/-- The coefficient homomorphism to the coordinate ring. -/
def constant (n : ℕ) : R →+* CoordinateRing R n :=
  (quotientMap R n).comp MvPolynomial.C

/-- The `i`-th barycentric coordinate. -/
def coordinate (n : ℕ) (i : Fin (n + 1)) : CoordinateRing R n :=
  quotientMap R n (MvPolynomial.X i)

@[simp]
theorem quotientMap_relation (n : ℕ) : quotientMap R n (relation R n) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The barycentric coordinates sum to one. -/
@[simp]
theorem sum_coordinate (n : ℕ) : ∑ i, coordinate R n i = 1 := by
  have h := quotientMap_relation R n
  simpa only [relation, map_sub, map_sum, map_one, coordinate, sub_eq_zero] using h

variable {R} {S : Type v} [CommRing S] {T : Type w} [CommRing T]

/-- Homomorphisms out of a simplex ring are determined by coefficients and coordinates. -/
@[ext]
theorem ringHom_ext {n : ℕ} {f g : CoordinateRing R n →+* S}
    (hC : ∀ r, f (constant R n r) = g (constant R n r))
    (hX : ∀ i, f (coordinate R n i) = g (coordinate R n i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  exact MvPolynomial.ringHom_ext hC hX

/-- Evaluate barycentric coordinates at a tuple with sum one. -/
def lift {n : ℕ} (c : R →+* S) (x : Fin (n + 1) → S) (hx : ∑ i, x i = 1) :
    CoordinateRing R n →+* S :=
  Ideal.Quotient.lift (ideal R n) (MvPolynomial.eval₂Hom c x) (by
    have h : ideal R n ≤ RingHom.ker (MvPolynomial.eval₂Hom c x) := by
      apply Ideal.span_le.mpr
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      change MvPolynomial.eval₂Hom c x (relation R n) = 0
      simp [relation, hx]
    exact h)

@[simp]
theorem lift_constant {n : ℕ} (c : R →+* S) (x : Fin (n + 1) → S)
    (hx : ∑ i, x i = 1) (r : R) : lift c x hx (constant R n r) = c r := by
  simp [lift, constant, quotientMap]

@[simp]
theorem lift_coordinate {n : ℕ} (c : R →+* S) (x : Fin (n + 1) → S)
    (hx : ∑ i, x i = 1) (i : Fin (n + 1)) : lift c x hx (coordinate R n i) = x i := by
  simp [lift, coordinate, quotientMap]

/-- The canonical universal-property map is unique. -/
theorem lift_unique {n : ℕ} (c : R →+* S) (x : Fin (n + 1) → S)
    (hx : ∑ i, x i = 1) (f : CoordinateRing R n →+* S)
    (hC : ∀ r, f (constant R n r) = c r)
    (hX : ∀ i, f (coordinate R n i) = x i) : f = lift c x hx := by
  apply ringHom_ext <;> simp_all

variable (R)

/-- Pullback along an arbitrary map of finite ordinals. Each coordinate pulls
back to the sum over its fiber. Monotonicity is unnecessary for this construction. -/
def pullback {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    CoordinateRing R n →+* CoordinateRing R m :=
  lift (constant R m) (fun j ↦ ∑ i with f i = j, coordinate R m i) (by
    rw [Finset.sum_fiberwise]
    exact sum_coordinate R m)

@[simp]
theorem pullback_constant {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (r : R) :
    pullback R f (constant R n r) = constant R m r :=
  lift_constant _ _ _ _

@[simp]
theorem pullback_coordinate {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (j : Fin (n + 1)) :
    pullback R f (coordinate R n j) = ∑ i with f i = j, coordinate R m i :=
  lift_coordinate _ _ _ _

@[simp]
theorem pullback_id (n : ℕ) : pullback R (id : Fin (n + 1) → Fin (n + 1)) =
    RingHom.id (CoordinateRing R n) := by
  apply ringHom_ext
  · intro r
    simp
  · intro i
    simp [Finset.sum_filter]

/-- Pullbacks compose contravariantly, for arbitrary maps of finite ordinals. -/
theorem pullback_comp {l m n : ℕ} (f : Fin (l + 1) → Fin (m + 1))
    (g : Fin (m + 1) → Fin (n + 1)) :
    pullback R (g ∘ f) = (pullback R f).comp (pullback R g) := by
  apply ringHom_ext
  · intro r
    simp
  · intro j
    simp only [pullback_coordinate, RingHom.comp_apply, map_sum]
    rw [Finset.sum_fiberwise_eq_sum_filter]
    simp

/-- The simplicial commutative ring of algebraic simplex coordinates. -/
def simplicialRing : SimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (CoordinateRing R n.unop.len)
  map f := CommRingCat.ofHom (pullback R f.unop.toOrderHom)
  map_id n := by
    apply CommRingCat.hom_ext
    exact pullback_id R n.unop.len
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact pullback_comp R g.unop.toOrderHom f.unop.toOrderHom

/-- The face map obtained by setting the `i`-th barycentric coordinate to zero. -/
def face {n : ℕ} (i : Fin (n + 2)) : CoordinateRing R (n + 1) →+* CoordinateRing R n :=
  ((simplicialRing R).δ i).hom

/-- The degeneracy map adding the two adjacent barycentric coordinates. -/
def degeneracy {n : ℕ} (i : Fin (n + 1)) :
    CoordinateRing R n →+* CoordinateRing R (n + 1) :=
  ((simplicialRing R).σ i).hom

/-- A face is pullback along the injection omitting its vertex. -/
theorem face_eq_pullback {n : ℕ} (i : Fin (n + 2)) :
    face R i = pullback R i.succAbove := rfl

/-- A degeneracy is pullback along the ordinal map identifying adjacent vertices. -/
theorem degeneracy_eq_pullback {n : ℕ} (i : Fin (n + 1)) :
    degeneracy R i = pullback R i.predAbove := rfl

@[simp]
theorem face_coordinate_self {n : ℕ} (i : Fin (n + 2)) :
    face R i (coordinate R (n + 1) i) = 0 := by
  simp [face_eq_pullback, Fin.succAbove_ne]

@[simp]
theorem face_coordinate_succAbove {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    face R i (coordinate R (n + 1) (i.succAbove j)) = coordinate R n j := by
  simp [face_eq_pullback, Finset.sum_filter]

/-- A degeneracy adds coordinates in the corresponding ordinal fiber. -/
theorem degeneracy_coordinate {n : ℕ} (i j : Fin (n + 1)) :
    degeneracy R i (coordinate R n j) =
      ∑ k with i.predAbove k = j, coordinate R (n + 1) k :=
  pullback_coordinate R i.predAbove j

@[simp]
theorem degeneracy_coordinate_self {n : ℕ} (i : Fin (n + 1)) :
    degeneracy R i (coordinate R n i) =
      coordinate R (n + 1) i.castSucc + coordinate R (n + 1) i.succ := by
  rw [degeneracy_coordinate, Finset.sum_filter, Fin.sum_univ_succAbove _ i.castSucc]
  simp

/-- The face-face identity in ring-homomorphism form. -/
theorem face_comp_face {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    (face R i).comp (face R j.succ) = (face R j).comp (face R i.castSucc) :=
  congrArg CommRingCat.Hom.hom ((simplicialRing R).δ_comp_δ h)

/-- The degeneracy-degeneracy identity in ring-homomorphism form. -/
theorem degeneracy_comp_degeneracy {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    (degeneracy R i.castSucc).comp (degeneracy R j) =
      (degeneracy R j.succ).comp (degeneracy R i) :=
  congrArg CommRingCat.Hom.hom ((simplicialRing R).σ_comp_σ h)

/-- The first face-degeneracy identity. -/
theorem face_comp_degeneracy_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) :
    (face R i.castSucc).comp (degeneracy R j.succ) =
      (degeneracy R j).comp (face R i) :=
  congrArg CommRingCat.Hom.hom ((simplicialRing R).δ_comp_σ_of_le h)

/-- The first cancellation identity for adjacent faces and degeneracies. -/
@[simp]
theorem face_comp_degeneracy_self {n : ℕ} (i : Fin (n + 1)) :
    (face R i.castSucc).comp (degeneracy R i) = RingHom.id (CoordinateRing R n) :=
  congrArg CommRingCat.Hom.hom ((simplicialRing R).δ_comp_σ_self (i := i))

/-- The second cancellation identity for adjacent faces and degeneracies. -/
@[simp]
theorem face_comp_degeneracy_succ {n : ℕ} (i : Fin (n + 1)) :
    (face R i.succ).comp (degeneracy R i) = RingHom.id (CoordinateRing R n) :=
  congrArg CommRingCat.Hom.hom ((simplicialRing R).δ_comp_σ_succ (i := i))

/-- The final face-degeneracy identity. -/
theorem face_comp_degeneracy_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) :
    (face R i.succ).comp (degeneracy R j.castSucc) =
      (degeneracy R j).comp (face R i) :=
  congrArg CommRingCat.Hom.hom ((simplicialRing R).δ_comp_σ_of_gt h)

variable {R}

/-- The homomorphism induced by changing the coefficient ring. -/
def mapCoefficients (c : R →+* S) (n : ℕ) : CoordinateRing R n →+* CoordinateRing S n :=
  lift ((constant S n).comp c) (coordinate S n) (sum_coordinate S n)

@[simp]
theorem mapCoefficients_constant (c : R →+* S) (n : ℕ) (r : R) :
    mapCoefficients c n (constant R n r) = constant S n (c r) :=
  lift_constant _ _ _ _

@[simp]
theorem mapCoefficients_coordinate (c : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    mapCoefficients c n (coordinate R n i) = coordinate S n i :=
  lift_coordinate _ _ _ _

@[simp]
theorem mapCoefficients_id (n : ℕ) :
    mapCoefficients (RingHom.id R) n = RingHom.id (CoordinateRing R n) := by
  apply ringHom_ext <;> simp

/-- Changing coefficients is functorial. -/
theorem mapCoefficients_comp (c : R →+* S) (d : S →+* T) (n : ℕ) :
    mapCoefficients (d.comp c) n = (mapCoefficients d n).comp (mapCoefficients c n) := by
  apply ringHom_ext <;> simp

/-- Changing coefficients commutes with every simplex pullback. -/
theorem mapCoefficients_pullback (c : R →+* S) {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) :
    (mapCoefficients c m).comp (pullback R f) =
      (pullback S f).comp (mapCoefficients c n) := by
  apply ringHom_ext <;> simp [map_sum]

/-- A coefficient homomorphism induces a morphism of simplicial commutative rings. -/
def simplicialMap {S : Type u} [CommRing S] (c : R →+* S) :
    simplicialRing R ⟶ simplicialRing S where
  app n := CommRingCat.ofHom (mapCoefficients c n.unop.len)
  naturality _ _ f := by
    apply CommRingCat.hom_ext
    exact mapCoefficients_pullback c f.unop.toOrderHom

@[simp]
theorem simplicialMap_id : simplicialMap (RingHom.id R) = 𝟙 (simplicialRing R) := by
  ext n : 2
  exact mapCoefficients_id n.unop.len

/-- Coefficient change composes as a morphism of simplicial rings. -/
theorem simplicialMap_comp {S T : Type u} [CommRing S] [CommRing T]
    (c : R →+* S) (d : S →+* T) :
    simplicialMap (d.comp c) = simplicialMap c ≫ simplicialMap d := by
  ext n : 2
  exact mapCoefficients_comp c d n.unop.len

end AlgebraicSimplex

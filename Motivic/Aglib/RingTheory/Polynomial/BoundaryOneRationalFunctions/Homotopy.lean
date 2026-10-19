/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Basic
public import Motivic.Aglib.RingTheory.Polynomial.ZeroNeighborhood.Pencil

/-!
# Affine linear homotopy of actual boundary-one rational functions

The literal formula `1 - s + s * f` is an admissible rational function. It
specializes to one and to `f`, is natural in the coefficient ring, and fixes
the function one. This is a map of sets, not a homomorphism of groups.
No geometric divisor presentation or sheaf comparison is asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace Polynomial.BoundaryOneRationalFunctions

open ZeroNeighborhoodInterpolation

variable {R : Type u} [CommRing R]

/-- The denominator of a literal fraction cancels in the actual ring. -/
theorem fraction_val_mul (p q : denominators R) :
    (fraction p q : Ring R) * algebraMap R[X] (Ring R) q =
      algebraMap R[X] (Ring R) p := by
  simpa only [fraction, Units.val_mul, polynomialUnit_val] using
    congrArg (fun z : (Ring R)ˣ => (z : Ring R))
      (div_mul_cancel (polynomialUnit p) (polynomialUnit q))

/-- The coefficient variable is the homotopy parameter, not the target variable. -/
def parameter (R : Type u) [CommRing R] : Ring R[X] :=
  algebraMap R[X][X] (Ring R[X]) (C X)

/-- The representation-independent affine linear formula in the actual ring. -/
def linear (f : group R) : Ring R[X] :=
  1 - parameter R + parameter R * ringMap C (f.val : Ring R)

/-- The literal linear combination has an admissible monic fraction presentation. -/
theorem exists_linear (f : group R) :
    ∃ g : group R[X], (g.val : Ring R[X]) = linear f := by
  nontriviality R
  obtain ⟨p, q, hd, hc, hf⟩ := f.2
  let P : R[X][X] := pencil (q : R[X]) p
  have hP := pencil_monic_natDegree q.2.1 p.2.1 hd
  have hC : P.coeff 0 = ((q : R[X]).map C).coeff 0 := by
    change (pencil (q : R[X]) p).coeff 0 = ((q : R[X]).map C).coeff 0
    rw [pencil_coeff, hc, coeff_map]
    ring
  have hU : IsUnit (P.coeff 0) := by
    rw [hC, coeff_map]
    exact q.2.2.map C
  let g := ofPresentation P ((q : R[X]).map C) hP.1 (q.2.1.map C)
    (hP.2.trans (q.2.1.natDegree_map C).symm) hC hU
  refine ⟨g, ?_⟩
  have hg : (g.val : Ring R[X]) * algebraMap R[X][X] (Ring R[X])
      ((q : R[X]).map C) = algebraMap R[X][X] (Ring R[X]) P :=
    fraction_val_mul ⟨P, hP.1, hU⟩ (denominatorMap C q)
  have hf' : ringMap C (f.val : Ring R) *
      algebraMap R[X][X] (Ring R[X]) ((q : R[X]).map C) =
        algebraMap R[X][X] (Ring R[X]) ((p : R[X]).map C) := by
    have h := congrArg (ringMap (C : R →+* R[X])) (fraction_val_mul p q)
    rw [hf]
    simpa only [map_mul, ringMap_algebraMap] using h
  apply (IsLocalization.map_units (Ring R[X]) (denominatorMap C q)).mul_left_inj.mp
  change (g.val : Ring R[X]) * algebraMap R[X][X] (Ring R[X])
    ((q : R[X]).map C) = linear f * algebraMap R[X][X] (Ring R[X])
      ((q : R[X]).map C)
  rw [hg]
  dsimp only [P, pencil, linear, parameter]
  rw [map_add, map_mul, map_mul, C_sub, C_1, map_sub, map_one, ← hf']
  ring

/-- The actual admissible affine homotopy. It is intentionally only a function. -/
def homotopy (f : group R) : group R[X] := (exists_linear f).choose

/-- The chosen admissible function is the literal affine expression. -/
@[simp] theorem homotopy_val (f : group R) :
    ((homotopy f).val : Ring R[X]) = linear f := (exists_linear f).choose_spec

/-- Specializing the parameter leaves the original rational function unchanged. -/
@[simp] theorem ringMap_specialize_constant (t : R) (x : Ring R) :
    ringMap (evalRingHom t) (ringMap C x) = x := by
  have h : (evalRingHom t).comp (C : R →+* R[X]) = RingHom.id R := by
    ext r
    simp
  change ((ringMap (evalRingHom t)).comp (ringMap C)) x = x
  rw [← ringMap_comp, h, ringMap_id]
  rfl

@[simp] theorem ringMap_specialize_parameter (t : R) :
    ringMap (evalRingHom t) (parameter R) =
      algebraMap R[X] (Ring R) (C t) := by
  simp [parameter]

/-- The zero endpoint of the actual linear homotopy is the identity function. -/
@[simp] theorem homotopy_zero (f : group R) : map (evalRingHom 0) (homotopy f) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ringMap (evalRingHom 0) ((homotopy f).val : Ring R[X]) = 1
  rw [homotopy_val]
  simp [linear]

/-- The one endpoint is the original rational function, with no inverse or twist. -/
@[simp] theorem homotopy_one (f : group R) : map (evalRingHom 1) (homotopy f) = f := by
  apply Subtype.ext
  apply Units.ext
  change ringMap (evalRingHom 1) ((homotopy f).val : Ring R[X]) = (f.val : Ring R)
  rw [homotopy_val]
  simp [linear]

/-- The linear homotopy fixes the trivial rational function. -/
@[simp] theorem homotopy_identity : homotopy (1 : group R) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((homotopy (1 : group R)).val : Ring R[X]) = 1
  rw [homotopy_val]
  simp [linear]

variable {S : Type v} [CommRing S]

/-- Changing coefficients commutes with adjoining the parameter. -/
theorem ringMap_coefficient_naturality (φ : R →+* S) (x : Ring R) :
    ringMap (Polynomial.mapRingHom φ) (ringMap C x) = ringMap C (ringMap φ x) := by
  have h : (Polynomial.mapRingHom φ).comp (C : R →+* R[X]) =
      (C : S →+* S[X]).comp φ := by
    ext r
    simp
  change ((ringMap (Polynomial.mapRingHom φ)).comp (ringMap C)) x =
    ((ringMap C).comp (ringMap φ)) x
  rw [← ringMap_comp, h, ringMap_comp]

@[simp] theorem ringMap_parameter (φ : R →+* S) :
    ringMap (Polynomial.mapRingHom φ) (parameter R) = parameter S := by
  simp [parameter]

/-- Naturality includes arbitrary noninjective maps, hence all simplex faces. -/
@[simp] theorem homotopy_natural (φ : R →+* S) (f : group R) :
    map (Polynomial.mapRingHom φ) (homotopy f) = homotopy (map φ f) := by
  apply Subtype.ext
  apply Units.ext
  change ringMap (Polynomial.mapRingHom φ) ((homotopy f).val : Ring R[X]) =
    ((homotopy (map φ f)).val : Ring S[X])
  rw [homotopy_val, homotopy_val]
  simp only [linear, map_add, map_sub, map_one, map_mul, ringMap_parameter,
    ringMap_coefficient_naturality]
  rfl

/-- Every face on which the original function is one remains one throughout the homotopy. -/
theorem homotopy_preserves_face_one (φ : R →+* S) (f : group R)
    (hf : map φ f = 1) : map (Polynomial.mapRingHom φ) (homotopy f) = 1 := by
  rw [homotopy_natural, hf, homotopy_identity]

end Polynomial.BoundaryOneRationalFunctions

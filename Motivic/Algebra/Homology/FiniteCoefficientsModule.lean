/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.FiniteCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Signed coordinates for finite-coefficient complexes of modules

The finite coefficient complex is the actual mathlib mapping cone, not a
record postulating cohomology groups. We construct its elements from pairs
`(a,b)`, prove that its differential is `(da - n b, -db)`, and identify its
cocycles by `da = n b` and `db = 0`. The connecting map is positive projection
onto `b`, exactly matching the coefficient triangle in `FiniteCoefficients`.

All definitions work for every ring and every natural coefficient level;
in particular, composite levels and the zero-coefficient level one are included.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex CochainComplex.HomComplex HomologicalComplex

universe u v

namespace Motivic.finiteCoefficients

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℕ)

/-- The signed inclusion of the Bockstein coordinate into a coefficient term. -/
noncomputable def inB (i : ℤ) : K.X (i + 1) ⟶ (finiteCoefficients K n).X i :=
  -(mappingCone.inl (n • 𝟙 K)).v (i + 1) i (by omega)

@[reassoc (attr := simp)]
theorem inB_a (i : ℤ) : inB K n i ≫ a K n i = 0 := by
  simp [inB, a]

@[reassoc (attr := simp)]
theorem inB_b (i : ℤ) : inB K n i ≫ b K n i = 𝟙 _ := by
  simp [inB, b]

/-- Every coefficient term is the direct sum of the two signed coordinates. -/
theorem coordinate_decomposition (i : ℤ) :
    b K n i ≫ inB K n i + a K n i ≫ (integral K n).f i = 𝟙 _ := by
  simpa [b, inB, a, integral, finiteCoefficients] using mappingCone.id_X (n • 𝟙 K) i (i + 1) rfl

/-- Construct an actual coefficient element from its integral and Bockstein coordinates. -/
noncomputable def ofPair (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    (finiteCoefficients K n).X i :=
  (integral K n).f i x + inB K n i y

@[simp]
theorem a_ofPair (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    a K n i (ofPair K n i x y) = x := by
  simp only [ofPair, map_add, ← ModuleCat.comp_apply, integral_a, inB_a]
  simp

@[simp]
theorem b_ofPair (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    b K n i (ofPair K n i x y) = y := by
  simp only [ofPair, map_add, ← ModuleCat.comp_apply, integral_b, inB_b]
  simp

@[simp]
theorem ofPair_coordinates (i : ℤ) (z : (finiteCoefficients K n).X i) :
    ofPair K n i (a K n i z) (b K n i z) = z := by
  have h := congrArg (fun f : (finiteCoefficients K n).X i ⟶
    (finiteCoefficients K n).X i => f z) (coordinate_decomposition K n i)
  simpa [ofPair, ModuleCat.comp_apply, add_comm] using h

/-- Elementwise extensionality in a coefficient term. -/
theorem element_ext (i : ℤ) {z w : (finiteCoefficients K n).X i}
    (ha : a K n i z = a K n i w) (hb : b K n i z = b K n i w) : z = w := by
  rw [← ofPair_coordinates K n i z, ← ofPair_coordinates K n i w, ha, hb]

/-- The differential has the signed formula `da - n b` on its integral coordinate. -/
@[simp]
theorem a_d_apply (i : ℤ) (z : (finiteCoefficients K n).X i) :
    a K n (i + 1) ((finiteCoefficients K n).d i (i + 1) z) =
      K.d i (i + 1) (a K n i z) - n • b K n i z := by
  have h := congrArg (fun f : (finiteCoefficients K n).X i ⟶ K.X (i + 1) => f z)
    (d_a K n i)
  simpa [ModuleCat.comp_apply] using h

/-- The differential has the signed formula `-db` on its Bockstein coordinate. -/
@[simp]
theorem b_d_apply (i : ℤ) (z : (finiteCoefficients K n).X i) :
    b K n (i + 1) ((finiteCoefficients K n).d i (i + 1) z) =
      -K.d (i + 1) (i + 1 + 1) (b K n i z) := by
  have h := congrArg (fun f : (finiteCoefficients K n).X i ⟶ K.X (i + 1 + 1) => f z)
    (d_b K n i)
  simpa [ModuleCat.comp_apply] using h

/-- The actual mapping-cone differential, written in the positive pair convention. -/
theorem d_ofPair (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    (finiteCoefficients K n).d i (i + 1) (ofPair K n i x y) =
      ofPair K n (i + 1) (K.d i (i + 1) x - n • y)
        (-K.d (i + 1) (i + 1 + 1) y) := by
  apply element_ext K n (i + 1) <;> simp

/-- A coefficient cocycle satisfies precisely `da = n b` and `db = 0`. -/
theorem isCycle_iff (i : ℤ) (z : (finiteCoefficients K n).X i) :
    (finiteCoefficients K n).d i (i + 1) z = 0 ↔
      K.d i (i + 1) (a K n i z) = n • b K n i z ∧
        K.d (i + 1) (i + 1 + 1) (b K n i z) = 0 := by
  constructor
  · intro hz
    have ha := congrArg (a K n (i + 1)) hz
    have hb := congrArg (b K n (i + 1)) hz
    simpa [sub_eq_zero] using And.intro ha hb
  · rintro ⟨ha, hb⟩
    apply element_ext K n (i + 1) <;> simp [ha, hb]

/-- The Bockstein is literally positive projection on pair representatives. -/
theorem bockstein_ofPair (i : ℤ) (x : K.X i) (y : K.X (i + 1)) :
    (bockstein K n).f i (ofPair K n i x y) = y := by
  rw [bockstein_f]
  simp

end Motivic.finiteCoefficients

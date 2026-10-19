/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Finite coefficients of a cochain complex

For a cochain complex `K` in an additive category, `finiteCoefficients K n`
is the actual mapping cone of `n • 𝟙 K`. This construction is defined in every
integer degree, including level one. Its coefficient triangle is mathlib's
standard mapping-cone triangle, whose connecting map is the negative first
projection. Accordingly, the positive Bockstein coordinate is `b = -fst`,
while the integral coordinate is `a = snd`: a cocycle satisfies `da = n b`.

The construction supplies functorial maps, coefficient reduction and insertion,
and a contraction at level one. At positive levels it is a chain-level model
for tensoring with the two-term free resolution of `ℤ/n`; no comparison with a derived tensor
functor or with a motivic complex is asserted here.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex CochainComplex.HomComplex HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Mapping-cone finite coefficients, represented by the mapping cone of multiplication by `n`. -/
noncomputable def finiteCoefficients (K : CochainComplex C ℤ) (n : ℕ) :
    CochainComplex C ℤ :=
  mappingCone (n • 𝟙 K)

namespace finiteCoefficients

variable (K : CochainComplex C ℤ) (n : ℕ)

/-- The canonical coefficient triangle `K --n--> K --> K/n --> K[1]`. -/
noncomputable def triangle : CategoryTheory.Pretriangulated.Triangle (CochainComplex C ℤ) :=
  mappingCone.triangle (n • 𝟙 K)

/-- The map from integral to finite coefficients. -/
noncomputable def integral : K ⟶ finiteCoefficients K n :=
  mappingCone.inr (n • 𝟙 K)

/-- The connecting morphism of the actual coefficient triangle. -/
noncomputable def bockstein : finiteCoefficients K n ⟶ K⟦(1 : ℤ)⟧ :=
  (triangle K n).mor₃

/-- The integral coordinate in degree `i`. -/
noncomputable def a (i : ℤ) : (finiteCoefficients K n).X i ⟶ K.X i :=
  (mappingCone.snd (n • 𝟙 K)).v i i (add_zero i)

/-- The positive Bockstein coordinate in degree `i`. -/
noncomputable def b (i : ℤ) : (finiteCoefficients K n).X i ⟶ K.X (i + 1) :=
  -(mappingCone.fst (n • 𝟙 K)).1.v i (i + 1) rfl

@[reassoc (attr := simp)]
theorem integral_a (i : ℤ) : (integral K n).f i ≫ a K n i = 𝟙 _ := by
  simp [integral, a]

@[reassoc (attr := simp)]
theorem integral_b (i : ℤ) : (integral K n).f i ≫ b K n i = 0 := by
  simp [integral, b]

/-- The first coordinate of the differential is `da - n b`. -/
@[reassoc]
theorem d_a (i : ℤ) :
    (finiteCoefficients K n).d i (i + 1) ≫ a K n (i + 1) =
      a K n i ≫ K.d i (i + 1) - n • b K n i := by
  dsimp [finiteCoefficients, a, b]
  rw [mappingCone.d_snd_v _ _ _ rfl]
  simp [sub_eq_add_neg, add_comm]

/-- The Bockstein coordinate of the differential is `-db`. -/
@[reassoc]
theorem d_b (i : ℤ) :
    (finiteCoefficients K n).d i (i + 1) ≫ b K n (i + 1) =
      -(b K n i ≫ K.d (i + 1) (i + 1 + 1)) := by
  dsimp [finiteCoefficients, b]
  rw [comp_neg, mappingCone.d_fst_v _ _ _ _ rfl rfl]
  simp

/-- The connecting morphism is the positive coordinate, followed by the shift identification. -/
theorem bockstein_f (i : ℤ) :
    (bockstein K n).f i =
      b K n i ≫ (K.shiftFunctorObjXIso 1 i (i + 1) rfl).inv := by
  apply mappingCone.ext_from (n • 𝟙 K) (i + 1) i rfl
  · simp [bockstein, triangle, b]
  · simp [bockstein, triangle, b]

/-- Equality into a coefficient term can be tested on its two signed coordinates. -/
theorem ext_to {A : C} (i : ℤ) {f g : A ⟶ (finiteCoefficients K n).X i}
    (ha : f ≫ a K n i = g ≫ a K n i)
    (hb : f ≫ b K n i = g ≫ b K n i) : f = g := by
  apply mappingCone.ext_to (n • 𝟙 K) i (i + 1) rfl
  · simpa [b] using hb
  · exact ha

variable {K} {L M : CochainComplex C ℤ}

/-- Functoriality of finite coefficients in the integral complex. -/
noncomputable def map (f : K ⟶ L) : finiteCoefficients K n ⟶ finiteCoefficients L n :=
  mappingCone.map (n • 𝟙 K) (n • 𝟙 L) f f (by simp)

@[simp]
theorem map_id : map n (𝟙 K) = 𝟙 (finiteCoefficients K n) := by
  exact mappingCone.map_id _

@[reassoc]
theorem map_comp (f : K ⟶ L) (g : L ⟶ M) :
    map n (f ≫ g) = map n f ≫ map n g := by
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem map_a (f : K ⟶ L) (i : ℤ) :
    (map n f).f i ≫ a L n i = a K n i ≫ f.f i := by
  apply mappingCone.ext_from (n • 𝟙 K) (i + 1) i rfl <;>
    simp [map, mappingCone.map, a]

@[reassoc (attr := simp)]
theorem map_b (f : K ⟶ L) (i : ℤ) :
    (map n f).f i ≫ b L n i = b K n i ≫ f.f (i + 1) := by
  apply mappingCone.ext_from (n • 𝟙 K) (i + 1) i rfl <;>
    simp [map, mappingCone.map, b]

@[reassoc]
theorem integral_naturality (f : K ⟶ L) :
    integral K n ≫ map n f = f ≫ integral L n := by
  ext i
  simp [integral, map, mappingCone.map]

@[reassoc]
theorem bockstein_naturality (f : K ⟶ L) :
    map n f ≫ bockstein L n = bockstein K n ≫ f⟦(1 : ℤ)⟧' := by
  exact (mappingCone.triangleMap (n • 𝟙 K) (n • 𝟙 L) f f (by simp)).comm₃.symm

/-- The finite coefficient construction is a functor on genuine cochain complexes. -/
noncomputable def functor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := finiteCoefficients K n
  map f := map n f
  map_id _ := map_id n
  map_comp f g := map_comp n f g

variable (K)

/-- Reduction from level `n * k` to level `n`; its positive coordinate is multiplied by `k`. -/
noncomputable def reduction (k : ℕ) :
    finiteCoefficients K (n * k) ⟶ finiteCoefficients K n :=
  mappingCone.map ((n * k) • 𝟙 K) (n • 𝟙 K) (k • 𝟙 K) (𝟙 K)
    (by simp [smul_smul])

/-- Coefficient insertion from level `n` to level `n * k`.
The integral coordinate is multiplied by `k`. -/
noncomputable def insertion (k : ℕ) :
    finiteCoefficients K n ⟶ finiteCoefficients K (n * k) :=
  mappingCone.map (n • 𝟙 K) ((n * k) • 𝟙 K) (𝟙 K) (k • 𝟙 K)
    (by simp [smul_smul, Nat.mul_comm])

@[reassoc (attr := simp)]
theorem reduction_a (k : ℕ) (i : ℤ) :
    (reduction K n k).f i ≫ a K n i = a K (n * k) i := by
  apply mappingCone.ext_from ((n * k) • 𝟙 K) (i + 1) i rfl <;>
    simp [reduction, mappingCone.map, a]

@[reassoc (attr := simp)]
theorem reduction_b (k : ℕ) (i : ℤ) :
    (reduction K n k).f i ≫ b K n i = k • b K (n * k) i := by
  apply mappingCone.ext_from ((n * k) • 𝟙 K) (i + 1) i rfl <;>
    simp [reduction, mappingCone.map, b]

@[reassoc (attr := simp)]
theorem insertion_a (k : ℕ) (i : ℤ) :
    (insertion K n k).f i ≫ a K (n * k) i = k • a K n i := by
  apply mappingCone.ext_from (n • 𝟙 K) (i + 1) i rfl <;>
    simp [insertion, mappingCone.map, a]

@[reassoc (attr := simp)]
theorem insertion_b (k : ℕ) (i : ℤ) :
    (insertion K n k).f i ≫ b K (n * k) i = b K n i := by
  apply mappingCone.ext_from (n • 𝟙 K) (i + 1) i rfl <;>
    simp [insertion, mappingCone.map, b]

/-- Inserting then reducing multiplies the original coefficient complex by `k`. -/
@[reassoc]
theorem insertion_reduction (k : ℕ) :
    insertion K n k ≫ reduction K n k = k • 𝟙 (finiteCoefficients K n) := by
  ext i
  apply ext_to K n i <;> simp

/-- Reducing then inserting multiplies the larger coefficient complex by `k`. -/
@[reassoc]
theorem reduction_insertion (k : ℕ) :
    reduction K n k ≫ insertion K n k = k • 𝟙 (finiteCoefficients K (n * k)) := by
  ext i
  apply ext_to K (n * k) i <;> simp

/-- Reduction is natural with respect to every morphism of integral complexes. -/
@[reassoc]
theorem reduction_naturality (f : K ⟶ L) (k : ℕ) :
    map (n * k) f ≫ reduction L n k = reduction K n k ≫ map n f := by
  ext i
  apply ext_to L n i <;> simp

/-- Insertion is natural with respect to every morphism of integral complexes. -/
@[reassoc]
theorem insertion_naturality (f : K ⟶ L) (k : ℕ) :
    map n f ≫ insertion L n k = insertion K n k ≫ map (n * k) f := by
  ext i
  apply ext_to L (n * k) i <;> simp

/-- Level-one coefficients are contractible, with an actual cochain homotopy. -/
noncomputable def contractionOne :
    Homotopy (𝟙 (finiteCoefficients K 1)) 0 := by
  exact mappingCone.descHomotopy (1 • 𝟙 K) _ _ 0 (mappingCone.inl _)
    (by simp [finiteCoefficients]) (by simp [finiteCoefficients])

/-- The homology of level-one coefficients vanishes in every degree. -/
theorem isZero_homology_one (i : ℤ) [(finiteCoefficients K 1).HasHomology i] :
    IsZero ((finiteCoefficients K 1).homology i) := by
  apply (IsZero.iff_id_eq_zero _).2
  simpa using (contractionOne K).homologyMap_eq i

end finiteCoefficients
end CochainComplex

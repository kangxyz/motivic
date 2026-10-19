/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.Pair
public import Motivic.Aglib.AlgebraicGeometry.Graph.PointTransport
public import Motivic.Aglib.AlgebraicGeometry.Graph.SpecTransversality

/-!
# The common diagonal list on actual affine graph products

The tensor-spectrum diagram is identified with the actual affine products.
The resulting regular diagonal-kernel list has regular literal images under
the actual graph pair stalk map. The graph source ring remains arbitrary.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open RingTheory.Sequence

universe u v

namespace AlgebraicGeometry.Scheme.Graph.Affine
open _root_.Algebra.TensorProduct _root_.AlgebraicGeometry.Scheme.Diagonal

variable (R : Type u) (σ : Type v) (A B : Type u)
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra (MvPolynomial σ R) B] [IsScalarTower R (MvPolynomial σ R) B]
  (f : B →ₐ[MvPolynomial σ R] A)
  (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))

set_option backward.isDefEq.respectTransparency false in
/-- The tensor pair map and the actual affine product pair map form a commuting square. -/
theorem spec_diagonalPullback_square :
    Spec.map (CommRingCat.ofHom (PolynomialGraph.diagonalPullback R σ A B f).toRingHom) ≫
      (pullbackSpecIso R B B).inv =
    (pullbackSpecIso R A B).inv ≫
      middlePair (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom f.toRingHom)) h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst, middlePair_fst,
      pullbackSpecIso_inv_fst_assoc, ← Spec.map_comp]
    congr 1
  · simp only [Category.assoc, pullbackSpecIso_inv_snd, middlePair_snd, ← Spec.map_comp]
    congr 1
    ext b
    change PolynomialGraph.diagonalPullback R σ A B f (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] b
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine graph maps to the actual target diagonal. -/
theorem graph_middlePair :
    graph R σ A B f ≫
      middlePair (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom f.toRingHom)) h =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Affine.diagonal R B := by
  apply pullback.hom_ext <;> simp

/-- The literal map from the target diagonal stalk to the actual affine graph product stalk. -/
def diagonalStalkMap (p : PrimeSpectrum A) :
    (_root_.AlgebraicGeometry.Scheme.Diagonal.Affine.product R B).presheaf.stalk
      (Affine.diagonal R B ((Spec.map (CommRingCat.ofHom f.toRingHom)) p)) ⟶
    (product R A B).presheaf.stalk (graph R σ A B f p) :=
  alignedStalkMap
    (middlePair (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom f.toRingHom)) h)
    (graph R σ A B f p)
    (Affine.diagonal R B ((Spec.map (CommRingCat.ofHom f.toRingHom)) p)) (by
      exact (congrArg (fun k : Spec (CommRingCat.of A) ⟶
          _root_.AlgebraicGeometry.Scheme.Diagonal.Affine.product R B => k p)
        (graph_middlePair R σ A B f h)).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The same actual diagonal kernel list has regular images in the actual affine graph stalk. -/
theorem etale_common_regular_list [Algebra.Etale (MvPolynomial σ R) B]
    (p : PrimeSpectrum A) (l : List σ) (hl : l.Nodup) (hcover : ∀ i, i ∈ l) :
    ∃ rs : List ((_root_.AlgebraicGeometry.Scheme.Diagonal.Affine.product R B).presheaf.stalk
      (Affine.diagonal R B ((Spec.map (CommRingCat.ofHom f.toRingHom)) p))),
      IsRegular ((_root_.AlgebraicGeometry.Scheme.Diagonal.Affine.product R B).presheaf.stalk
        (Affine.diagonal R B ((Spec.map (CommRingCat.ofHom f.toRingHom)) p))) rs ∧
      RingHom.ker ((Affine.diagonal R B).stalkMap
        ((Spec.map (CommRingCat.ofHom f.toRingHom)) p)).hom = Ideal.ofList rs ∧
      IsRegular ((product R A B).presheaf.stalk (graph R σ A B f p))
        (rs.map (diagonalStalkMap R σ A B f h p).hom) := by
  let i := Affine.diagonal R B
  let q := middlePair (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (Spec.map (CommRingCat.ofHom f.toRingHom)) h
  let i' := Spec.map (CommRingCat.ofHom (RelativePolynomial.multiplication R B))
  let q' := Spec.map
    (CommRingCat.ofHom (PolynomialGraph.diagonalPullback R σ A B f).toRingHom)
  let d := p.comap (f : B →+* A)
  let z := PolynomialTensor.graphPoint R σ A B f p
  let t := PolynomialTensor.diagonalPoint R σ A B f p
  have hi : i' ≫ (pullbackSpecIso R B B).inv = (𝟙 (Spec (CommRingCat.of B))) ≫ i := by
    simpa only [Category.id_comp] using (diagonal_SpecMap R B).symm
  have hq : q' ≫ (pullbackSpecIso R B B).inv = (pullbackSpecIso R A B).inv ≫ q :=
    spec_diagonalPullback_square R σ A B f h
  have hdi : t = i' d := rfl
  have hzq : t = q' z := PolynomialTensor.diagonalPoint_eq_comap_graphPoint R σ A B f p
  have hdi' : (pullbackSpecIso R B B).inv t = i ((𝟙 (Spec (CommRingCat.of B))) d) := by
    change (i' ≫ (pullbackSpecIso R B B).inv) d = _
    rw [hi]
    rfl
  have hzq' : (pullbackSpecIso R B B).inv t = q ((pullbackSpecIso R A B).inv z) := by
    rw [hzq]
    change (q' ≫ (pullbackSpecIso R B B).inv) z = _
    rw [hq]
    rfl
  have hlocal := PolynomialTensor.spec_common_regular_list R σ A B f p l hl hcover
  have hlocal' : ∃ rs : List ((Spec (CommRingCat.of (B ⊗[R] B))).presheaf.stalk t),
      IsRegular ((Spec (CommRingCat.of (B ⊗[R] B))).presheaf.stalk t) rs ∧
      RingHom.ker (alignedStalkMap i' d t hdi).hom = Ideal.ofList rs ∧
      IsRegular ((Spec (CommRingCat.of (A ⊗[R] B))).presheaf.stalk z)
        (rs.map (alignedStalkMap q' z t hzq).hom) := by
    have heq : alignedStalkMap i' d t hdi = i'.stalkMap d :=
      alignedStalkMap_rfl i' d
    rw [heq]
    exact hlocal
  have ht := exists_regular_kernel_and_regular_image_of_openCharts i q i' q'
    (𝟙 (Spec (CommRingCat.of B))) (pullbackSpecIso R A B).inv (pullbackSpecIso R B B).inv
    hi hq d z t hdi hzq hdi' hzq' hlocal'
  have htpoint : (pullbackSpecIso R B B).inv t =
      Affine.diagonal R B ((Spec.map (CommRingCat.ofHom f.toRingHom)) p) := hdi'
  have hzpoint : (pullbackSpecIso R A B).inv z = graph R σ A B f p := rfl
  have hzfinal : i ((Spec.map (CommRingCat.ofHom f.toRingHom)) p) =
      q (graph R σ A B f p) :=
    (congrArg (fun k : Spec (CommRingCat.of A) ⟶
        _root_.AlgebraicGeometry.Scheme.Diagonal.Affine.product R B => k p)
      (graph_middlePair R σ A B f h)).symm
  have ht' := common_regular_list_congr_points i q
    ((𝟙 (Spec (CommRingCat.of B))) d) ((Spec.map (CommRingCat.ofHom f.toRingHom)) p)
    ((pullbackSpecIso R A B).inv z) (graph R σ A B f p)
    ((pullbackSpecIso R B B).inv t) (i ((Spec.map (CommRingCat.ofHom f.toRingHom)) p))
    rfl hzpoint htpoint hdi' hzq' rfl hzfinal ht
  simpa only [i, q, diagonalStalkMap, alignedStalkMap_rfl] using ht'

end AlgebraicGeometry.Scheme.Graph.Affine

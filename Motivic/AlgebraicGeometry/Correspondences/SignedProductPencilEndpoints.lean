/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.ProductZeroCycles
public import Motivic.AlgebraicGeometry.Correspondences.DiagonalZeroCycle
public import Motivic.AlgebraicGeometry.Correspondences.PolynomialPencilCycles

/-! # Actual signed product pencils and their original endpoint sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open Motivic.RelativeEndpointDiagram
universe u

namespace Motivic.SignedProductPencilEndpoints

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {C : Scheme.{u}} (p : C ⟶ X.left)
  [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)]
  (L : LineBundle C) (a c : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (g : C ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)

abbrev familySource := Hom.zeroInclusion (familyMap (p ≫ X.hom) L a c) ≫ parameterMap X.hom p
abbrev familyTarget := Hom.zeroInclusion (familyMap (p ≫ X.hom) L a c) ≫ projection (p ≫ X.hom) ≫ g

include h
omit [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)] in
/-- The literal family maps retain the original equation over the ground field. -/
theorem family_base : familySource p L a c ≫ relativeLineHom X.hom =
    familyTarget p L a c g ≫ Y.hom := by
  change (Hom.zeroInclusion _ ≫ parameterMap X.hom p) ≫
      (projection X.hom ≫ X.hom) = _
  rw [Category.assoc, ← Category.assoc (parameterMap X.hom p), parameterMap_projection]
  simp only [familyTarget, Category.assoc, h]

variable [IsFinite (familySource p L a c)] [Flat (familySource p L a c)]

/-- The positive correspondence of the original polynomial family. -/
def familyCorrespondence : Cor.mk (relativeLineSite X) ⟶ Cor.mk Y :=
  Cor.ofFiniteFlatSpan (familySource p L a c) (familyTarget p L a c g) (family_base p L a c g h)

/-- Endpoint graph evaluation is proved using the retained parameter curve,
then forgotten to the actual arbitrary target. -/
theorem graph_family (t : k) :
    (Cor.graphFunctor k).map (endpointMorphism X t) ≫ familyCorrespondence p L a c g h =
      Cor.relativeFiniteFlatSpanEndpoint (familySource p L a c) (familyTarget p L a c g)
        (family_base p L a c g h) t := by
  let R := relativeLineSite (SmoothSite.mk (p ≫ X.hom))
  let i : Hom.zeroScheme (familyMap (p ≫ X.hom) L a c) ⟶ R.left := Hom.zeroInclusion _
  have hi : familySource p L a c ≫ relativeLineHom X.hom = i ≫ R.hom := by
    change (Hom.zeroInclusion _ ≫ parameterMap X.hom p) ≫
      (projection X.hom ≫ X.hom) = Hom.zeroInclusion _ ≫ (projection (p ≫ X.hom) ≫ (p ≫ X.hom))
    rw [Category.assoc, ← Category.assoc (parameterMap X.hom p), parameterMap_projection]
    simp only [Category.assoc]
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (Hom.zeroInclusion _))
  have : IsClosedImmersion (pullback.lift (familySource p L a c) i hi) := by
    have : IsClosedImmersion (pullback.lift (familySource p L a c) i hi ≫
        pullback.snd (relativeLineHom X.hom) R.hom) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd _ _)
  let q : R ⟶ Y := SmoothSite.homMk (projection (p ≫ X.hom) ≫ g) (by
    change (projection (p ≫ X.hom) ≫ g) ≫ Y.hom = projection (p ≫ X.hom) ≫ (p ≫ X.hom)
    rw [Category.assoc, h])
  simpa only [familyCorrespondence, familyTarget, q, i, SmoothSite.homMk_left, Category.assoc] using
    Cor.graph_relative_endpoint_ofFiniteFlatSpan_postcompose (X := X) (Y := R) (Z := Y)
      (familySource p L a c) i hi q t

/-- The zero graph evaluates to the full original zero section. -/
theorem graph_family_zero [IsFinite (Hom.zeroInclusion a ≫ p)] [Flat (Hom.zeroInclusion a ≫ p)] :
    (Cor.graphFunctor k).map (endpointMorphism X 0) ≫ familyCorrespondence p L a c g h =
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ p) (Hom.zeroInclusion a ≫ g)
        (by simp only [Category.assoc, h]) := by
  rw [graph_family]
  exact PolynomialPencilCycles.zero_endpoint_cycle p L a c g h _

/-- The one graph evaluates to the full original one section. -/
theorem graph_family_one [IsFinite (Hom.zeroInclusion c ≫ p)] [Flat (Hom.zeroInclusion c ≫ p)] :
    (Cor.graphFunctor k).map (endpointMorphism X 1) ≫ familyCorrespondence p L a c g h =
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion c ≫ p) (Hom.zeroInclusion c ≫ g)
        (by simp only [Category.assoc, h]) := by
  rw [graph_family]
  exact PolynomialPencilCycles.one_endpoint_cycle p L a c g h _

variable {N : C.Modules} (d : N ⟶ SheafOfModules.unit C.ringCatSheaf)
  [IsFinite (Hom.zeroInclusion d ≫ p)] [Flat (Hom.zeroInclusion d ≫ p)]

/-- Subtract the constant original pole divisor, not the whole zero endpoint. -/
def signedCorrespondence : Cor.mk (relativeLineSite X) ⟶ Cor.mk Y :=
  familyCorrespondence p L a c g h -
    (show Cor.mk (relativeLineSite X) ⟶ Cor.mk Y from
      (Cor.graphFunctor k).map (GlobalBoundaryPencil.projectionMorphism X) ≫
        Cor.ofFiniteFlatSpan (X := X) (Y := Y)
          (Hom.zeroInclusion d ≫ p) (Hom.zeroInclusion d ≫ g)
          (by simp only [Category.assoc, h]))

/-- The signed zero endpoint retains both original full zero schemes. -/
theorem signed_zero [IsFinite (Hom.zeroInclusion a ≫ p)] [Flat (Hom.zeroInclusion a ≫ p)] :
    (Cor.graphFunctor k).map (endpointMorphism X 0) ≫ signedCorrespondence p L a c g h d =
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ p) (Hom.zeroInclusion a ≫ g)
        (by simp only [Category.assoc, h]) -
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion d ≫ p) (Hom.zeroInclusion d ≫ g)
        (by simp only [Category.assoc, h]) := by
  rw [signedCorrespondence, Preadditive.comp_sub, graph_family_zero,
    ← Category.assoc, ← Functor.map_comp, GlobalBoundaryPencil.endpoint_projection,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The signed one endpoint is the original numerator divisor minus pole divisor. -/
theorem signed_one [IsFinite (Hom.zeroInclusion c ≫ p)] [Flat (Hom.zeroInclusion c ≫ p)] :
    (Cor.graphFunctor k).map (endpointMorphism X 1) ≫ signedCorrespondence p L a c g h d =
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion c ≫ p) (Hom.zeroInclusion c ≫ g)
        (by simp only [Category.assoc, h]) -
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion d ≫ p) (Hom.zeroInclusion d ≫ g)
        (by simp only [Category.assoc, h]) := by
  rw [signedCorrespondence, Preadditive.comp_sub, graph_family_one,
    ← Category.assoc, ← Functor.map_comp, GlobalBoundaryPencil.endpoint_projection,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Motivic.SignedProductPencilEndpoints

namespace Motivic.SignedProductPencilEndpoints

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {C : Scheme.{u}} (p : C ⟶ X.left)
  [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)]
  (L M : LineBundle C)
  (s : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (d : M.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono s] [Mono d]
  (c : (tensorLineBundle C L M).val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (g : C ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)
  [IsFinite (Hom.zeroInclusion s ≫ p)] [Flat (Hom.zeroInclusion s ≫ p)]
  [IsFinite (Hom.zeroInclusion d ≫ p)] [Flat (Hom.zeroInclusion d ≫ p)]
  [IsFinite (familySource p (tensorLineBundle C L M) (Hom.productSection s d) c)]
  [Flat (familySource p (tensorLineBundle C L M) (Hom.productSection s d) c)]

/-- The actual product section supplies and cancels the constant pole divisor.
No endpoint-cycle identity is assumed. -/
theorem signed_product_zero :
    (Cor.graphFunctor k).map (endpointMorphism X 0) ≫
      signedCorrespondence p (tensorLineBundle C L M) (Hom.productSection s d) c g h d =
        Cor.ofFiniteFlatSpan (Hom.zeroInclusion s ≫ p) (Hom.zeroInclusion s ≫ g)
          (by simp only [Category.assoc, h]) := by
  have hz := PolynomialPencilCycles.zero_finite_flat X.hom p
    (tensorLineBundle C L M) (Hom.productSection s d) c
  let := hz.1
  let := hz.2
  rw [signed_zero, ProductZeroCycles.ofFiniteFlatSpan_productSection L M s d p g h,
    add_sub_cancel_right]

end Motivic.SignedProductPencilEndpoints

namespace Motivic.SignedProductPencilEndpoints

/-- The actual diagonal-product polynomial pencil, minus the constant pole,
evaluates at zero to the original graph. The entire family and all zero schemes
are retained; the graph endpoint is a conclusion, not an input. -/
theorem signed_diagonal_zero {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
    (p : C ⟶ X.left)
    [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)]
    (j : X.left ⟶ C) [IsClosedImmersion j] (hp : j ≫ p = 𝟙 X.left)
    (hI : IsLocallyRankOne C (Scheme.Hom.idealModule j))
    (M : LineBundle C) (d : M.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono d]
    (c : (tensorLineBundle C ⟨Scheme.Hom.idealModule j, hI⟩ M).val ⟶
      SheafOfModules.unit C.ringCatSheaf)
    (g : C ⟶ Y.left) (φ : X ⟶ Y) (hg : j ≫ g = φ.left)
    (h : p ≫ X.hom = g ≫ Y.hom)
    [IsFinite (Hom.zeroInclusion d ≫ p)] [Flat (Hom.zeroInclusion d ≫ p)]
    [IsFinite (familySource p (tensorLineBundle C ⟨Scheme.Hom.idealModule j, hI⟩ M)
      (Hom.productSection (Scheme.Hom.idealInclusion j) d) c)]
    [Flat (familySource p (tensorLineBundle C ⟨Scheme.Hom.idealModule j, hI⟩ M)
      (Hom.productSection (Scheme.Hom.idealInclusion j) d) c)] :
    (Cor.graphFunctor k).map (endpointMorphism X 0) ≫
      signedCorrespondence p (tensorLineBundle C ⟨Scheme.Hom.idealModule j, hI⟩ M)
        (Hom.productSection (Scheme.Hom.idealInclusion j) d) c g h d =
      (Cor.graphFunctor k).map φ := by
  let J : LineBundle C := ⟨Scheme.Hom.idealModule j, hI⟩
  let : (Scheme.Hom.idealModule j).IsLocallyFree := lineBundle_isLocallyFree C J
  let : Mono (show J.val ⟶ SheafOfModules.unit C.ringCatSheaf from
      Scheme.Hom.idealInclusion j) := Scheme.Hom.idealInclusionMono j
  have hj := DiagonalZeroCycle.zeroIdealInclusion_finite_flat j p hp
  let := hj.1
  let := hj.2
  exact (signed_product_zero p J M (Scheme.Hom.idealInclusion j) d c g h).trans
    (DiagonalZeroCycle.canonicalSection_zero_graph j p hp g φ hg h)

end Motivic.SignedProductPencilEndpoints

namespace Motivic.SignedProductPencilEndpoints

/-- The one endpoint uses the actual numerator factors after the specified
line-bundle isomorphism, rather than a presumed equality of divisor cycles. -/
theorem signed_one_product {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
    (p : C ⟶ X.left)
    [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)]
    (L A N M : LineBundle C)
    (a0 : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (a : A.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (n : N.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono a] [Mono n]
    (e : L.val ≅ (tensorLineBundle C A N).val)
    (d : M.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (g : C ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)
    [IsFinite (Hom.zeroInclusion a ≫ p)] [Flat (Hom.zeroInclusion a ≫ p)]
    [IsFinite (Hom.zeroInclusion n ≫ p)] [Flat (Hom.zeroInclusion n ≫ p)]
    [IsFinite (Hom.zeroInclusion d ≫ p)] [Flat (Hom.zeroInclusion d ≫ p)]
    [IsFinite (familySource p L a0 (e.hom ≫ Hom.productSection a n))]
    [Flat (familySource p L a0 (e.hom ≫ Hom.productSection a n))] :
    (Cor.graphFunctor k).map (endpointMorphism X 1) ≫
      signedCorrespondence p L a0 (e.hom ≫ Hom.productSection a n) g h d =
      (Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ p) (Hom.zeroInclusion a ≫ g)
          (by simp only [Category.assoc, h]) +
        Cor.ofFiniteFlatSpan (Hom.zeroInclusion n ≫ p) (Hom.zeroInclusion n ≫ g)
          (by simp only [Category.assoc, h])) -
        Cor.ofFiniteFlatSpan (Hom.zeroInclusion d ≫ p) (Hom.zeroInclusion d ≫ g)
          (by simp only [Category.assoc, h]) := by
  have hc := PolynomialPencilCycles.one_finite_flat X.hom p L a0 (e.hom ≫ Hom.productSection a n)
  let := hc.1
  let := hc.2
  let E := zeroSchemePrecompIso e (Hom.productSection a n)
  have he : E.hom ≫ (Hom.zeroInclusion (Hom.productSection a n) ≫ p) =
      Hom.zeroInclusion (e.hom ≫ Hom.productSection a n) ≫ p := by
    simp only [E, zeroSchemePrecompIso_hom_inclusion_assoc]
  have hi : Hom.zeroInclusion (Hom.productSection a n) ≫ p =
      E.inv ≫ (Hom.zeroInclusion (e.hom ≫ Hom.productSection a n) ≫ p) := by
    rw [← he, E.inv_hom_id_assoc]
  have : IsFinite (Hom.zeroInclusion (Hom.productSection a n) ≫ p) := by
    rw [hi]
    infer_instance
  have : Flat (Hom.zeroInclusion (Hom.productSection a n) ≫ p) := by
    rw [hi]
    infer_instance
  rw [signed_one]
  have hs : Cor.ofFiniteFlatSpan (X := X) (Y := Y)
      (Hom.zeroInclusion (e.hom ≫ Hom.productSection a n) ≫ p)
      (Hom.zeroInclusion (e.hom ≫ Hom.productSection a n) ≫ g)
      (by simp only [Category.assoc, h]) =
      Cor.ofFiniteFlatSpan (Hom.zeroInclusion (Hom.productSection a n) ≫ p)
        (Hom.zeroInclusion (Hom.productSection a n) ≫ g)
        (by simp only [Category.assoc, h]) := by
    apply PolynomialPencilCycles.span_eq_of_iso E
    · exact he
    · simp only [E, zeroSchemePrecompIso_hom_inclusion_assoc]
  rw [hs, ProductZeroCycles.ofFiniteFlatSpan_productSection A N a n p g h]

end Motivic.SignedProductPencilEndpoints

namespace Motivic.SignedProductPencilEndpoints

/-- With the actual pole `b*d`, the endpoint has the correction sign
`(Z(a)-Z(b))-(Z(d)-Z(n))`. The four zero correspondences are all original spans. -/
theorem signed_one_four_sections {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
    (p : C ⟶ X.left)
    [Smooth (p ≫ X.hom)] [IsSeparated (p ≫ X.hom)] [QuasiCompact (p ≫ X.hom)]
    (L A N B D : LineBundle C)
    (a0 : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (a : A.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (n : N.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (b : B.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (d : D.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [Mono a] [Mono n] [Mono b] [Mono d]
    (e : L.val ≅ (tensorLineBundle C A N).val)
    (g : C ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)
    [IsFinite (Hom.zeroInclusion a ≫ p)] [Flat (Hom.zeroInclusion a ≫ p)]
    [IsFinite (Hom.zeroInclusion n ≫ p)] [Flat (Hom.zeroInclusion n ≫ p)]
    [IsFinite (Hom.zeroInclusion b ≫ p)] [Flat (Hom.zeroInclusion b ≫ p)]
    [IsFinite (Hom.zeroInclusion d ≫ p)] [Flat (Hom.zeroInclusion d ≫ p)]
    [IsFinite (Hom.zeroInclusion (Hom.productSection b d) ≫ p)]
    [Flat (Hom.zeroInclusion (Hom.productSection b d) ≫ p)]
    [IsFinite (familySource p L a0 (e.hom ≫ Hom.productSection a n))]
    [Flat (familySource p L a0 (e.hom ≫ Hom.productSection a n))] :
    (Cor.graphFunctor k).map (endpointMorphism X 1) ≫
      signedCorrespondence p L a0 (e.hom ≫ Hom.productSection a n) g h
        (Hom.productSection b d) =
      (Cor.ofFiniteFlatSpan (Hom.zeroInclusion a ≫ p) (Hom.zeroInclusion a ≫ g)
          (by simp only [Category.assoc, h]) -
        Cor.ofFiniteFlatSpan (Hom.zeroInclusion b ≫ p) (Hom.zeroInclusion b ≫ g)
          (by simp only [Category.assoc, h])) -
      (Cor.ofFiniteFlatSpan (Hom.zeroInclusion d ≫ p) (Hom.zeroInclusion d ≫ g)
          (by simp only [Category.assoc, h]) -
        Cor.ofFiniteFlatSpan (Hom.zeroInclusion n ≫ p) (Hom.zeroInclusion n ≫ g)
          (by simp only [Category.assoc, h])) := by
  rw [signed_one_product p L A N (tensorLineBundle C B D) a0 a n e
    (Hom.productSection b d) g h,
    ProductZeroCycles.ofFiniteFlatSpan_productSection B D b d p g h]
  abel

end Motivic.SignedProductPencilEndpoints

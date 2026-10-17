/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.TensorProduct.GraphPullback
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual affine graph stalks in étale polynomial coordinates

The scheme map defined by tensor graph evaluation has the identity and the
original morphism as its two projections, so it is the actual affine graph.
Its stalk map is identified with localized graph evaluation. The explicit
coordinate differences therefore generate its kernel and form a regular list,
with no flatness, reducedness, or connectedness condition on the graph source.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open RingTheory.Sequence

universe u v

namespace Motivic.AffineGraph

variable (R : Type u) (σ : Type v) (A B : Type u)
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra (MvPolynomial σ R) B] [IsScalarTower R (MvPolynomial σ R) B]
  (f : B →ₐ[MvPolynomial σ R] A)

/-- The actual affine product containing the graph. -/
abbrev product : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))

/-- The actual graph morphism, expressed through tensor evaluation. -/
def graph : Spec (CommRingCat.of A) ⟶ product R A B :=
  Spec.map (CommRingCat.ofHom (PolynomialTensorGraph.evaluation R σ A B f).toRingHom) ≫
    (pullbackSpecIso R A B).inv

@[reassoc (attr := simp)]
theorem graph_fst : graph R σ A B f ≫ pullback.fst _ _ = 𝟙 _ := by
  simp only [graph, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  change PolynomialTensorGraph.evaluation R σ A B f (a ⊗ₜ[R] 1) = a
  simp

@[reassoc (attr := simp)]
theorem graph_snd :
    graph R σ A B f ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom f.toRingHom) := by
  simp only [graph, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  ext b
  change PolynomialTensorGraph.evaluation R σ A B f (1 ⊗ₜ[R] b) = f b
  simp

/-- The explicit affine map is the unique actual graph determined by its projections. -/
theorem graph_eq_lift
    (h : (𝟙 (Spec (CommRingCat.of A))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    graph R σ A B f = pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom f.toRingHom)) h := by
  apply pullback.hom_ext
  · exact (graph_fst R σ A B f).trans (pullback.lift_fst _ _ _).symm
  · exact (graph_snd R σ A B f).trans (pullback.lift_snd _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual graph stalk map is isomorphic to localized tensor graph evaluation. -/
def arrowStalkIso (p : PrimeSpectrum A) :
    Arrow.mk ((graph R σ A B f).stalkMap p) ≅
      Arrow.mk (CommRingCat.ofHom (PolynomialTensorGraph.localEvaluation R σ A B f p.asIdeal)) := by
  unfold graph
  refine (Arrow.isoMk
    (g := Arrow.mk ((Spec.map (CommRingCat.ofHom
      (PolynomialTensorGraph.evaluation R σ A B f).toRingHom)).stalkMap p))
    (asIso ((pullbackSpecIso R A B).inv.stalkMap
      ((Spec.map (CommRingCat.ofHom
        (PolynomialTensorGraph.evaluation R σ A B f).toRingHom)) p)))
    (Iso.refl _) ?_) ≪≫
      Scheme.arrowStalkMapSpecIso
        (CommRingCat.ofHom (PolynomialTensorGraph.evaluation R σ A B f).toRingHom) p
  simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id, asIso_hom,
    Scheme.Hom.stalkMap_comp]

/-- The actual graph ambient stalk is the corresponding tensor localization. -/
def stalkEquiv (p : PrimeSpectrum A) :
    (product R A B).presheaf.stalk (graph R σ A B f p) ≃+*
      Localization.AtPrime (PolynomialTensorGraph.graphPrime R σ A B f p.asIdeal) :=
  (Arrow.leftFunc.mapIso (arrowStalkIso R σ A B f p)).commRingCatIsoToRingEquiv

/-- The source affine stalk is the localization of its coefficient ring. -/
def sourceStalkEquiv (p : PrimeSpectrum A) :
    (Spec (CommRingCat.of A)).presheaf.stalk p ≃+* Localization.AtPrime p.asIdeal :=
  (Arrow.rightFunc.mapIso (arrowStalkIso R σ A B f p)).commRingCatIsoToRingEquiv

/-- The concrete equivalences intertwine the actual graph stalk and local evaluation. -/
theorem localEvaluation_stalkEquiv (p : PrimeSpectrum A)
    (x : (product R A B).presheaf.stalk (graph R σ A B f p)) :
    PolynomialTensorGraph.localEvaluation R σ A B f p.asIdeal (stalkEquiv R σ A B f p x) =
      sourceStalkEquiv R σ A B f p ((graph R σ A B f).stalkMap p x) :=
  ConcreteCategory.congr_hom (arrowStalkIso R σ A B f p).hom.w x

/-- The actual graph stalk kernel is the inverse image of the actual localized graph kernel. -/
theorem ker_stalkMap (p : PrimeSpectrum A) :
    RingHom.ker ((graph R σ A B f).stalkMap p).hom =
      (RingHom.ker (PolynomialTensorGraph.localEvaluation R σ A B f p.asIdeal)).comap
        (stalkEquiv R σ A B f p) := by
  ext x
  change ((graph R σ A B f).stalkMap p).hom x = 0 ↔
    PolynomialTensorGraph.localEvaluation R σ A B f p.asIdeal (stalkEquiv R σ A B f p x) = 0
  rw [localEvaluation_stalkEquiv]
  exact (sourceStalkEquiv R σ A B f p).map_eq_zero_iff.symm

/-- A literal graph coordinate difference in the actual ambient scheme stalk. -/
def stalkDifference (p : PrimeSpectrum A) (i : σ) :
    (product R A B).presheaf.stalk (graph R σ A B f p) :=
  (stalkEquiv R σ A B f p).symm (PolynomialTensorGraph.localDifference R σ A B f p.asIdeal i)

@[simp]
theorem stalkEquiv_stalkDifference (p : PrimeSpectrum A) (i : σ) :
    stalkEquiv R σ A B f p (stalkDifference R σ A B f p i) =
      PolynomialTensorGraph.localDifference R σ A B f p.asIdeal i :=
  (stalkEquiv R σ A B f p).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The explicit graph differences form a regular list in the actual product stalk. -/
theorem isRegular_stalkDifferences [Module.Flat (MvPolynomial σ R) B]
    (p : PrimeSpectrum A) (l : List σ) (hl : l.Nodup) :
    IsRegular ((product R A B).presheaf.stalk (graph R σ A B f p))
      (l.map (stalkDifference R σ A B f p)) := by
  let e := (stalkEquiv R σ A B f p).symm
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm
    (e : Localization.AtPrime (PolynomialTensorGraph.graphPrime R σ A B f p.asIdeal) →+*
      (product R A B).presheaf.stalk (graph R σ A B f p))
    (e.symm : (product R A B).presheaf.stalk (graph R σ A B f p) →+*
      Localization.AtPrime (PolynomialTensorGraph.graphPrime R σ A B f p.asIdeal))
  have h := (e.toSemilinearEquiv.isRegular_congr'
    (l.map (PolynomialTensorGraph.localDifference R σ A B f p.asIdeal))).mp
      (PolynomialTensorGraph.isRegular_localDifferences R σ A B f p.asIdeal l hl)
  convert! h using 1
  simp only [List.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The explicit graph differences generate the actual graph stalk kernel. -/
theorem ker_stalkMap_eq_ofList [Algebra.Etale (MvPolynomial σ R) B]
    (p : PrimeSpectrum A) (l : List σ) (hcover : ∀ i, i ∈ l) :
    RingHom.ker ((graph R σ A B f).stalkMap p).hom =
      Ideal.ofList (l.map (stalkDifference R σ A B f p)) := by
  rw [ker_stalkMap, PolynomialTensorGraph.ker_localEvaluation_eq_ofList
    R σ A B f p.asIdeal l hcover, ← Ideal.map_symm (stalkEquiv R σ A B f p)]
  change (Ideal.ofList (l.map (PolynomialTensorGraph.localDifference R σ A B f p.asIdeal))).map
    (stalkEquiv R σ A B f p).symm.toRingHom = _
  rw [Ideal.map_ofList]
  simp only [List.map_map]
  rfl

/-- Étale coordinates give an explicit regular presentation of the actual graph stalk kernel. -/
theorem etale_stalkPresentation [Algebra.Etale (MvPolynomial σ R) B]
    (p : PrimeSpectrum A) (l : List σ) (hl : l.Nodup) (hcover : ∀ i, i ∈ l) :
    IsRegular ((product R A B).presheaf.stalk (graph R σ A B f p))
      (l.map (stalkDifference R σ A B f p)) ∧
    RingHom.ker ((graph R σ A B f).stalkMap p).hom =
      Ideal.ofList (l.map (stalkDifference R σ A B f p)) :=
  ⟨isRegular_stalkDifferences R σ A B f p l hl,
    ker_stalkMap_eq_ofList R σ A B f p l hcover⟩

end Motivic.AffineGraph

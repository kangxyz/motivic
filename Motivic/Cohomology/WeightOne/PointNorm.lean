/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.ReducedTorus
public import Motivic.AlgebraicGeometry.Correspondences.Generators.BaseField
public import Aglib.RingTheory.FiniteAlgebraNormLength
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The determinant norm on actual weight-one point cycles

Each integral finite support over `Spec k` has its literal finite field of global
sections. The Laurent coordinate is pulled back through the actual support
projection and the first coordinate of the canonical one-fold torus power.
The existing determinant norm extends over signed geometric cycles.

This file concerns degree-zero cycles and the identity-axis quotient only.
It does not assert that singular boundaries vanish or compute motivic cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.WeightOnePointNorm
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

private instance baseIntegral : IsIntegral ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

/-- The actual source point in the correspondence category. -/
abbrev point : Cor k := Cor.mk (SmoothSite.base (Spec (.of k)))

/-- The canonical one-fold product used in `reducedTorus k 1`. -/
abbrev target : Cor k := Cor.mk (SmoothSite.torusPower (.of k) 1)

/-- The geometric generators of the actual degree-zero cycle group. -/
abbrev Generator := FiniteCorrespondenceGenerator
  (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 1).hom

variable {k} (Z : Generator k)

/-- The coordinate ring of the whole finite integral support. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(Z.scheme, ⊤)

/-- The entire actual support is affine because its source projection is finite. -/
instance supportAffine : IsAffine Z.scheme := by
  let : IsAffine ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  exact isAffine_of_isAffineHom Z.projection

/-- The support is the spectrum of its actual whole coordinate ring. -/
def supportIsoSpec : Z.scheme ≅ Spec (coordinateRing Z) := Z.scheme.isoSpec

/-- The scalar map is induced by the literal finite source projection. -/
def scalarMap : k →+* coordinateRing Z :=
  (Z.projection.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

instance coordinateAlgebra : Algebra k (coordinateRing Z) := (scalarMap Z).toAlgebra

/-- The whole support coordinate algebra is finite over the base field. -/
instance coordinateFinite : Module.Finite k (coordinateRing Z) := by
  let : IsAffine ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  change (scalarMap Z).Finite
  exact Z.projection.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- Integrality and finite projection make this actual coordinate algebra a field. -/
theorem coordinateRing_isField : IsField (coordinateRing Z) :=
  isField_of_universallyClosed k Z.projection

/-- The genuine Laurent coordinate on the support, through the canonical product coordinate. -/
def coordinateUnit : (coordinateRing Z)ˣ :=
  Units.map ((Z.targetProjection ≫
    (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k))

/-- The ordinary determinant field norm of the actual support coordinate. -/
def generatorNorm : kˣ := Units.map (Algebra.norm k) (coordinateUnit Z)

@[simp] theorem generatorNorm_val :
    (generatorNorm Z : k) = Algebra.norm k (coordinateUnit Z : coordinateRing Z) := rfl

variable (k)

/-- Norm on the literal signed point cycles, with integer multiplicities. -/
def cycleNorm : (point k ⟶ target k) →+ Additive kˣ :=
  Finsupp.liftAddHom fun Z => zmultiplesHom _ (Additive.ofMul (generatorNorm Z))

variable {k}

/-- An actual support with signed multiplicity is sent to the corresponding signed norm. -/
@[simp] theorem cycleNorm_single (Z : Generator k) (n : ℤ) :
    cycleNorm k (Finsupp.single Z n) = n • Additive.ofMul (generatorNorm Z) :=
  Finsupp.liftAddHom_apply_single _ _ _

@[simp] theorem cycleNorm_cycle (Z : Generator k) :
    cycleNorm k Z.cycle = Additive.ofMul (generatorNorm Z) := by
  change cycleNorm k (Finsupp.single Z 1) = _
  rw [cycleNorm_single, one_zsmul]

/-- The canonical coordinate of a rational point, in the original base field. -/
def rationalCoordinate (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 1) : kˣ :=
  Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom
    (Units.map ((φ.left ≫ (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k)))

/-- The actual graph generator on the specified field base. -/
abbrev graphSupport (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 1) : Generator k :=
  graphGeneratorOver (X := Spec (.of k)) φ.left (MorphismProperty.Over.w φ)

/-- A graph has degree one for the literal support scalar map. -/
theorem graph_finrank (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 1) :
    Module.finrank k (coordinateRing (graphSupport φ)) = 1 := by
  apply Module.finrank_of_bijective_algebraMap
  change Function.Bijective (scalarMap (graphSupport φ))
  exact (asIso (graphSupport φ).projection.appTop).commRingCatIsoToRingEquiv.bijective.comp
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective

/-- On an actual graph the pulled-back coordinate is the scalar rational coordinate. -/
theorem graph_coordinate (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 1) :
    (coordinateUnit (graphSupport φ) :
      coordinateRing (graphSupport φ)) =
      algebraMap k _ (rationalCoordinate φ : k) := by
  change ((graphSupport φ).targetProjection ≫
    (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop ((laurentGlobalUnit (.of k)).val) =
    (scalarMap (graphSupport φ)) (rationalCoordinate φ : k)
  rw [← graphGeneratorOver_projection_target, Category.assoc, Scheme.Hom.comp_appTop]
  change _ = (graphSupport φ).projection.appTop
    ((Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom
      ((φ.left ≫ (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop
        ((laurentGlobalUnit (.of k)).val))))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
  rfl

/-- The determinant norm of the actual graph support is exactly its rational unit. -/
@[simp] theorem generatorNorm_graph (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 1) :
    generatorNorm (graphSupport φ) =
      rationalCoordinate φ := by
  apply Units.ext
  rw [generatorNorm_val, graph_coordinate, Algebra.norm_algebraMap, graph_finrank, pow_one]

/-- The actual correspondence-category graph has its prescribed norm. -/
@[simp] theorem cycleNorm_graph (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 1) :
    cycleNorm k ((Cor.graphFunctor k).map φ) = Additive.ofMul (rationalCoordinate φ) := by
  let : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  rw [Cor.graphFunctor_map, componentGraphCycleOver_eq_graphGeneratorOver_cycle,
    cycleNorm_cycle, generatorNorm_graph]

variable (k)

/-- The Laurent-evaluation point of the actual affine torus. -/
def rationalTorusPoint (a : kˣ) :
    SmoothSite.base (Spec (.of k)) ⟶ SmoothSite.torus (.of k) :=
  SmoothSite.homMk
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a))) (by
      change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of k))
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext r
      exact LaurentPolynomial.eval₂_C _ _ _)

/-- A unit determines its literal Laurent-evaluation section of the canonical torus power. -/
def rationalPoint (a : kˣ) : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 1 :=
  SmoothSite.torusPowerLift (.of k) 1 (fun _ => rationalTorusPoint k a)

variable {k}

/-- Evaluating the global coordinate along the section recovers the input unit. -/
@[simp] theorem rationalCoordinate_rationalPoint (a : kˣ) :
    rationalCoordinate (rationalPoint k a) = a := by
  apply Units.ext
  have hc : (rationalPoint k a).left ≫ (SmoothSite.torusCoordinate (.of k) 1 0).left =
      (rationalTorusPoint k a).left := congrArg (fun f => f.left)
        (SmoothSite.torusPowerLift_coordinate (.of k) 1 (fun _ => rationalTorusPoint k a) 0)
  change (Scheme.ΓSpecIso (.of k)).hom
    (((rationalPoint k a).left ≫ (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop
      ((laurentGlobalUnit (.of k)).val)) = (a : k)
  rw [hc]
  change (Scheme.ΓSpecIso (.of k)).hom
    ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) = _
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a))).symm
        (LaurentPolynomial.T 1)
  change (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a))).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1)) =
    (Scheme.ΓSpecIso (.of k)).inv
      (LaurentPolynomial.eval₂ (RingHom.id k) a (LaurentPolynomial.T 1)) at h
  rw [h]
  simp [LaurentPolynomial.eval₂_T]

/-- The literal graph of a unit has norm that unit, with no inverse or degree-zero sign. -/
@[simp] theorem cycleNorm_graph_unit (a : kˣ) :
    cycleNorm k ((Cor.graphFunctor k).map (rationalPoint k a)) = Additive.ofMul a := by
  rw [cycleNorm_graph, rationalCoordinate_rationalPoint]

/-- The actual inserted identity coordinate evaluates to the unit one. -/
@[simp] theorem rationalCoordinate_identityAxis :
    rationalCoordinate (SmoothSite.torusInsertOne (.of k) 0 0) = 1 := by
  apply Units.ext
  change (Scheme.ΓSpecIso (.of k)).hom
    (((SmoothSite.torusInsertOne (.of k) 0 0).left ≫
      (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop
      ((laurentGlobalUnit (.of k)).val)) = 1
  rw [SmoothSite.torusInsertOne_left_coordinate_self]
  change (Scheme.ΓSpecIso (.of k)).hom
    ((𝟙 (Spec (.of k)) ≫ laurentOneSection (.of k)).appTop
      ((laurentGlobalUnit (.of k)).val)) = 1
  rw [Category.id_comp, laurentOneSection_appTop_coordinate]
  exact map_one _

/-- Every actual signed cycle in the identity-axis image has trivial norm. -/
theorem cycleNorm_identityAxis (α : point k ⟶ point k) :
    cycleNorm k (α ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0)) = 0 := by
  obtain ⟨n, hn, _⟩ := Cor.base_endomorphism_existsUnique_zsmul_id α
  rw [hn, Preadditive.zsmul_comp, Category.id_comp, map_zsmul, cycleNorm_graph,
    rationalCoordinate_identityAxis]
  exact smul_zero n

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

variable (k)

/-- The same norm on the genuine universe-lifted representable sections. -/
def largeCycleNorm : sections (torusRepresentable k 1) (point k) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (Additive kˣ)) :=
  AddCommGrpCat.ofHom
    { toFun := fun α => ULift.up (cycleNorm k α.down)
      map_zero' := by change ULift.up ((cycleNorm k) 0) = ULift.up 0; rw [map_zero]
      map_add' := by
        intro α β
        change ULift.up ((cycleNorm k) (α.down + β.down)) =
          ULift.up ((cycleNorm k) α.down + (cycleNorm k) β.down)
        rw [map_add] }

/-- The defining actual relation morphism is annihilated at the field base. -/
theorem relation_largeCycleNorm :
    (torusRelation k 1).app (op (point k)) ≫ largeCycleNorm k = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change largeCycleNorm k ((torusRelation k 1).app (op (point k)) s) = 0
  rw [torusRelation_app_apply, Fin.sum_univ_one]
  change ULift.up (cycleNorm k (_ ≫
    (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0))) = ULift.up 0
  rw [cycleNorm_identityAxis]

/-- The objectwise norm descended through the actual reduced-torus cokernel. -/
def reducedNormLarge : sections (reducedTorus k 1) (point k) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (Additive kˣ)) :=
  (PreservesCokernel.iso
      ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (point k))) (torusRelation k 1)).hom ≫
    cokernel.desc ((torusRelation k 1).app (op (point k)))
      (largeCycleNorm k) (relation_largeCycleNorm k)

/-- This descent extends the original signed cycle norm along the literal quotient map. -/
@[reassoc (attr := simp)] theorem toReducedTorus_reducedNormLarge :
    (toReducedTorus k 1).hom.app (op (point k)) ≫ reducedNormLarge k = largeCycleNorm k := by
  change ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (point k))).map
    (cokernel.π (torusRelation k 1)) ≫ _ = _
  rw [reducedNormLarge, PreservesCokernel.π_iso_hom_assoc]
  exact cokernel.π_desc _ _ _

/-- The norm of an actual reduced point section, valued in the original field's units. -/
def reducedNorm : sections (reducedTorus k 1) (point k) →+ Additive kˣ where
  toFun s := (reducedNormLarge k s).down
  map_zero' := by rw [map_zero]; rfl
  map_add' s t := by rw [map_add]; rfl

variable {k}

/-- The actual quotient retains the original norm formula on every signed cycle. -/
@[simp] theorem reducedNorm_quotient (α : point k ⟶ target k) :
    reducedNorm k ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up α)) =
      cycleNorm k α := by
  have h := ConcreteCategory.congr_hom (toReducedTorus_reducedNormLarge k) (ULift.up α)
  exact congrArg ULift.down h

/-- The class of the graph of a unit has norm that unit in the actual reduced quotient. -/
@[simp] theorem reducedNorm_graph_unit (a : kˣ) :
    reducedNorm k ((toReducedTorus k 1).hom.app (op (point k))
      (ULift.up ((Cor.graphFunctor k).map (rationalPoint k a)))) = Additive.ofMul a := by
  rw [reducedNorm_quotient, cycleNorm_graph_unit]

/-- Every base-field unit is the norm of the corresponding actual graph cycle. -/
theorem cycleNorm_surjective : Function.Surjective (cycleNorm k) := by
  intro a
  exact ⟨(Cor.graphFunctor k).map (rationalPoint k a.toMul), cycleNorm_graph_unit a.toMul⟩

/-- The actual reduced-torus point norm is surjective. No injectivity claim is made here. -/
theorem reducedNorm_surjective : Function.Surjective (reducedNorm k) := by
  intro a
  exact ⟨(toReducedTorus k 1).hom.app (op (point k))
    (ULift.up ((Cor.graphFunctor k).map (rationalPoint k a.toMul))),
      reducedNorm_graph_unit a.toMul⟩

end Motivic.WeightOnePointNorm

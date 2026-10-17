/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalPointNorm
public import Motivic.KTheory.MilnorK.FiniteExtensionNormTower
public import Motivic.AlgebraicGeometry.Cycles.FiniteImageProjection
public import Motivic.Aglib.AlgebraicGeometry.FiniteFieldResidueDegree

/-!
# Evaluation of whole finite points in every diagonal weight

A finite field point need not be a closed immersion into the torus. Its actual
image correspondence carries the original geometric residue degree. The proved
Milnor norm tower law shows that its signed-cycle value is nevertheless the norm
of all original units from the entire original finite point field.

This remains a statement about raw correspondences, not boundary descent.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.DiagonalFinitePointEvaluation

open DiagonalPointNorm KTheory.MilnorK
open AlgebraicGeometry.Scheme.PolynomialLaurent

variable (k : Type u) [Field k]

/-- The original source-target product for all-coordinate point cycles. -/
abbrev ambient (q : ℕ) : Scheme.{u} :=
  pullback (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) q).hom

/-- Each literal Laurent coordinate of the original product. -/
def ambientCoordinate (q : ℕ) (i : Fin q) : ambient k q ⟶ (SmoothSite.torus (.of k)).left :=
  pullback.snd (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) q).hom ≫
    (SmoothSite.torusCoordinate (.of k) q i).left

variable {k} {q : ℕ}

/-- The actual affine pullback of each coordinate to the original point field. -/
def affineCoordinateUnit {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ ambient k q) (i : Fin q) : Rˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom
    (Units.map ((j ≫ ambientCoordinate k q i).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k)))

/-- Literal affine Laurent evaluation recovers the specified original unit. -/
theorem affineCoordinateUnit_of_eval {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ ambient k q) (i : Fin q) (c : k →+* R) (b : Rˣ)
    (h : j ≫ ambientCoordinate k q i =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ c b))) :
    affineCoordinateUnit j i = b := by
  apply Units.ext
  change (Scheme.ΓSpecIso (.of R)).hom
    ((j ≫ ambientCoordinate k q i).appTop (laurentGlobalUnit (.of k)).val) = (b : R)
  rw [h]
  change (Scheme.ΓSpecIso (.of R)).hom
    ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ c b))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) = _
  have he := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (LaurentPolynomial.eval₂ c b))).symm (LaurentPolynomial.T 1)
  change (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ c b))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1)) =
    (Scheme.ΓSpecIso (.of R)).inv
      (LaurentPolynomial.eval₂ c b (LaurentPolynomial.T 1)) at he
  rw [he]
  simp [LaurentPolynomial.eval₂_T]

section FinitePoint

variable {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
  (j : Spec (.of E) ⟶ ambient k q) [IsFinite j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The literal closed image of the finite field point, with its finite base projection. -/
def imageGenerator : Generator k q := by
  have hf : IsFinite (j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom) := by
    rw [hj]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  refine ⟨j.ker, isIntegral_finiteImage j, ?_, ?_⟩
  · exact isFinite_image_projection j _
  · have : Nonempty j.image := ⟨j.toImage (genericPoint (Spec (.of E)))⟩
    have : Subsingleton ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
      inferInstanceAs (Subsingleton (Spec (.of k)))
    have hs : Function.Surjective
        (correspondenceProjection (SmoothSite.base (Spec (.of k))).hom
          (SmoothSite.torusPower (.of k) q).hom j.ker) :=
      Function.surjective_to_subsingleton _
    change Set.range (correspondenceProjection (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom j.ker) ∈ irreducibleComponents (Spec (.of k))
    rw [Set.range_eq_univ.mpr hs]
    exact (irreducibleComponents_eq_singleton (X := Spec (.of k))) ▸ Set.mem_singleton _

/-- The source-to-image map has the original structural scalar map. -/
@[reassoc (attr := simp)]
theorem imageGenerator_toImage_projection :
    j.toImage ≫ (imageGenerator j hj).projection =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  simpa [imageGenerator, FiniteCorrespondenceGenerator.projection,
    correspondenceProjection] using hj

/-- The finite pushforward support is the actual scheme-theoretic image. -/
theorem imageGenerator_support :
    (imageGenerator j hj).toIntegralClosedSubscheme =
      (IntegralClosedSubscheme.pointClosure (genericPoint (Spec (.of E)))).finiteImage j := by
  apply IntegralClosedSubscheme.point_injective
  rw [IntegralClosedSubscheme.point_finiteImage, IntegralClosedSubscheme.point_pointClosure]
  exact imageι_genericPoint j

/-- The whole pushed point includes its full original residue degree. -/
def finitePointCorrespondence : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q :=
  Finsupp.single (imageGenerator j hj) (j.residueDegree (genericPoint (Spec (.of E))) : ℤ)

/-- Forgetting admissibility recovers the original full finite fundamental pushforward. -/
theorem toIntegralCycle_finitePointCorrespondence :
    FiniteCorrespondence.toIntegralCycle (finitePointCorrespondence j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E))) := by
  rw [fundamentalCycle_of_isIntegral, IntegralCycle.finitePushforward_single]
  simp only [finitePointCorrespondence, FiniteCorrespondence.toIntegralCycle_single,
    imageGenerator_support, IntegralClosedSubscheme.point_pointClosure, one_mul]

/-- The original pullback from the image field to the given extension field. -/
def imageScalarMap : coordinateRing (imageGenerator j hj) →+* E :=
  (Scheme.ΓSpecIso (.of E)).hom.hom.comp j.toImage.appTop.hom

/-- This image field action uses the actual map on global sections. -/
instance imageAlgebra : Algebra (coordinateRing (imageGenerator j hj)) E :=
  (imageScalarMap j hj).toAlgebra

/-- The original structural maps commute before any norm or degree is taken. -/
theorem imageScalarMap_comp :
    (imageScalarMap j hj).comp (algebraMap k (coordinateRing (imageGenerator j hj))) =
      algebraMap k E := by
  have h : (j.toImage ≫ (imageGenerator j hj).projection).appTop ≫
      (Scheme.ΓSpecIso (.of E)).hom =
      (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k E) := by
    rw [imageGenerator_toImage_projection, Scheme.ΓSpecIso_naturality]
  apply RingHom.ext
  intro r
  have hv := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of k)).inv r)
  rw [Scheme.Hom.comp_appTop] at hv
  change (Scheme.ΓSpecIso (.of E)).hom
    (j.toImage.appTop ((imageGenerator j hj).projection.appTop
      ((Scheme.ΓSpecIso (.of k)).inv r))) = algebraMap k E r
  change (Scheme.ΓSpecIso (.of E)).hom
    (j.toImage.appTop ((imageGenerator j hj).projection.appTop
      ((Scheme.ΓSpecIso (.of k)).inv r))) =
    algebraMap k E ((Scheme.ΓSpecIso (.of k)).hom
      ((Scheme.ΓSpecIso (.of k)).inv r)) at hv
  simpa only [Iso.inv_hom_id_apply] using hv

instance imageScalarTower : IsScalarTower k (coordinateRing (imageGenerator j hj)) E :=
  IsScalarTower.of_algebraMap_eq' (imageScalarMap_comp j hj).symm

/-- The original Laurent coordinate pulls back along the actual field inclusion. -/
theorem imageScalarMap_coordinate (i : Fin q) :
    imageScalarMap j hj
      (coordinateUnit (imageGenerator j hj) i : coordinateRing (imageGenerator j hj)) =
      (affineCoordinateUnit j i : E) := by
  have h : j.toImage ≫ ((imageGenerator j hj).targetProjection ≫
      (SmoothSite.torusCoordinate (.of k) q i).left) = j ≫ ambientCoordinate k q i := by
    change j.toImage ≫ j.imageι ≫ ambientCoordinate k q i = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  have ha := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ha
  have hv := ConcreteCategory.congr_hom ha
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val
  exact congrArg (fun r => (Scheme.ΓSpecIso (.of E)).hom r) hv

/-- The given extension is finite over the actual image field too. -/
instance imageFinite : Module.Finite (coordinateRing (imageGenerator j hj)) E :=
  Module.Finite.of_restrictScalars_finite k _ _

/-- The source-to-image map becomes exactly the original global-section map
under the canonical affine chart. -/
theorem toImage_isoSpec :
    j.toImage ≫ (imageGenerator j hj).scheme.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (imageScalarMap j hj)) := by
  have h := Scheme.isoSpec_hom_naturality
    (show Spec (.of E) ⟶ (imageGenerator j hj).scheme from j.toImage)
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp] at h
  exact h.symm

/-- The geometric pushforward coefficient is the full degree over the literal
image field, not the degree of the image over the base. -/
theorem residueDegree_eq_image_finrank (x : Spec (.of E)) :
    j.residueDegree x = Module.finrank (coordinateRing (imageGenerator j hj)) E := by
  calc
    j.residueDegree x = j.toImage.residueDegree x := by
      have h := congrArg (fun f => f.residueDegree x) j.toImage_imageι
      rw [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul] at h
      exact h.symm
    _ = (Spec.map (CommRingCat.ofHom (imageScalarMap j hj))).residueDegree x := by
      have h := congrArg (fun f => f.residueDegree x) (toImage_isoSpec j hj)
      have hc := residueDegree_comp
        (show Spec (.of E) ⟶ (imageGenerator j hj).scheme from j.toImage)
        (imageGenerator j hj).scheme.isoSpec.hom x
      rw [residueDegree_of_isIso (imageGenerator j hj).scheme.isoSpec.hom, one_mul] at hc
      exact hc.symm.trans h
    _ = _ := Scheme.Hom.residueDegree_SpecMap_algebraMap
      (coordinateRing (imageGenerator j hj)) E x

/-- Pullback of each original support unit through the literal image-field map. -/
theorem imageScalarMap_coordinateUnit (i : Fin q) :
    Units.map (algebraMap (coordinateRing (imageGenerator j hj)) E).toMonoidHom
      (coordinateUnit (imageGenerator j hj) i) = affineCoordinateUnit j i := by
  apply Units.ext
  exact imageScalarMap_coordinate j hj i

variable [CharZero k]

/-- Restriction to the entire finite point retains the actual degree over
its image field. This uses the proved all-weight Milnor norm tower law. -/
theorem norm_symbol_map_degree (a : Fin q → (coordinateRing (imageGenerator j hj))ˣ) :
    finiteExtensionNorm k E q
      (symbol ((Units.map
        (algebraMap (coordinateRing (imageGenerator j hj)) E).toMonoidHom) ∘ a)) =
      Module.finrank (coordinateRing (imageGenerator j hj)) E •
        finiteExtensionNorm k (coordinateRing (imageGenerator j hj)) q (symbol a) := by
  let : CharZero (coordinateRing (imageGenerator j hj)) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  rw [← map_symbol, finiteExtensionNorm_tower (coordinateRing (imageGenerator j hj)) E,
    finiteExtensionNorm_map_constants, map_smul, natCast_zsmul]

/-- The entire finite point evaluates in its original field, even when its
torus image has a proper residue subfield. The image multiplicity is retained. -/
theorem cycleValue_finitePointCorrespondence :
    cycleValue k q (finitePointCorrespondence j hj) =
      finiteExtensionNorm k E q (symbol (affineCoordinateUnit j)) := by
  unfold finitePointCorrespondence
  rw [cycleValue_single, residueDegree_eq_image_finrank j hj, natCast_zsmul]
  change Module.finrank (coordinateRing (imageGenerator j hj)) E •
    finiteExtensionNorm k (coordinateRing (imageGenerator j hj)) q
      (symbol (coordinateUnit (imageGenerator j hj))) = _
  rw [← norm_symbol_map_degree j hj]
  exact congrArg (fun a => finiteExtensionNorm k E q (symbol a))
    (funext (imageScalarMap_coordinateUnit j hj))

include hj in
/-- A supplied equality of actual finite fundamental cycles computes the
norm in the original finite field, without assuming equality after evaluation. -/
theorem cycleValue_eq_norm_of_finite_fundamental
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleValue k q α = finiteExtensionNorm k E q (symbol (affineCoordinateUnit j)) := by
  have h : α = finitePointCorrespondence j hj :=
    FiniteCorrespondence.toIntegralCycle_injective
      (hα.trans (toIntegralCycle_finitePointCorrespondence j hj).symm)
  rw [h, cycleValue_finitePointCorrespondence]

include hj in
/-- Every coordinate may be specified without replacing the full finite field. -/
theorem cycleValue_eq_norm_units_of_finite_fundamental
    (a : Fin q → Eˣ) (ha : ∀ i, affineCoordinateUnit j i = a i)
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleValue k q α = finiteExtensionNorm k E q (symbol a) := by
  rw [cycleValue_eq_norm_of_finite_fundamental j hj α hα, funext ha]

end FinitePoint

section IdentityAxes

variable [CharZero k]

/-- An actual graph postcomposition retains its complete original support
field, even when the new tuple generates only a proper subfield. -/
theorem cycleValue_cycle_comp_graph {r : ℕ} (Z : Generator k q)
    (ψ : SmoothSite.torusPower (.of k) q ⟶ SmoothSite.torusPower (.of k) r) :
    cycleValue k r (Z.cycle ≫ (Cor.graphFunctor k).map ψ) =
      finiteExtensionNorm k (coordinateRing Z) r
        (symbol (affineCoordinateUnit ((supportIsoSpec Z).inv ≫
          Z.graphPostcompositionMap ψ.left (MorphismProperty.Over.w ψ)))) := by
  let : IsNoetherian ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsNoetherian (Spec (.of k)))
  let : IsNoetherian Z.scheme := isNoetherian_of_finiteType Z.projection
  let j := (supportIsoSpec Z).inv ≫
    Z.graphPostcompositionMap ψ.left (MorphismProperty.Over.w ψ)
  have hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) r).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing Z))) := by
    dsimp only [j]
    rw [Category.assoc, FiniteCorrespondenceGenerator.graphPostcompositionMap_fst,
      supportIsoSpec_inv_projection]
  apply cycleValue_eq_norm_of_finite_fundamental j hj
  have hchart : IntegralCycle.finitePushforward j
      (fundamentalCycle (Spec (coordinateRing Z))) =
      IntegralCycle.finitePushforward
        (Z.graphPostcompositionMap ψ.left (MorphismProperty.Over.w ψ))
        (fundamentalCycle Z.scheme) := by
    dsimp only [j]
    rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
      finitePushforward_fundamentalCycle]
  exact (Z.toIntegralCycle_incidenceTorPairing_componentGraph_right k ψ.left
    (MorphismProperty.Over.w ψ)).trans hchart.symm

omit [CharZero k] in
/-- The inserted coordinate is one on the entire original support field. -/
theorem affineCoordinateUnit_axis (Z : Generator k q) (i : Fin (q + 1)) :
    affineCoordinateUnit (q := q + 1) ((supportIsoSpec Z).inv ≫
      Z.graphPostcompositionMap (SmoothSite.torusInsertOne (.of k) q i).left
        (MorphismProperty.Over.w _)) i = 1 := by
  apply Units.ext
  change (Scheme.ΓSpecIso (coordinateRing Z)).hom
    ((((supportIsoSpec Z).inv ≫
      Z.graphPostcompositionMap (SmoothSite.torusInsertOne (.of k) q i).left
        (MorphismProperty.Over.w _)) ≫ ambientCoordinate k (q + 1) i).appTop
          (laurentGlobalUnit (.of k)).val) = 1
  rw [ambientCoordinate, Category.assoc,
    FiniteCorrespondenceGenerator.graphPostcompositionMap_snd_assoc,
    SmoothSite.torusInsertOne_left_coordinate_self]
  simp only [← Category.assoc]
  change (Scheme.ΓSpecIso (coordinateRing Z)).hom
    ((((supportIsoSpec Z).inv ≫ Z.targetProjection) ≫
      (SmoothSite.torusPower (.of k) q).hom).appTop
        ((laurentOneSection (.of k)).appTop
          (laurentGlobalUnit (.of k) : Γ(Spec (.of (LaurentPolynomial k)), ⊤)))) = 1
  rw [laurentOneSection_appTop_coordinate]
  simp only [map_one]

/-- Every actual finite generator dies after insertion of an identity coordinate. -/
theorem cycleValue_cycle_axis (Z : Generator k q) (i : Fin (q + 1)) :
    cycleValue k (q + 1) (Z.cycle ≫ (Cor.graphFunctor k).map
      (SmoothSite.torusInsertOne (.of k) q i)) = 0 := by
  rw [cycleValue_cycle_comp_graph,
    symbol_eq_zero_of_eq_one _ i (affineCoordinateUnit_axis Z i), map_zero]

/-- The full original identity-axis relation, with arbitrary signed support,
is annihilated before any homology or boundary quotient is formed. -/
theorem cycleValue_axis (i : Fin (q + 1))
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q) :
    cycleValue k (q + 1) (α ≫ (Cor.graphFunctor k).map
      (SmoothSite.torusInsertOne (.of k) q i)) = 0 := by
  classical
  let f : (WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q) →+ K k (q + 1) :=
    (cycleValue k (q + 1)).comp
      (Preadditive.rightComp (WeightOnePointNorm.point k)
        ((Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) q i)))
  change f α = 0
  have hf : f = 0 := by
    apply Finsupp.addHom_ext
    intro Z n
    have hn : Finsupp.single Z n = n • Z.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hn, map_zsmul]
    change n • cycleValue k (q + 1) (Z.cycle ≫ (Cor.graphFunctor k).map
      (SmoothSite.torusInsertOne (.of k) q i)) = 0
    rw [cycleValue_cycle_axis, smul_zero]
  rw [hf, AddMonoidHom.zero_apply]

end IdentityAxes

end Motivic.DiagonalFinitePointEvaluation

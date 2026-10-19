/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteDomainGenericFiber
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.AffineChart
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.FiniteImage
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The whole generic coordinate algebra with its original ambient residue maps

For the actual finite map between the point closures of x and f(x), an affine
neighborhood of the target generic point supplies the entire finite inverse
image. Both actual generic coordinate primes are proved to be zero. The whole
generic coordinate algebra is identified with the original ambient residue
field κ(x), through the literal open charts and support immersions. Its scalar
square retains the original f.residueFieldMap x.

This is the original-generic-coordinate prerequisite for exterior base change.
It does not identify a whole exterior finite algebra with a tensor product,
reduce an exterior stalk, or choose a branch after exterior base change.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cycles.Pushforward.GenericCoordinateFiber

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
open _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart
open _root_.AlgebraicGeometry.Scheme.GenericFiber.FiniteDomain
open _root_.AlgebraicGeometry.Scheme.Hom.FiniteFiber
open _root_.PrimeSpectrum.FiniteFiber

/-- Equal-point alignment of the actual scheme residue map. -/
def pointedResidueMap {D E : Scheme.{u}} (i : D ⟶ E) (d : D) (e : E)
    (h : e = i d) : E.residueField e ⟶ D.residueField d :=
  (E.residueFieldCongr h).hom ≫ i.residueFieldMap d

@[simp] theorem pointedResidueMap_rfl {D E : Scheme.{u}} (i : D ⟶ E) (d : D) :
    pointedResidueMap i d (i d) rfl = i.residueFieldMap d := by
  simp only [pointedResidueMap, Scheme.residueFieldCongr_refl, Iso.refl_hom,
    Category.id_comp]

/-- The original commuting scheme square gives its exact residue-field square,
including point transports. No abstract field isomorphisms enter this identity. -/
theorem pointedResidueMap_naturality
    {D E D' E' : Scheme.{u}} (i : D ⟶ E) (i' : D' ⟶ E')
    (jD : D' ⟶ D) (jE : E' ⟶ E) (hsq : i' ≫ jE = jD ≫ i)
    (d' : D') (e' : E') (d : D) (e : E)
    (hi' : e' = i' d') (hjD : d = jD d') (hjE : e = jE e') (hi : e = i d) :
    pointedResidueMap jE e' e hjE ≫ pointedResidueMap i' d' e' hi' =
      pointedResidueMap i d e hi ≫ pointedResidueMap jD d' d hjD := by
  subst d
  subst e'
  subst e
  simp only [pointedResidueMap, Scheme.residueFieldCongr_refl, Iso.refl_hom,
    Category.id_comp, Category.assoc]
  rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
  rw [Scheme.Hom.residueFieldMap_congr hsq d']
  simp

/-- A stalk-surjective chart or support immersion gives its own residue
isomorphism, with the actual residue map as forward homomorphism. -/
def pointedResidueIso {D E : Scheme.{u}} (i : D ⟶ E) [SurjectiveOnStalks i]
    (d : D) (e : E) (h : e = i d) : E.residueField e ≅ D.residueField d := by
  letI : IsIso (i.residueFieldMap d) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(i.residueFieldMap d).hom.injective, Hom.residueFieldMap_surjective i d⟩
  exact E.residueFieldCongr h ≪≫ asIso (i.residueFieldMap d)

@[simp] theorem pointedResidueIso_hom {D E : Scheme.{u}} (i : D ⟶ E)
    [SurjectiveOnStalks i] (d : D) (e : E) (h : e = i d) :
    (pointedResidueIso i d e h).hom = pointedResidueMap i d e h := rfl

/-- In an actual nonempty affine chart of an integral scheme the generic
coordinate prime, and not just an unnamed point, is the zero prime. -/
theorem genericCoordinate_eq_zero {D : Scheme.{u}} [IsIntegral D]
    {V : D.Opens} [Nonempty V] (hV : IsAffineOpen V) (hη : genericPoint D ∈ V) :
    hV.primeIdealOf ⟨genericPoint D, hη⟩ = zeroPrime Γ(D, V) := by
  change hV.primeIdealOf ⟨genericPoint D, hη⟩ = (⊥ : PrimeSpectrum Γ(D, V))
  rw [hV.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]

/-- The original chart sends zero to the original integral generic point. -/
theorem fromSpec_zero {D : Scheme.{u}} [IsIntegral D]
    {V : D.Opens} [Nonempty V] (hV : IsAffineOpen V) :
    hV.fromSpec (zeroPrime Γ(D, V)) = genericPoint D := by
  have h := genericPoint_eq_of_isOpenImmersion hV.fromSpec
  rw [genericPoint_eq_bot_of_affine] at h
  exact h

/-- Only the original generic stalk is a field. Its actual residue quotient
is therefore an isomorphism, preserving the actual localization map. -/
def genericLocalResidueIso (D : CommRingCat.{u}) [IsDomain D] :
    CommRingCat.of (Localization.AtPrime (zeroPrime D).asIdeal) ≅
      (Spec D).residueField (zeroPrime D) := by
  have hf : IsField ((Spec D).presheaf.stalk (zeroPrime D)) := by
    have hzero : zeroPrime D = genericPoint (Spec D) :=
      (genericPoint_eq_bot_of_affine D).symm
    rw [hzero]
    apply isField_stalk_of_closure_mem_irreducibleComponents
    rw [genericPoint_spec]
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
  letI := hf.toField
  letI : IsIso ((Spec D).residue (zeroPrime D)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨((Spec D).residue (zeroPrime D)).hom.injective, (Spec D).residue_surjective _⟩
  exact (Spec.stalkIso D (zeroPrime D)).symm ≪≫ asIso ((Spec D).residue (zeroPrime D))

/-- The localization/residue isomorphism is precisely the inverse stalk chart
followed by the actual residue quotient. -/
@[simp] theorem genericLocalResidueIso_hom (D : CommRingCat.{u}) [IsDomain D] :
    (genericLocalResidueIso D).hom =
      (Spec.stalkIso D (zeroPrime D)).inv ≫ (Spec D).residue (zeroPrime D) := rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
  {U : (pointClosure (f x)).val.subscheme.Opens} [Nonempty U] (hU : IsAffineOpen U)

/-- The actual target coordinate ring of the chosen whole affine chart. -/
abbrev targetRing := Γ((pointClosure (f x)).val.subscheme, U)

/-- The actual source coordinate ring of the whole finite inverse image. -/
abbrev sourceRing := Γ((pointClosure x).val.subscheme, pointClosureMap f x ⁻¹ᵁ U)

local notation "A" => targetRing f x (U := U)
local notation "B" => sourceRing f x (U := U)

omit [IsFinite f] in
/-- The chosen nonempty open contains the actual integral target generic point. -/
theorem generic_mem : genericPoint (pointClosure (f x)).val.subscheme ∈ U :=
  ((genericPoint_spec (pointClosure (f x)).val.subscheme).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

local instance sourceOpen_nonempty : Nonempty (pointClosureMap f x ⁻¹ᵁ U) :=
  ⟨⟨genericPoint (pointClosure x).val.subscheme, by
    change pointClosureMap f x (genericPoint (pointClosure x).val.subscheme) ∈ U
    rw [pointClosureMap_genericPoint]
    exact generic_mem f x⟩⟩

/-- The coordinate scalar action is the actual support map on sections. -/
local instance coordinateAlgebra : Algebra A B := ((pointClosureMap f x).app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [IsFinite f] in
/-- The literal target coordinate prime is zero. -/
theorem targetCoordinate_eq_zero :
    hU.primeIdealOf ⟨genericPoint (pointClosure (f x)).val.subscheme, generic_mem f x⟩ =
      zeroPrime A :=
  genericCoordinate_eq_zero hU (generic_mem f x)

/-- The literal source coordinate prime is zero on the entire finite inverse image. -/
theorem sourceCoordinate_eq_zero
    (hx : genericPoint (pointClosure x).val.subscheme ∈ pointClosureMap f x ⁻¹ᵁ U) :
    (hU.preimage (pointClosureMap f x)).primeIdealOf
      ⟨genericPoint (pointClosure x).val.subscheme, hx⟩ = zeroPrime B :=
  genericCoordinate_eq_zero (hU.preimage (pointClosureMap f x)) hx

/-- The whole-inverse-image chart's zero prime is the actual source generic point. -/
theorem sourceChart_zero :
    sourceChart (pointClosureMap f x) hU (zeroPrime B) =
      genericPoint (pointClosure x).val.subscheme :=
  fromSpec_zero (hU.preimage (pointClosureMap f x))

omit [IsFinite f] in
/-- The target zero coordinate is the original target-support generic point. -/
theorem targetChart_zero :
    hU.fromSpec (zeroPrime A) = genericPoint (pointClosure (f x)).val.subscheme :=
  fromSpec_zero hU

include hU in
/-- The coordinate zero contraction follows from the actual injective section map. -/
theorem zero_contraction :
    coordinateMap (pointClosureMap f x) (zeroPrime B) = zeroPrime A :=
  zeroPrime_comap A B (pointClosureMap_app_injective f x hU)

/-- The whole original generic algebra, before any exterior base change or branch choice. -/
abbrev wholeGenericAlgebra := localAlgebra A B (zeroPrime A)

include hU in
/-- Finiteness and domain properties come from the actual integral support morphism. -/
theorem wholeGenericAlgebra_isField : IsField (wholeGenericAlgebra f x (U := U)) := by
  let : Module.Finite A B := pointClosureMap_coordinate_finite f x hU
  exact whole_isField A B (pointClosureMap_app_injective f x hU)

/-- The source chart followed by the original point-closure immersion. -/
abbrev sourceAmbientChart : Spec B ⟶ X :=
  sourceChart (pointClosureMap f x) hU ≫ (pointClosure x).val.subschemeι

/-- The target chart followed by its original point-closure immersion. -/
abbrev targetAmbientChart : Spec A ⟶ Y :=
  hU.fromSpec ≫ (pointClosure (f x)).val.subschemeι

/-- The original ambient point is recovered, with no freely chosen field identification. -/
theorem sourceAmbientChart_zero : sourceAmbientChart f x hU (zeroPrime B) = x := by
  rw [sourceAmbientChart, Scheme.Hom.comp_apply, sourceChart_zero f x hU]
  exact point_pointClosure x

omit [IsFinite f] in
/-- The actual image point is recovered by the original target support immersion. -/
theorem targetAmbientChart_zero : targetAmbientChart f x hU (zeroPrime A) = f x := by
  rw [targetAmbientChart, Scheme.Hom.comp_apply, targetChart_zero f x hU]
  exact point_pointClosure (f x)

omit [Nonempty U] in
/-- The complete affine/support square is the literal original morphism f. -/
@[reassoc] theorem ambientChart_square :
    coordinateMap (pointClosureMap f x) (U := U) ≫ targetAmbientChart f x hU =
      sourceAmbientChart f x hU ≫ f := by
  rw [targetAmbientChart, ← Category.assoc, chart_square]
  simp only [sourceAmbientChart, Category.assoc, pointClosureMap_ambient]

/-- κ(x) is identified with its zero-coordinate residue field by the actual chart. -/
def sourceResidueIso : X.residueField x ≅ (Spec B).residueField (zeroPrime B) :=
  pointedResidueIso (sourceAmbientChart f x hU) (zeroPrime B) x
    (sourceAmbientChart_zero f x hU).symm

/-- κ(f x) is identified with its zero-coordinate residue by the actual target chart. -/
def targetResidueIso : Y.residueField (f x) ≅ (Spec A).residueField (zeroPrime A) :=
  pointedResidueIso (targetAmbientChart f x hU) (zeroPrime A) (f x)
    (targetAmbientChart_zero f x hU).symm

/-- The original generic target localization is κ(f x), with the exact
chart/immersion scalar map, before any exterior stalk enters the construction. -/
def targetLocalResidueIso :
    CommRingCat.of (Localization.AtPrime (zeroPrime A).asIdeal) ≅ Y.residueField (f x) :=
  genericLocalResidueIso A ≪≫ (targetResidueIso f x hU).symm

omit [IsFinite f] in
@[reassoc] theorem targetLocalResidueIso_hom :
    (targetLocalResidueIso f x hU).hom =
      (Spec.stalkIso A (zeroPrime A)).inv ≫ (Spec A).residue (zeroPrime A) ≫
        (targetResidueIso f x hU).inv := by
  simp only [targetLocalResidueIso, Iso.trans_hom, Iso.symm_hom,
    genericLocalResidueIso_hom, Category.assoc]

/-- The coordinate residue extension is the original ambient residue extension,
under the two actual chart/immersion residue maps. -/
theorem originalResidue_square :
    (targetResidueIso f x hU).hom ≫
      pointedSpecResidueMap ((pointClosureMap f x).app U) (zeroPrime A) (zeroPrime B)
        (zero_contraction f x hU) =
      f.residueFieldMap x ≫ (sourceResidueIso f x hU).hom := by
  simpa only [targetResidueIso, sourceResidueIso, pointedResidueIso_hom,
    pointedSpecResidueMap, pointedResidueMap, Scheme.residueFieldCongr_refl,
    Iso.refl_hom, Category.id_comp] using
    pointedResidueMap_naturality f (coordinateMap (pointClosureMap f x))
      (sourceAmbientChart f x hU) (targetAmbientChart f x hU)
      (ambientChart_square f x hU) (zeroPrime B) (zeroPrime A) x (f x)
      (zero_contraction f x hU).symm
      (sourceAmbientChart_zero f x hU).symm
      (targetAmbientChart_zero f x hU).symm rfl

/-- The WHOLE original generic finite algebra identifies with κ(x), through
its field proof and its literal source chart/immersion residue map. -/
def wholeOriginalResidueIso : CommRingCat.of (wholeGenericAlgebra f x (U := U)) ≅
    X.residueField x := by
  let : Module.Finite A B := pointClosureMap_coordinate_finite f x hU
  exact wholeResidueIso A B (pointClosureMap_app_injective f x hU) ≪≫
    (sourceResidueIso f x hU).symm

/-- The whole-algebra identification preserves the exact original residue-field
extension. This is the scalar input for later genuine exterior tensor base change. -/
@[reassoc] theorem wholeOriginalResidueIso_base_square :
    CommRingCat.ofHom (algebraMap (Localization.AtPrime (zeroPrime A).asIdeal)
      (wholeGenericAlgebra f x (U := U))) ≫ (wholeOriginalResidueIso f x hU).hom =
      (Spec.stalkIso A (zeroPrime A)).inv ≫ (Spec A).residue (zeroPrime A) ≫
        (targetResidueIso f x hU).inv ≫ f.residueFieldMap x := by
  let : Module.Finite A B := pointClosureMap_coordinate_finite f x hU
  rw [wholeOriginalResidueIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    wholeResidueIso_base_square]
  have hs := congrArg (fun k => (targetResidueIso f x hU).inv ≫ k ≫
      (sourceResidueIso f x hU).inv) (originalResidue_square f x hU)
  have hs' :
      pointedSpecResidueMap ((pointClosureMap f x).app U) (zeroPrime A) (zeroPrime B)
          (zero_contraction f x hU) ≫ (sourceResidueIso f x hU).inv =
        (targetResidueIso f x hU).inv ≫ f.residueFieldMap x := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using hs
  simpa only [Category.assoc, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    using congrArg (fun k => (Spec.stalkIso A (zeroPrime A)).inv ≫
      (Spec A).residue (zeroPrime A) ≫ k) hs'

/-- The κ(f x)-action on the whole generic algebra is obtained through the
inverse of the proved actual target-localization residue comparison. -/
def originalBaseToWhole :
    Y.residueField (f x) ⟶ CommRingCat.of (wholeGenericAlgebra f x (U := U)) :=
  (targetLocalResidueIso f x hU).inv ≫
    CommRingCat.ofHom (algebraMap (Localization.AtPrime (zeroPrime A).asIdeal)
      (wholeGenericAlgebra f x (U := U)))

/-- This action becomes exactly f.residueFieldMap x under the whole-algebra
comparison, which is the required scalar witness for later tensor congruence. -/
@[reassoc] theorem originalBaseToWhole_residue_square :
    originalBaseToWhole f x hU ≫ (wholeOriginalResidueIso f x hU).hom =
      f.residueFieldMap x := by
  rw [originalBaseToWhole, Category.assoc, wholeOriginalResidueIso_base_square]
  rw [← targetLocalResidueIso_hom_assoc]
  simp only [Iso.inv_hom_id_assoc]

/-- The whole-algebra isomorphism is linear for the original ambient residue
extension. No arbitrary algebra structure or numerical degree premise is used. -/
def wholeOriginalResidueAlgEquiv :
    letI := (originalBaseToWhole f x hU).hom.toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    wholeGenericAlgebra f x (U := U) ≃ₐ[Y.residueField (f x)] X.residueField x := by
  letI := (originalBaseToWhole f x hU).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  exact { (wholeOriginalResidueIso f x hU).commRingCatIsoToRingEquiv with
    commutes' := fun a => ConcreteCategory.congr_hom
      (originalBaseToWhole_residue_square f x hU) a }

/-- The source-coordinate action also retains its literal original germ,
residue, and inverse support-chart residue map. -/
@[reassoc] theorem wholeOriginalResidueIso_source_square :
    CommRingCat.ofHom (algebraMap B (wholeGenericAlgebra f x (U := U))) ≫
        (wholeOriginalResidueIso f x hU).hom =
      (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ (zeroPrime B) trivial ≫
        (Spec B).residue (zeroPrime B) ≫ (sourceResidueIso f x hU).inv := by
  let : Module.Finite A B := pointClosureMap_coordinate_finite f x hU
  rw [wholeOriginalResidueIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    wholeResidueIso_source_square]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Cycles.Pushforward.GenericCoordinateFiber

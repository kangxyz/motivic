/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.CartesianAffineAlgebra
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.CoordinateFiber

/-!
# The whole exterior algebra over the original residue extension

An actual Cartesian base change of the finite map between integral point
closures gives the whole finite algebra over an exterior target stalk R.
When the actual exterior projection lands at the original target generic
point, the original coordinate action extends through its zero-prime
localization. The accepted coordinate/residue comparisons then identify the
whole algebra with R tensor κ(x) over κ(f(x)), with the literal original
residue-field map as the right scalar action.

The target stalk R is never made a field or reduced. Both actual whole
inverse-image algebras are retained; no source branch is selected. The
Cartesian tensor comparison is constructed from the original square, rather
than assumed. Branch indexing and degree/length regrouping are separate.

Prepared against the original Cartesian and coordinate/residue APIs.
Verification status is recorded separately from this mathematical source.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cycles.BaseChange.ResidueTensor
open _root_.AlgebraicGeometry.Scheme.Hom

section BaseIsomorphism

variable {K L R E : Type u} [CommRing K] [CommRing L] [CommRing R] [CommRing E]
  [Algebra K R] [Algebra K E] (e : K ≃+* L)

/-- Transport the tensor base through a proved ring isomorphism, transporting
both actions by its inverse. No tensor comparison is supplied as a hypothesis. -/
def tensorBaseIsoEquiv :
    let := ((algebraMap K R).comp e.symm.toRingHom).toAlgebra
    let := ((algebraMap K E).comp e.symm.toRingHom).toAlgebra
    R ⊗[K] E ≃ₐ[R] R ⊗[L] E := by
  let := ((algebraMap K R).comp e.symm.toRingHom).toAlgebra
  let := ((algebraMap K E).comp e.symm.toRingHom).toAlgebra
  let : Algebra L K := e.symm.toRingHom.toAlgebra
  let : Algebra K L := e.toRingHom.toAlgebra
  let : IsScalarTower L K R := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L K E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L R := IsScalarTower.of_algebraMap_eq (by
    intro a
    change algebraMap K R a = algebraMap K R (e.symm (e a))
    rw [e.symm_apply_apply])
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq (by
    intro a
    change algebraMap K E a = algebraMap K E (e.symm (e a))
    rw [e.symm_apply_apply])
  exact Algebra.TensorProduct.equivOfCompatibleSMul L K R R E

/-- Transport of the tensor base preserves every pure tensor literally. -/
@[simp] theorem tensorBaseIsoEquiv_tmul (r : R) (b : E) :
    let := ((algebraMap K R).comp e.symm.toRingHom).toAlgebra
    let := ((algebraMap K E).comp e.symm.toRingHom).toAlgebra
    tensorBaseIsoEquiv e (r ⊗ₜ[K] b) = r ⊗ₜ[L] b := rfl

end BaseIsomorphism

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
open _root_.AlgebraicGeometry.Scheme.Cycles.Pushforward.GenericCoordinateFiber
open _root_.AlgebraicGeometry.Scheme.GenericFiber.FiniteDomain

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
  {U : (pointClosure (f x)).val.subscheme.Opens} [Nonempty U] (hU : IsAffineOpen U)

local notation "A" => targetRing f x (U := U)
local notation "B" => sourceRing f x (U := U)
local notation "K" => Localization.AtPrime (PrimeSpectrum.asIdeal (zeroPrime A))
local notation "L" => Y.residueField (f x)
local notation "M" => X.residueField x
local notation "E" => wholeGenericAlgebra f x (U := U)

/-- The coordinate algebra is induced by the actual point-closure map on sections. -/
local instance sourceCoordinateAlgebra : Algebra A B :=
  ((pointClosureMap f x).app U).hom.toAlgebra

local instance sourceOpen_nonempty : Nonempty (pointClosureMap f x ⁻¹ᵁ U) :=
  ⟨⟨genericPoint (pointClosure x).val.subscheme, by
    change pointClosureMap f x (genericPoint (pointClosure x).val.subscheme) ∈ U
    rw [pointClosureMap_genericPoint]
    exact generic_mem f x⟩⟩

/-- The right-hand field action is the original ambient residue-field map. -/
abbrev originalResidueAlgebra : Algebra L M := (f.residueFieldMap x).hom.toAlgebra

section ProjectedStalk

variable {Y' : Scheme.{u}} (g : Y' ⟶ (pointClosure (f x)).val.subscheme)
  (y : Y') (hy : g y = genericPoint (pointClosure (f x)).val.subscheme)

omit [IsFinite f] in
include hy in
/-- The actual projected point lies in every nonempty original affine chart. -/
theorem projected_mem : g y ∈ U := by
  rw [hy]
  exact generic_mem f x

omit [IsFinite f] in
/-- The actual projected coordinate prime is zero, not an arbitrarily chosen
prime or a consequence of a finite map preserving generic points. -/
theorem projectedCoordinate_eq_zero :
    hU.primeIdealOf ⟨g y, projected_mem f x g y hy (U := U)⟩ = zeroPrime A := by
  simpa only [hy] using targetCoordinate_eq_zero f x hU

/-- The original coordinate localization is the actual projected support stalk,
with its original germ scalar action. -/
def projectedLocalizationEquiv :
    let := ((pointClosure (f x)).val.subscheme.presheaf.germ U (g y)
      (projected_mem f x g y hy (U := U))).hom.toAlgebra
    K ≃ₐ[A] (pointClosure (f x)).val.subscheme.presheaf.stalk (g y) := by
  let := ((pointClosure (f x)).val.subscheme.presheaf.germ U (g y)
    (projected_mem f x g y hy (U := U))).hom.toAlgebra
  let : IsLocalization.AtPrime
      ((pointClosure (f x)).val.subscheme.presheaf.stalk (g y)) (zeroPrime A).asIdeal := by
    simpa only [projectedCoordinate_eq_zero f x hU g y hy] using
      hU.isLocalization_stalk ⟨g y, projected_mem f x g y hy (U := U)⟩
  exact IsLocalization.algEquiv (zeroPrime A).asIdeal.primeCompl _ _

/-- The original localization acts through the literal exterior projection
stalk map, after its germ-preserving affine localization comparison. -/
def genericLocalizationToStalk : K →+* Y'.presheaf.stalk y :=
  (g.stalkMap y).hom.comp (projectedLocalizationEquiv f x hU g y hy).toRingHom

omit [IsFinite f] in
/-- This localization action sends original coordinate fractions of denominator
one to the actual projection's image of the original germs. -/
@[simp] theorem genericLocalizationToStalk_algebraMap (a : A) :
    genericLocalizationToStalk f x hU g y hy (algebraMap A K a) =
      g.stalkMap y ((pointClosure (f x)).val.subscheme.presheaf.germ U (g y)
        (projected_mem f x g y hy (U := U)) a) := by
  let := ((pointClosure (f x)).val.subscheme.presheaf.germ U (g y)
    (projected_mem f x g y hy (U := U))).hom.toAlgebra
  change g.stalkMap y (projectedLocalizationEquiv f x hU g y hy
    (algebraMap A K a)) = _
  exact congrArg (fun z => g.stalkMap y z)
    ((projectedLocalizationEquiv f x hU g y hy).commutes a)

/-- The actual ambient target residue field acts on the exterior stalk through
the accepted original localization/residue map and the literal projection. -/
def originalResidueToStalk : L →+* Y'.presheaf.stalk y :=
  (genericLocalizationToStalk f x hU g y hy).comp (targetLocalResidueIso f x hU).inv.hom

omit [IsFinite f] in
/-- The residue action recovers the entire localization action; this records
which target-residue identification is used, not just its abstract field type. -/
theorem originalResidueToStalk_localizationSquare :
    (originalResidueToStalk f x hU g y hy).comp (targetLocalResidueIso f x hU).hom.hom =
      genericLocalizationToStalk f x hU g y hy := by
  ext a
  simp [originalResidueToStalk]

end ProjectedStalk

section ActualCartesianSquare

variable {X' Y' : Scheme.{u}} {i : X' ⟶ (pointClosure x).val.subscheme}
  {f' : X' ⟶ Y'} {g : Y' ⟶ (pointClosure (f x)).val.subscheme}
  (sq : IsPullback i f' (pointClosureMap f x) g)
  {V : Y'.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
  (y : V) (hy : g y.1 = genericPoint (pointClosure (f x)).val.subscheme)

local notation "C" => FiniteCartesianAffineAlgebra.baseChangedTargetRing (Y' := Y') (V := V)
local notation "D" => FiniteCartesianAffineAlgebra.baseChangedSourceRing (f' := f') (V := V)
local notation "R" => Y'.presheaf.stalk (Subtype.val y)

/-- The actual original-coordinate action on the exterior stalk is the
horizontal section map followed by the exterior germ. -/
abbrev exteriorCoordinateAlgebra : Algebra A R :=
  ((Y'.presheaf.germ V y.1 y.2).hom.comp (g.appLE U V hVU).hom).toAlgebra

omit [IsFinite f] in
/-- The localization extension agrees with the actual chart action on every
original coordinate, by the literal scheme germ/stalk square. -/
theorem genericLocalization_coordinateSquare :
    (genericLocalizationToStalk f x hU g y.1 hy).comp (algebraMap A K) =
      (Y'.presheaf.germ V y.1 y.2).hom.comp (g.appLE U V hVU).hom := by
  ext a
  rw [RingHom.comp_apply, genericLocalizationToStalk_algebraMap]
  exact (ConcreteCategory.congr_hom
    (FiniteCartesianAffineAlgebra.originalGerm_stalkSquare hVU y) a).symm

omit [IsFinite f] in
/-- The target-residue action has the same literal original-coordinate germ
square. It is not an unspecified extension of the coordinate action. -/
theorem originalResidueToStalk_coordinateSquare :
    (originalResidueToStalk f x hU g y.1 hy).comp
        ((targetLocalResidueIso f x hU).hom.hom.comp (algebraMap A K)) =
      (Y'.presheaf.germ V y.1 y.2).hom.comp (g.appLE U V hVU).hom := by
  rw [← RingHom.comp_assoc, originalResidueToStalk_localizationSquare]
  exact genericLocalization_coordinateSquare f x hU hVU y hy

/-- After the actual localization extension, the original-coordinate tensor
becomes the original ambient residue tensor. The right action is exactly
f.residueFieldMap x. -/
def coordinateToResidueTensorEquiv :
    let := exteriorCoordinateAlgebra f x hVU y
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    let := originalResidueAlgebra f x
    R ⊗[A] B ≃ₐ[R] R ⊗[L] M := by
  let := exteriorCoordinateAlgebra f x hVU y
  let := (genericLocalizationToStalk f x hU g y.1 hy).toAlgebra
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let := originalResidueAlgebra f x
  let : IsScalarTower A K R := IsScalarTower.of_algebraMap_eq'
    (genericLocalization_coordinateSquare f x hU hVU y hy).symm
  let := (originalBaseToWhole f x hU).hom.toAlgebra
  exact (Algebra.TensorProduct.cancelBaseChange A K R R B).symm.trans
    ((tensorBaseIsoEquiv (targetLocalResidueIso f x hU).commRingCatIsoToRingEquiv).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
        (wholeOriginalResidueAlgEquiv f x hU)))

/-- The actual original source-coordinate numerator map into κ(x), displayed
as the original chart germ, residue quotient and inverse support-chart map. -/
def originalSourceNumerator : B ⟶ M :=
  (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ (zeroPrime B) trivial ≫
    (Spec B).residue (zeroPrime B) ≫ (sourceResidueIso f x hU).inv

/-- The accepted whole generic residue comparison sends each numerator through
its original source chart; no abstract source field identification is chosen. -/
theorem originalSourceNumerator_eq (b : B) :
    (wholeOriginalResidueIso f x hU).hom (1 ⊗ₜ[A] b) = originalSourceNumerator f x hU b := by
  exact ConcreteCategory.congr_hom (wholeOriginalResidueIso_source_square f x hU) b

/-- The coordinate-to-residue tensor comparison preserves every source
numerator and every element of the possibly nonreduced exterior stalk. -/
@[simp] theorem coordinateToResidueTensorEquiv_tmul (r : R) (b : B) :
    let := exteriorCoordinateAlgebra f x hVU y
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    let := originalResidueAlgebra f x
    coordinateToResidueTensorEquiv f x hU hVU y hy (r ⊗ₜ[A] b) =
      r ⊗ₜ[L] originalSourceNumerator f x hU b := by
  let := exteriorCoordinateAlgebra f x hVU y
  let := (genericLocalizationToStalk f x hU g y.1 hy).toAlgebra
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let := originalResidueAlgebra f x
  simp only [coordinateToResidueTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, tensorBaseIsoEquiv_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  exact congrArg (fun m => r ⊗ₜ[L] m) (originalSourceNumerator_eq f x hU b)

/-- The whole actual finite inverse-image algebra over the original exterior
stalk is R tensor κ(x) over κ(f(x)), with both actual residue actions. -/
def wholeStalkResidueEquiv :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    let := originalResidueAlgebra f x
    R ⊗[C] D ≃ₐ[R] R ⊗[L] M := by
  let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
  let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
  let := exteriorCoordinateAlgebra f x hVU y
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let := originalResidueAlgebra f x
  exact (FiniteCartesianAffineAlgebra.wholeStalkEquiv sq hU hV hVU y).trans
    (coordinateToResidueTensorEquiv f x hU hVU y hy)

/-- The whole-algebra comparison keeps the original source horizontal section
map and its literal residue numerator map in the same commuting square. -/
@[simp] theorem wholeStalkResidueEquiv_source (r : R) (b : B) :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    let := originalResidueAlgebra f x
    wholeStalkResidueEquiv f x hU sq hV hVU y hy
        (r ⊗ₜ[C] FiniteCartesianAffineAlgebra.sourceSectionMap sq hVU b) =
      r ⊗ₜ[L] originalSourceNumerator f x hU b := by
  let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
  let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let := originalResidueAlgebra f x
  simp only [wholeStalkResidueEquiv, AlgEquiv.trans_apply,
    FiniteCartesianAffineAlgebra.wholeStalkEquiv_source, coordinateToResidueTensorEquiv_tmul]

/-- The original source numerator comparison is a literal ring-map square,
not only a correspondence of pure tensors or of points. -/
theorem wholeStalkResidueEquiv_numeratorSquare :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    let := originalResidueAlgebra f x
    (wholeStalkResidueEquiv f x hU sq hV hVU y hy).toRingHom.comp
        ((Algebra.TensorProduct.includeRight.toRingHom : D →+* R ⊗[C] D).comp
          (FiniteCartesianAffineAlgebra.sourceSectionMap sq hVU).hom) =
      (Algebra.TensorProduct.includeRight.toRingHom : M →+* R ⊗[L] M).comp
        (originalSourceNumerator f x hU).hom := by
  let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
  let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let := originalResidueAlgebra f x
  ext b
  exact wholeStalkResidueEquiv_source f x hU sq hV hVU y hy 1 b

/-- The scalar square is over the entire exterior target stalk, before any
quotient or branch localization. In particular all its nilpotents act. -/
theorem wholeStalkResidueEquiv_scalarSquare :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    let := originalResidueAlgebra f x
    (wholeStalkResidueEquiv f x hU sq hV hVU y hy).toRingHom.comp
        (algebraMap R (R ⊗[C] D)) = algebraMap R (R ⊗[L] M) := by
  let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
  let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let := originalResidueAlgebra f x
  ext r
  exact (wholeStalkResidueEquiv f x hU sq hV hVU y hy).commutes r

include sq hV in
/-- Finiteness belongs to the whole actual exterior algebra, with no maximal
branch removed. -/
theorem wholeStalk_finite :
    let := FiniteCartesianAffineAlgebra.baseChangedAlgebra (f' := f') (V := V)
    let := FiniteCartesianAffineAlgebra.targetStalkAlgebra y
    Module.Finite R (R ⊗[C] D) :=
  FiniteCartesianAffineAlgebra.wholeStalk_finite sq hV y

end ActualCartesianSquare

end AlgebraicGeometry.Scheme.Cycles.BaseChange.ResidueTensor

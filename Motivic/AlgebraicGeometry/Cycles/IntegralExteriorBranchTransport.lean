/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorResidueTensor
public import Motivic.AlgebraicGeometry.Cycles.FiniteAffineChart
public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardStalk
public import Motivic.AlgebraicGeometry.Cycles.GenericFiniteFiber

/-!
# Every branch of the actual exterior residue tensor

The constructed whole exterior algebra equivalence transports every maximal
ideal of the residue tensor to the existing finite-fiber local algebra. Its
localizations are identified with the actual exterior source stalks, preserving
the literal whole-target-stalk action and its induced residue-field action.
Only when the actual exterior target point is generic are the source points
identified with generic points of the exterior source SUPPORT scheme.

This transports the resulting whole fiber through an isomorphism. It does not
assert preservation of the original branches under arbitrary base change.
There is no reducedness, single-branch, degree-balance or cycle-equality premise.
SOURCE-ONLY: no compilation or mathematical admission is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.IntegralExteriorBranchTransport

section RingTransport

variable {T S : Type u} [CommRing T] [CommRing S] (e : T ≃+* S)

/-- All maximal ideals are transported by contraction along the inverse
isomorphism. This is an equivalence of whole maximal spectra. -/
def maximalEquiv : MaximalSpectrum T ≃ MaximalSpectrum S where
  toFun q := ⟨q.asIdeal.comap e.symm.toRingHom,
    q.isMaximal.comap_bijective _ e.symm.bijective⟩
  invFun q := ⟨q.asIdeal.comap e.toRingHom,
    q.isMaximal.comap_bijective _ e.bijective⟩
  left_inv q := by
    apply MaximalSpectrum.ext
    ext a
    change e.symm (e a) ∈ q.asIdeal ↔ a ∈ q.asIdeal
    rw [e.symm_apply_apply]
  right_inv q := by
    apply MaximalSpectrum.ext
    ext a
    change e (e.symm a) ∈ q.asIdeal ↔ a ∈ q.asIdeal
    rw [e.apply_symm_apply]

/-- The ideal is the literal contraction, not an independently chosen index. -/
@[simp] theorem maximalEquiv_asIdeal (q : MaximalSpectrum T) :
    (maximalEquiv e q).asIdeal = q.asIdeal.comap e.symm.toRingHom := rfl

/-- The forward isomorphism contracts the transported ideal back to the original. -/
theorem maximalEquiv_comap (q : MaximalSpectrum T) :
    q.asIdeal = (maximalEquiv e q).asIdeal.comap e.toRingHom := by
  ext a
  change a ∈ q.asIdeal ↔ e.symm (e a) ∈ q.asIdeal
  rw [e.symm_apply_apply]

/-- Localize the given whole-algebra isomorphism at each transported branch. -/
def maximalLocalizationEquiv (q : MaximalSpectrum T) :
    Localization.AtPrime q.asIdeal ≃+*
      Localization.AtPrime (maximalEquiv e q).asIdeal :=
  Localization.localRingEquiv q.asIdeal (maximalEquiv e q).asIdeal e
    (maximalEquiv_comap e q)

/-- The branch comparison preserves the image of every whole-algebra element. -/
theorem maximalLocalizationEquiv_algebraMap (q : MaximalSpectrum T) (a : T) :
    maximalLocalizationEquiv e q (algebraMap T (Localization.AtPrime q.asIdeal) a) =
      algebraMap S (Localization.AtPrime (maximalEquiv e q).asIdeal) (e a) :=
  Localization.localRingHom_to_map _ _ _ (maximalEquiv_comap e q) a

end RingTransport

section ActualFiniteFiber

variable {W Z : Scheme.{u}} (a : W ⟶ Z) [IsFinite a]
  {V : Z.Opens} (hV : IsAffineOpen V) (y : V)

local notation "C" => FiniteCartesianAffineAlgebra.baseChangedTargetRing (Y' := Z) (V := V)
local notation "D" => FiniteCartesianAffineAlgebra.baseChangedSourceRing (f' := a) (V := V)
local notation "R" => Z.presheaf.stalk (Subtype.val y)
local notation "p" => hV.primeIdealOf y
local notation "K" => Localization.AtPrime (PrimeSpectrum.asIdeal (hV.primeIdealOf y))
local notation "S" => FiniteFiber.localAlgebra C D p

/-- The source coordinates use the actual finite-map section pullback. -/
local instance finiteCoordinateAlgebra : Algebra C D := (a.app V).hom.toAlgebra

/-- The target coordinates act through their literal germ at the chosen point. -/
local instance targetGermAlgebra : Algebra C R := (Z.presheaf.germ V y.1 y.2).hom.toAlgebra

include hV in
/-- The actual finite map gives finite coordinates on the entire affine preimage. -/
theorem finiteCoordinates : Module.Finite C D := a.finite_app V hV

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Align only the equal target points in the actual fiber. -/
def pointFiberCongr {y₁ y₂ : Z} (h : y₁ = y₂) :
    {w : W // a w = y₁} ≃ {w : W // a w = y₂} where
  toFun w := ⟨w.1, w.2.trans h⟩
  invFun w := ⟨w.1, w.2.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The existing whole-local-algebra fiber equivalence, aligned with the
literal chosen target point, contains every actual source fiber point. -/
def localAlgebraFiberEquiv : MaximalSpectrum S ≃ {w : W // a w = y.1} := by
  letI : Module.Finite C D := a.finite_app V hV
  exact (FiniteFiber.maximalSpectrumEquivFiber C D p).trans
    ((FiniteAffineChart.fiberEquiv a hV p).trans
      (pointFiberCongr a (hV.fromSpec_primeIdealOf y)))

/-- The actual source point is precisely the existing finite-fiber source
coordinate point followed by the whole affine inverse-image chart. -/
@[simp] theorem localAlgebraFiberEquiv_val (q : MaximalSpectrum S) :
    letI : Module.Finite C D := a.finite_app V hV
    (localAlgebraFiberEquiv a hV y q).1 =
      FiniteAffineChart.sourceChart a hV (FiniteFiber.sourcePoint C D p q).1 := by
  let : Module.Finite C D := a.finite_app V hV
  rfl

/-- The source point belongs to the whole inverse-image affine chart. -/
theorem sourcePoint_mem (q : MaximalSpectrum S) :
    (localAlgebraFiberEquiv a hV y q).1 ∈ a ⁻¹ᵁ V := by
  change a (localAlgebraFiberEquiv a hV y q).1 ∈ V
  rw [(localAlgebraFiberEquiv a hV y q).2]
  exact y.2

/-- The branch source stalk carries the actual whole-source-coordinate germ. -/
abbrev sourceGermAlgebra (q : MaximalSpectrum S) :
    Algebra D (W.presheaf.stalk (localAlgebraFiberEquiv a hV y q).1) :=
  (W.presheaf.germ (a ⁻¹ᵁ V) (localAlgebraFiberEquiv a hV y q).1
    (sourcePoint_mem a hV y q)).hom.toAlgebra

/-- The coordinate source localization is the actual source stalk, with its
literal germ action. No abstract local-ring comparison is an input. -/
def sourceCoordinateStalkEquiv (q : MaximalSpectrum S) :
    letI : Module.Finite C D := a.finite_app V hV
    let := sourceGermAlgebra a hV y q
    Localization.AtPrime (FiniteFiber.sourcePoint C D p q).1.asIdeal ≃ₐ[D]
      W.presheaf.stalk (localAlgebraFiberEquiv a hV y q).1 := by
  letI : Module.Finite C D := a.finite_app V hV
  let := sourceGermAlgebra a hV y q
  let : IsLocalization.AtPrime
      (W.presheaf.stalk (localAlgebraFiberEquiv a hV y q).1)
      (FiniteFiber.sourcePoint C D p q).1.asIdeal :=
    (hV.preimage a).isLocalization_stalk' (FiniteFiber.sourcePoint C D p q).1
      (sourcePoint_mem a hV y q)
  exact IsLocalization.algEquiv (FiniteFiber.sourcePoint C D p q).1.asIdeal.primeCompl _ _

/-- Each maximal localization of the existing whole local algebra is the
actual exterior source stalk. Its D-linearity is the original germ action. -/
def localAlgebraStalkEquiv (q : MaximalSpectrum S) :
    let := sourceGermAlgebra a hV y q
    Localization.AtPrime q.asIdeal ≃ₐ[D]
      W.presheaf.stalk (localAlgebraFiberEquiv a hV y q).1 := by
  letI : Module.Finite C D := a.finite_app V hV
  let := sourceGermAlgebra a hV y q
  exact (FiniteFiber.sourceLocalizationEquiv C D p q).trans
    (sourceCoordinateStalkEquiv a hV y q)

/-- The actual finite-map stalk homomorphism with its target point aligned. -/
def actualFiberStalkMap (w : {w : W // a w = y.1}) :
    R ⟶ W.presheaf.stalk w.1 :=
  Graph.alignedStalkMap a w.1 y.1 w.2.symm

/-- Point alignment does not change the local nature of the literal stalk map. -/
instance actualFiberStalkMap_isLocalHom (w : {w : W // a w = y.1}) :
    IsLocalHom (actualFiberStalkMap a y w).hom := by
  dsimp only [actualFiberStalkMap, Graph.alignedStalkMap]
  infer_instance

omit [IsFinite a] in
/-- The target germ goes to the actual source germ of the section pullback. -/
theorem actualFiberStalkMap_germ (w : {w : W // a w = y.1}) (c : C) :
    actualFiberStalkMap a y w (Z.presheaf.germ V y.1 y.2 c) =
      W.presheaf.germ (a ⁻¹ᵁ V) w.1
        (by
          change a w.1 ∈ V
          rw [w.2]
          exact y.2) (a.app V c) := by
  rcases y with ⟨y, hy⟩
  rcases w with ⟨w, hw⟩
  dsimp only at hw
  subst y
  simp only [actualFiberStalkMap, Graph.alignedStalkMap_rfl,
    Scheme.Hom.germ_stalkMap_apply]

/-- The local-algebra/source-stalk comparison uses the literal actual
whole-target-stalk scalar map, not a new action chosen after localizing. -/
theorem localAlgebraStalkEquiv_scalarSquare (q : MaximalSpectrum S) :
    let := sourceGermAlgebra a hV y q
    (localAlgebraStalkEquiv a hV y q).toRingHom.comp
        ((algebraMap K (Localization.AtPrime q.asIdeal)).comp
          (FiniteCartesianAffineAlgebra.targetStalkLocalizationEquiv hV y).toRingHom) =
      (actualFiberStalkMap a y (localAlgebraFiberEquiv a hV y q)).hom := by
  let := sourceGermAlgebra a hV y q
  let : IsLocalization.AtPrime R (hV.primeIdealOf y).asIdeal := hV.isLocalization_stalk y
  apply IsLocalization.ringHom_ext (hV.primeIdealOf y).asIdeal.primeCompl
  ext c
  change localAlgebraStalkEquiv a hV y q
      (algebraMap K (Localization.AtPrime q.asIdeal)
        (FiniteCartesianAffineAlgebra.targetStalkLocalizationEquiv hV y
          (algebraMap C R c))) = _
  rw [(FiniteCartesianAffineAlgebra.targetStalkLocalizationEquiv hV y).commutes,
    ← IsScalarTower.algebraMap_apply C K (Localization.AtPrime q.asIdeal),
    IsScalarTower.algebraMap_apply C D (Localization.AtPrime q.asIdeal),
    (localAlgebraStalkEquiv a hV y q).commutes]
  exact (actualFiberStalkMap_germ a y (localAlgebraFiberEquiv a hV y q) c).symm

/-- The aligned actual residue map is induced by the same scheme morphism. -/
def actualFiberResidueMap (w : {w : W // a w = y.1}) :
    Z.residueField y.1 ⟶ W.residueField w.1 :=
  (Scheme.residueFieldCongr (X := Z) w.2.symm).hom ≫ a.residueFieldMap w.1

omit [IsFinite a] in
/-- Reduction commutes with the actual aligned finite-map stalk map. -/
theorem actualFiberStalkMap_residue (w : {w : W // a w = y.1}) :
    Z.residue y.1 ≫ actualFiberResidueMap a y w =
      actualFiberStalkMap a y w ≫ W.residue w.1 := by
  rcases y with ⟨y, hy⟩
  rcases w with ⟨w, hw⟩
  dsimp only at hw
  subst y
  simp only [actualFiberResidueMap, actualFiberStalkMap, Graph.alignedStalkMap_rfl,
    Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp]
  exact Scheme.residue_residueFieldMap a w

end ActualFiniteFiber

section ActualExterior

open IntegralClosedSubscheme IntegralGenericCoordinateFiber IntegralExteriorResidueTensor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
  {U : (pointClosure (f x)).val.subscheme.Opens} [Nonempty U] (hU : IsAffineOpen U)
  {X' Y' : Scheme.{u}} {i : X' ⟶ (pointClosure x).val.subscheme}
  {f' : X' ⟶ Y'} {g : Y' ⟶ (pointClosure (f x)).val.subscheme}
  (sq : IsPullback i f' (pointClosureMap f x) g)
  {V : Y'.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
  (y : V) (hy : g y.1 = genericPoint (pointClosure (f x)).val.subscheme)

local notation "C" => FiniteCartesianAffineAlgebra.baseChangedTargetRing (Y' := Y') (V := V)
local notation "D" => FiniteCartesianAffineAlgebra.baseChangedSourceRing (f' := f') (V := V)
local notation "R" => Y'.presheaf.stalk (Subtype.val y)
local notation "L" => Y.residueField (f x)
local notation "M" => X.residueField x
local notation "p" => hV.primeIdealOf y
local notation "K" => Localization.AtPrime (PrimeSpectrum.asIdeal (hV.primeIdealOf y))
local notation "S" => FiniteFiber.localAlgebra C D p

include sq in
/-- Finiteness of the exterior map is derived from the actual Cartesian square. -/
theorem exteriorFinite : IsFinite f' :=
  MorphismProperty.of_isPullback sq inferInstance

/-- Exterior source coordinates use the actual exterior section pullback. -/
local instance exteriorCoordinates : Algebra C D := (f'.app V).hom.toAlgebra

/-- Exterior target coordinates act through the original target germ. -/
local instance exteriorGerm : Algebra C R := (Y'.presheaf.germ V y.1 y.2).hom.toAlgebra

/-- The original target residue field acts through the literal projection stalk map. -/
abbrev exteriorResidue : Algebra L R :=
  (originalResidueToStalk f x hU g y.1 hy).toAlgebra

/-- The original source residue action is the given finite-map residue action. -/
local instance originalResidue : Algebra L M := originalResidueAlgebra f x

local notation "T" => R ⊗[L] M

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The already constructed residue tensor is identified with the existing
whole finite local algebra. Neither isomorphism is supplied as a premise. -/
def residueTensorToLocalEquiv :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    T ≃+* S := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  exact (wholeStalkResidueEquiv f x hU sq hV hVU y hy).symm.toRingEquiv.trans
    (FiniteCartesianAffineAlgebra.wholeStalkToLocalEquiv (f' := f') hV y).toRingEquiv

/-- Its scalar square retains every element of the actual exterior target
stalk and the actual affine localization comparison. -/
theorem residueTensorToLocalEquiv_scalar (r : R) :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    residueTensorToLocalEquiv f x hU sq hV hVU y hy (algebraMap R T r) =
      algebraMap K S (FiniteCartesianAffineAlgebra.targetStalkLocalizationEquiv hV y r) := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  change FiniteCartesianAffineAlgebra.wholeStalkToLocalEquiv (f' := f') hV y
      ((wholeStalkResidueEquiv f x hU sq hV hVU y hy).symm (algebraMap R T r)) = _
  rw [(wholeStalkResidueEquiv f x hU sq hV hVU y hy).symm.commutes]
  exact FiniteCartesianAffineAlgebra.wholeStalkToLocalEquiv_scalar (f' := f') hV y r

/-- Every maximal residue-tensor branch has its literal maximal ideal in the
existing whole finite local algebra. -/
def tensorMaximalEquiv :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    MaximalSpectrum T ≃ MaximalSpectrum S := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  exact maximalEquiv (residueTensorToLocalEquiv f x hU sq hV hVU y hy)

/-- Every branch of the residue tensor corresponds to exactly one point of
the actual exterior source fiber; the inverse includes all fiber points. -/
def tensorFiberEquiv :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    MaximalSpectrum T ≃ {w : X' // f' w = y.1} := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  exact (tensorMaximalEquiv f x hU sq hV hVU y hy).trans
    (localAlgebraFiberEquiv f' hV y)

/-- The branch-local ring isomorphism is induced by the constructed whole
isomorphism and the existing finite-fiber source localization. -/
def tensorBranchStalkEquiv :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    Localization.AtPrime q.asIdeal ≃+*
      X'.presheaf.stalk (tensorFiberEquiv f x hU sq hV hVU y hy q).1 := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  dsimp only
  intro q
  let := sourceGermAlgebra f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q)
  exact (maximalLocalizationEquiv (residueTensorToLocalEquiv f x hU sq hV hVU y hy) q).trans
    (localAlgebraStalkEquiv f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q)).toRingEquiv

/-- The entire target stalk acts through the canonical scalar map into the
residue tensor, followed by this branch's localization. -/
def tensorBranchBaseMap :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T), R →+* Localization.AtPrime q.asIdeal := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  exact (algebraMap T (Localization.AtPrime q.asIdeal)).comp (algebraMap R T)

/-- The branch-local scalar square is the literal actual exterior finite-map
stalk homomorphism, with only the equal target points aligned. -/
theorem tensorBranchStalkEquiv_scalarSquare :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    (tensorBranchStalkEquiv f x hU sq hV hVU y hy q).toRingHom.comp
        (tensorBranchBaseMap f x hU y hy q) =
      (actualFiberStalkMap f' y (tensorFiberEquiv f x hU sq hV hVU y hy q)).hom := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  dsimp only
  intro q
  ext r
  change localAlgebraStalkEquiv f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q)
      (maximalLocalizationEquiv (residueTensorToLocalEquiv f x hU sq hV hVU y hy) q
        (algebraMap T (Localization.AtPrime q.asIdeal) (algebraMap R T r))) = _
  rw [maximalLocalizationEquiv_algebraMap, residueTensorToLocalEquiv_scalar]
  change localAlgebraStalkEquiv f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q)
      (algebraMap S (Localization.AtPrime
        (tensorMaximalEquiv f x hU sq hV hVU y hy q).asIdeal)
        (algebraMap K S (FiniteCartesianAffineAlgebra.targetStalkLocalizationEquiv hV y r))) = _
  rw [← IsScalarTower.algebraMap_apply K S
    (Localization.AtPrime (tensorMaximalEquiv f x hU sq hV hVU y hy q).asIdeal)]
  exact RingHom.congr_fun (localAlgebraStalkEquiv_scalarSquare f' hV y
    (tensorMaximalEquiv f x hU sq hV hVU y hy q)) r

include sq hV hVU in
/-- Locality is proved from the literal actual source-stalk square. -/
theorem tensorBranchBaseMap_isLocalHom :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    IsLocalHom (tensorBranchBaseMap f x hU y hy q) := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  dsimp only
  intro q
  have : IsLocalHom
      ((tensorBranchStalkEquiv f x hU sq hV hVU y hy q).toRingHom.comp
        (tensorBranchBaseMap f x hU y hy q)) := by
    rw [tensorBranchStalkEquiv_scalarSquare f x hU sq hV hVU y hy q]
    infer_instance
  exact isLocalHom_of_comp (tensorBranchBaseMap f x hU y hy q)
    (tensorBranchStalkEquiv f x hU sq hV hVU y hy q).toRingHom

/-- The induced target residue action, with locality supplied by the proved
actual Cartesian branch square. -/
def tensorBranchResidueMap :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    Y'.residueField y.1 →+* q.asIdeal.ResidueField := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  letI := tensorBranchBaseMap_isLocalHom f x hU sq hV hVU y hy q
  exact IsLocalRing.ResidueField.map (tensorBranchBaseMap f x hU y hy q)

/-- The branch residue action is the reduction of the full original stalk action. -/
@[simp] theorem tensorBranchResidueMap_residue :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T) (r : R),
    tensorBranchResidueMap f x hU sq hV hVU y hy q (Y'.residue y.1 r) =
      IsLocalRing.residue _ (tensorBranchBaseMap f x hU y hy q r) := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q r
  rfl

/-- Each residue comparison is induced by the proved branch-local stalk
isomorphism, rather than by an independently chosen field isomorphism. -/
def tensorBranchResidueEquiv :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    q.asIdeal.ResidueField ≃+*
      X'.residueField (tensorFiberEquiv f x hU sq hV hVU y hy q).1 := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  exact IsLocalRing.ResidueField.mapEquiv (tensorBranchStalkEquiv f x hU sq hV hVU y hy q)

/-- The branch residue comparison preserves reduction of every branch-local
element, including images of nilpotents before reduction. -/
@[simp] theorem tensorBranchResidueEquiv_residue :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T) (z : Localization.AtPrime q.asIdeal),
    tensorBranchResidueEquiv f x hU sq hV hVU y hy q (IsLocalRing.residue _ z) =
      X'.residue (tensorFiberEquiv f x hU sq hV hVU y hy q).1
        (tensorBranchStalkEquiv f x hU sq hV hVU y hy q z) := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q z
  rfl

/-- The branch residue action agrees with the actual exterior morphism's
residueFieldMap, not merely with an abstract extension of isomorphic fields. -/
theorem tensorBranchResidueEquiv_scalarSquare :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    (tensorBranchResidueEquiv f x hU sq hV hVU y hy q).toRingHom.comp
        (tensorBranchResidueMap f x hU sq hV hVU y hy q) =
      (actualFiberResidueMap f' y (tensorFiberEquiv f x hU sq hV hVU y hy q)).hom := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  ext z
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
  change X'.residue (tensorFiberEquiv f x hU sq hV hVU y hy q).1
      (tensorBranchStalkEquiv f x hU sq hV hVU y hy q
        (tensorBranchBaseMap f x hU y hy q r)) = _
  have hs := RingHom.congr_fun
    (tensorBranchStalkEquiv_scalarSquare f x hU sq hV hVU y hy q) r
  have hr := ConcreteCategory.congr_hom
    (actualFiberStalkMap_residue f' y (tensorFiberEquiv f x hU sq hV hVU y hy q)) r
  exact (congrArg (X'.residue (tensorFiberEquiv f x hU sq hV hVU y hy q).1) hs).trans hr.symm

/-- The original ambient target residue field acts through exactly the
projection action used to construct the whole residue tensor. -/
theorem tensorBranchStalkEquiv_originalResidueSquare :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    (tensorBranchStalkEquiv f x hU sq hV hVU y hy q).toRingHom.comp
        ((tensorBranchBaseMap f x hU y hy q).comp
          (originalResidueToStalk f x hU g y.1 hy)) =
      (actualFiberStalkMap f' y (tensorFiberEquiv f x hU sq hV hVU y hy q)).hom.comp
        (originalResidueToStalk f x hU g y.1 hy) := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  rw [← RingHom.comp_assoc, tensorBranchStalkEquiv_scalarSquare]

/-- The whole tensor/local-algebra comparison preserves the literal original
source numerator and the horizontal section map from the original source chart. -/
theorem residueTensorToLocalEquiv_sourceNumerator
    (b : IntegralGenericCoordinateFiber.sourceRing f x (U := U)) :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    residueTensorToLocalEquiv f x hU sq hV hVU y hy
        (1 ⊗ₜ[L] originalSourceNumerator f x hU b) =
      (1 : K) ⊗ₜ[C] FiniteCartesianAffineAlgebra.sourceSectionMap sq hVU b := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  change FiniteCartesianAffineAlgebra.wholeStalkToLocalEquiv (f' := f') hV y
      ((wholeStalkResidueEquiv f x hU sq hV hVU y hy).symm
        (1 ⊗ₜ[L] originalSourceNumerator f x hU b)) = _
  rw [← wholeStalkResidueEquiv_source f x hU sq hV hVU y hy 1 b,
    AlgEquiv.symm_apply_apply]
  exact FiniteCartesianAffineAlgebra.wholeStalkToLocalEquiv_source (f' := f') hV y _

/-- The source side of each branch comparison is also literal: the original
source residue numerator lands in the actual germ of its horizontal pullback. -/
theorem tensorBranchStalkEquiv_sourceNumerator :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
    ∀ (q : MaximalSpectrum T) (b : IntegralGenericCoordinateFiber.sourceRing f x (U := U)),
    tensorBranchStalkEquiv f x hU sq hV hVU y hy q
        (algebraMap T (Localization.AtPrime q.asIdeal)
          (1 ⊗ₜ[L] originalSourceNumerator f x hU b)) =
      X'.presheaf.germ (f' ⁻¹ᵁ V)
        (tensorFiberEquiv f x hU sq hV hVU y hy q).1
        (sourcePoint_mem f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q))
        (FiniteCartesianAffineAlgebra.sourceSectionMap sq hVU b) := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  dsimp only
  intro q b
  change localAlgebraStalkEquiv f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q)
      (maximalLocalizationEquiv (residueTensorToLocalEquiv f x hU sq hV hVU y hy) q
        (algebraMap T (Localization.AtPrime q.asIdeal)
          (1 ⊗ₜ[L] originalSourceNumerator f x hU b))) = _
  rw [maximalLocalizationEquiv_algebraMap, residueTensorToLocalEquiv_sourceNumerator]
  change localAlgebraStalkEquiv f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q)
      (algebraMap S (Localization.AtPrime
        (tensorMaximalEquiv f x hU sq hV hVU y hy q).asIdeal)
        (algebraMap D S (FiniteCartesianAffineAlgebra.sourceSectionMap sq hVU b))) = _
  rw [← IsScalarTower.algebraMap_apply D S
    (Localization.AtPrime (tensorMaximalEquiv f x hU sq hV hVU y hy q).asIdeal)]
  let := sourceGermAlgebra f' hV y (tensorMaximalEquiv f x hU sq hV hVU y hy q)
  exact (localAlgebraStalkEquiv f' hV y
    (tensorMaximalEquiv f x hU sq hV hVU y hy q)).commutes _

/-- Above an actual generic target point, every tensor branch is a generic
point of the actual exterior source scheme, by finite-fiber reflection. -/
def tensorGenericFiberEquiv (hygen : y.1 ∈ genericPoints Y') :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    MaximalSpectrum T ≃ {w : genericPoints X' // f' w.1 = y.1} := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  exact (tensorFiberEquiv f x hU sq hV hVU y hy).trans
    (Motivic.genericFiberEquiv f' ⟨y.1, hygen⟩)

/-- Generic reflection leaves the actual source fiber point unchanged. It
says nothing about genericity in any whole ambient product scheme. -/
@[simp] theorem tensorGenericFiberEquiv_val (hygen : y.1 ∈ genericPoints Y') :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    ((tensorGenericFiberEquiv f x hU sq hV hVU y hy hygen q).1 : X') =
      (tensorFiberEquiv f x hU sq hV hVU y hy q).1 := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  rfl

end ActualExterior

end Motivic.IntegralExteriorBranchTransport

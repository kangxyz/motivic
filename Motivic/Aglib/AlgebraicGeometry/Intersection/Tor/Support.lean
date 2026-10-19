/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkModules
public import Motivic.Aglib.AlgebraicGeometry.Intersection.PointedStalkTor
public import Motivic.Aglib.Algebra.Homology.TotalComplex.NatShapeSymmetry
public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteTor
public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.TripleAmbient
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FiniteGeneration
public import Motivic.Aglib.AlgebraicGeometry.Intersection.TransverseTor
public import Motivic.Aglib.AlgebraicGeometry.Intersection.Triple.DiagonalRegularity
public import Motivic.Aglib.Algebra.Category.ModuleCat.ScalarRestriction.Surjective

/-!
# Support of intersection Tor modules
-/

@[expose] public noncomputable section

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

namespace AlgebraicGeometry.Scheme.StalkDescent
open _root_.ModuleCat.SurjectiveScalarDescent

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The canonical ideal-quotient action agrees with the existing actual
surjective-stalk descent action through the forced quotient ring equivalence.
The comparison is the identity on the original additive group. -/
def _root_.ModuleCat.SurjectiveScalarDescent.quotientIdealModuleIso (f : R →+* S) (hf :
    Function.Surjective f)
    (I : Ideal R) (hI : I = RingHom.ker f) (M : ModuleCat.{u} R)
    (hM : I ≤ Module.annihilator R M) :
    _root_.ModuleCat.TorComparison.quotientModule I M hM ≅
      (ModuleCat.restrictScalars
        ((Ideal.quotEquivOfEq hI).trans (f.quotientKerEquivOfSurjective hf)).toRingHom).obj
        (descendedModule f hf M (hI ▸ hM)) := by
  let A := _root_.ModuleCat.TorComparison.quotientModule I M hM
  let B := (ModuleCat.restrictScalars
    ((Ideal.quotEquivOfEq hI).trans (f.quotientKerEquivOfSurjective hf)).toRingHom).obj
      (descendedModule f hf M (hI ▸ hM))
  let e : A ≃ₗ[R ⧸ I] B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        change r • (show M from x) = actionHom f hf M (hI ▸ hM) (f r) x
        exact (actionHom_apply_image f hf M (hI ▸ hM) r x).symm }
  exact e.toModuleIso

/-- The quotient-to-actual-stalk comparison is literally identity on elements. -/
theorem _root_.ModuleCat.SurjectiveScalarDescent.quotientIdealModuleIso_hom_apply (f : R →+* S) (hf
    : Function.Surjective f)
    (I : Ideal R) (hI : I = RingHom.ker f) (M : ModuleCat.{u} R)
    (hM : I ≤ Module.annihilator R M) (x : M) :
    (quotientIdealModuleIso f hf I hI M hM).hom x = x := rfl

/-- Finite ambient modules remain finite over their actual descended stalk
ring, with scalar compatibility proved from the surjective map itself. -/
instance _root_.ModuleCat.SurjectiveScalarDescent.descendedModule_finite (f : R →+* S) (hf :
    Function.Surjective f)
    (M : ModuleCat.{u} R) (hM : RingHom.ker f ≤ Module.annihilator R M)
    [Module.Finite R M] : Module.Finite S (descendedModule f hf M hM) := by
  let := f.toAlgebra
  let := moduleAction f hf M hM
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul
    (fun r x => actionHom_apply_image f hf M hM r x)
  exact Module.Finite.of_restrictScalars_finite R S M

end AlgebraicGeometry.Scheme.StalkDescent

namespace AlgebraicGeometry.Scheme.Intersection

variable {D T P : Scheme.{u}} (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T)
  (hp : i d = j t) [IsClosedImmersion i] [IsClosedImmersion j]

/-- The actual closed-stalk quotient presentations induce the genuine Tor
comparison, retaining coefficient-first/source-second order. -/
def quotientTorStalkIso (n : ℕ) :
    (((Tor (ModuleCat (ambientStalk i d)) n).obj
      (ModuleCat.of (ambientStalk i d) ((ambientStalk i d) ⧸
        RingHom.ker (coefficientStalkMap i d j t hp).hom))).obj
      (ModuleCat.of (ambientStalk i d) ((ambientStalk i d) ⧸
        RingHom.ker (i.stalkMap d).hom))) ≅
    (((Tor (ModuleCat (ambientStalk i d)) n).obj (coefficientStalkModule i d j t hp)).obj
      (sourceStalkModule i d)) :=
  ((Tor (ModuleCat (ambientStalk i d)) n).mapIso
      (coefficientKernelQuotientIso i d j t hp)).app _ ≪≫
    ((Tor (ModuleCat (ambientStalk i d)) n).obj (coefficientStalkModule i d j t hp)).mapIso
      (sourceKernelQuotientIso i d)

/-- Actual stalk Tor is the literal restriction of the existing canonical
support-quotient Tor module for the two actual stalk kernels. -/
def torSupportStalkRestrictIso (n : ℕ) :
    (((Tor (ModuleCat (ambientStalk i d)) n).obj (coefficientStalkModule i d j t hp)).obj
      (sourceStalkModule i d)) ≅
    (ModuleCat.restrictScalars (Ideal.Quotient.mk
      (RingHom.ker (i.stalkMap d).hom ⊔
        RingHom.ker (coefficientStalkMap i d j t hp).hom))).obj
      (_root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (i.stalkMap d).hom)
        (RingHom.ker (coefficientStalkMap i d j t hp).hom) n) :=
  (quotientTorStalkIso i d j t hp n).symm ≪≫
    _root_.ModuleCat.TorComparison.torSupportModuleRestrictIso _ _ n

/-- Both actual closed-stalk kernels annihilate their actual categorical Tor,
without requiring any regular list or coefficient flatness. -/
theorem stalkSupport_annihilates_tor (n : ℕ) :
    RingHom.ker (i.stalkMap d).hom ⊔ RingHom.ker (coefficientStalkMap i d j t hp).hom ≤
      Module.annihilator (ambientStalk i d)
        ((((Tor (ModuleCat (ambientStalk i d)) n).obj
          (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d))) :=
  (_root_.ModuleCat.TorComparison.quotient_support_le_annihilator _ _ n).trans
    ((quotientTorStalkIso i d j t hp n).hom.hom.annihilator_le_of_surjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- The canonical support Tor and the actual stalk Tor agree already as
modules over the full sum quotient, via the actual quotient presentations. -/
def torSupportStalkQuotientIso (n : ℕ) :
    _root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (i.stalkMap d).hom)
      (RingHom.ker (coefficientStalkMap i d j t hp).hom) n ≅
    _root_.ModuleCat.TorComparison.quotientModule
      (RingHom.ker (i.stalkMap d).hom ⊔ RingHom.ker (coefficientStalkMap i d j t hp).hom)
      ((((Tor (ModuleCat (ambientStalk i d)) n).obj
        (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)))
      (stalkSupport_annihilates_tor i d j t hp n) :=
  _root_.ModuleCat.TorComparison.quotientLinearIso _ _ _ (quotientTorStalkIso i d j t hp n)

variable (s : List (ambientStalk i d))
  (hker : RingHom.ker (i.stalkMap d).hom = Ideal.ofList s)
  (hs : IsRegular (ambientStalk i d) s)

/-- The canonical quotient-coordinate Tor computes actual regular-list
Koszul homology of the original coefficient stalk. -/
def quotientTorHomologyStalkIso (n : ℕ) :
    (((Tor (ModuleCat (ambientStalk i d)) n).obj
      (ModuleCat.of (ambientStalk i d) ((ambientStalk i d) ⧸
        RingHom.ker (coefficientStalkMap i d j t hp).hom))).obj
      (ModuleCat.of (ambientStalk i d) ((ambientStalk i d) ⧸
        RingHom.ker (i.stalkMap d).hom))) ≅
    (_root_.ChainComplex.Koszul.coefficientComplex (coefficientStalkModule i d j t hp) s).homology n
        :=
  quotientTorStalkIso i d j t hp n ≪≫ torIsoHomology i d j t hp s hker hs n

include hker hs in
/-- The actual full sum support annihilates Koszul homology via its canonical
Tor comparison; no radical replacement or homology assumption is used. -/
theorem stalkSupport_annihilates_homology (n : ℕ) :
    RingHom.ker (i.stalkMap d).hom ⊔ RingHom.ker (coefficientStalkMap i d j t hp).hom ≤
      Module.annihilator (ambientStalk i d)
        ((_root_.ChainComplex.Koszul.coefficientComplex (coefficientStalkModule i d j t hp)
            s).homology n) :=
  (_root_.ModuleCat.TorComparison.quotient_support_le_annihilator _ _ n).trans
    ((quotientTorHomologyStalkIso i d j t hp s hker hs n).hom.hom.annihilator_le_of_surjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- The actual Tor/Koszul comparison is linear over the precise sum quotient,
using the existing canonical Tor support action and canonical quotient lift. -/
def torSupportHomologyStalkIso (n : ℕ) :
    _root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (i.stalkMap d).hom)
      (RingHom.ker (coefficientStalkMap i d j t hp).hom) n ≅
    _root_.ModuleCat.TorComparison.quotientModule
      (RingHom.ker (i.stalkMap d).hom ⊔ RingHom.ker (coefficientStalkMap i d j t hp).hom)
      ((_root_.ChainComplex.Koszul.coefficientComplex (coefficientStalkModule i d j t hp)
          s).homology n)
      (stalkSupport_annihilates_homology i d j t hp s hker hs n) :=
  _root_.ModuleCat.TorComparison.quotientLinearIso _ _ _ (quotientTorHomologyStalkIso i d j t hp s
      hker hs n)

/-- Quotient descent preserves the exact original comparison on elements. -/
theorem torSupportHomologyStalkIso_hom_apply (n : ℕ)
    (x : _root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (i.stalkMap d).hom)
      (RingHom.ker (coefficientStalkMap i d j t hp).hom) n) :
    (torSupportHomologyStalkIso i d j t hp s hker hs n).hom x =
      (quotientTorHomologyStalkIso i d j t hp s hker hs n).hom x := rfl

/-- The original ambient Koszul homology is the actual restriction of the
canonical support Tor module; only homology, not ambient complex terms, descends. -/
def homologyStalkSupportRestrictIso (n : ℕ) :
    (_root_.ChainComplex.Koszul.coefficientComplex (coefficientStalkModule i d j t hp) s).homology n
        ≅
    (ModuleCat.restrictScalars (Ideal.Quotient.mk
      (RingHom.ker (i.stalkMap d).hom ⊔
        RingHom.ker (coefficientStalkMap i d j t hp).hom))).obj
      (_root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (i.stalkMap d).hom)
        (RingHom.ker (coefficientStalkMap i d j t hp).hom) n) :=
  (torIsoHomology i d j t hp s hker hs n).symm ≪≫ torSupportStalkRestrictIso i d j t hp n

/-- Genuine finite generation over the support quotient follows from canonical
finite Tor and the proved quotient-linear comparison. -/
theorem finite_stalkSupport_homology [IsNoetherianRing (ambientStalk i d)] (n : ℕ) :
    Module.Finite ((ambientStalk i d) ⧸
      (RingHom.ker (i.stalkMap d).hom ⊔ RingHom.ker (coefficientStalkMap i d j t hp).hom))
      (_root_.ModuleCat.TorComparison.quotientModule
        (RingHom.ker (i.stalkMap d).hom ⊔ RingHom.ker (coefficientStalkMap i d j t hp).hom)
        ((_root_.ChainComplex.Koszul.coefficientComplex (coefficientStalkModule i d j t hp)
            s).homology n)
        (stalkSupport_annihilates_homology i d j t hp s hker hs n)) :=
  Module.Finite.of_surjective (torSupportHomologyStalkIso i d j t hp s hker hs n).hom.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end AlgebraicGeometry.Scheme.Intersection

namespace AlgebraicGeometry.Scheme.Intersection

variable {V D T P : Scheme.{u}} (a : V ⟶ D) (b : V ⟶ T) (i : D ⟶ P) (j : T ⟶ P)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b i j)

include sq in
/-- The actual intersection inclusion has a surjective literal ambient stalk map. -/
theorem intersectionStalkMap_surjective (w : V) :
    Function.Surjective ((a ≫ i).stalkMap w).hom := by
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sq.flip inferInstance
  exact (a ≫ i).stalkMap_surjective w

/-- Canonical support Tor agrees with the existing actual intersection-stalk
descent action through the quotient equivalence forced by the literal stalk
map. The equality of its kernel with the actual sum support is proved. -/
def torSupportActualStalkIso (w : V) (n : ℕ) :
    let hp := point_eq a b i j sq w
    let I := RingHom.ker (i.stalkMap (a w)).hom ⊔
      RingHom.ker (coefficientStalkMap i (a w) j (b w) hp).hom
    let f : ambientStalk i (a w) →+* V.presheaf.stalk w := ((a ≫ i).stalkMap w).hom
    let hf := intersectionStalkMap_surjective a b i j sq w
    let hI : I = RingHom.ker f := (stalkMap_kernel_eq_sup a b i j sq w).symm
    let M := (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
      (coefficientStalkModule i (a w) j (b w) hp)).obj (sourceStalkModule i (a w)))
    let hM := stalkSupport_annihilates_tor i (a w) j (b w) hp n
    _root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (i.stalkMap (a w)).hom)
      (RingHom.ker (coefficientStalkMap i (a w) j (b w) hp).hom) n ≅
      (ModuleCat.restrictScalars
        ((Ideal.quotEquivOfEq hI).trans (f.quotientKerEquivOfSurjective hf)).toRingHom).obj
        (_root_.ModuleCat.SurjectiveScalarDescent.descendedModule f hf M (hI ▸ hM)) :=
  torSupportStalkQuotientIso i (a w) j (b w) (point_eq a b i j sq w) n ≪≫
    _root_.ModuleCat.SurjectiveScalarDescent.quotientIdealModuleIso _
        (intersectionStalkMap_surjective a b i j sq w) _
      (stalkMap_kernel_eq_sup a b i j sq w).symm _ _

end AlgebraicGeometry.Scheme.Intersection

namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- The genuine six-factor ambient is locally Noetherian over a locally
Noetherian base when the four original factors are locally finite type. -/
theorem isLocallyNoetherian_correspondenceSixfoldAmbient [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i] : IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i) := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian i
  have : IsLocallyNoetherian (pullback h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h i)
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h))

end AlgebraicGeometry.Scheme

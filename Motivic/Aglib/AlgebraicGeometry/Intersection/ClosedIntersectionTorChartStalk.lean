/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedIntersectionTorLocalization
public import Motivic.Aglib.AlgebraicGeometry.Modules.Restriction.Open.RestrictionStalk

/-!
# Actual stalks of closed-intersection Tor chart sheaves

The canonical stalk of the genuinely constructed chart sheaf is identified with
supported geometric Tor. All scalar changes use the original affine chart and
open inclusion stalk maps. Finite generation is distinct from finite length.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward

open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison
open _root_.AlgebraicGeometry.Scheme.Modules.Stalk

variable {X : Scheme.{u}} (U : X.affineOpens) (x : U.1)

/-- The actual structure-stalk isomorphism from the affine spectrum to the original scheme. -/
def affineOpenStructureStalkIso :
    (Spec Γ(X, U)).presheaf.stalk (U.2.isoSpec.hom x) ≅ X.presheaf.stalk x.1 :=
  asIso (U.2.isoSpec.hom.stalkMap x) ≪≫ U.1.stalkIso x

/-- The affine structure-stalk identification retains the literal section germ. -/
@[reassoc] theorem affineOpenStructureStalkIso_germ :
    CommRingCat.ofHom (algebraMap Γ(X, U)
        ((Spec Γ(X, U)).presheaf.stalk (U.2.isoSpec.hom x))) ≫
      (affineOpenStructureStalkIso U x).hom = X.presheaf.germ U.1 x.1 x.2 := by
  change (Scheme.ΓSpecIso Γ(X, U)).inv ≫
    (Spec Γ(X, U)).presheaf.germ ⊤ (U.2.isoSpec.hom x) (by trivial) ≫
      U.2.isoSpec.hom.stalkMap x ≫ (U.1.stalkIso x).hom = _
  rw [Scheme.Hom.germ_stalkMap_assoc]
  change (Scheme.ΓSpecIso Γ(X, U)).inv ≫
    U.2.isoSpec.hom.appTop ≫ U.1.toScheme.presheaf.germ ⊤ x (by trivial) ≫
      (U.1.stalkIso x).hom = _
  rw [IsAffineOpen.isoSpec_hom_appTop, Category.assoc, Iso.inv_hom_id_assoc,
    Scheme.Opens.germ_stalkIso_hom]
  dsimp [Scheme.Opens.topIso]
  rw [TopCat.Presheaf.germ_res]

/-- The inverse affine stalk ring map is the original inclusion followed by the
inverse original affine-chart stalk map. -/
theorem affineOpenStructureStalkIso_inv :
    (affineOpenStructureStalkIso U x).inv =
      U.1.ι.stalkMap x ≫ inv (U.2.isoSpec.hom.stalkMap x) := by
  simp only [affineOpenStructureStalkIso, Iso.trans_inv, asIso_inv,
    Scheme.Opens.stalkIso_inv]

/-- Extension to the affine spectrum stalk followed by its actual ring isomorphism
is extension along the original section germ. -/
def affineOpenStalkExtensionIso (M : ModuleCat.{u} Γ(X, U)) :
    (ModuleCat.restrictScalars (affineOpenStructureStalkIso U x).inv.hom).obj
      ((ModuleCat.extendScalars (algebraMap Γ(X, U)
        ((Spec Γ(X, U)).presheaf.stalk (U.2.isoSpec.hom x)))).obj M) ≅
      (ModuleCat.extendScalars (X.presheaf.germ U.1 x.1 x.2).hom).obj M := by
  let e := (affineOpenStructureStalkIso U x).commRingCatIsoToRingEquiv
  let f := algebraMap Γ(X, U) ((Spec Γ(X, U)).presheaf.stalk (U.2.isoSpec.hom x))
  have h : e.toRingHom.comp f = (X.presheaf.germ U.1 x.1 x.2).hom :=
    congrArg CommRingCat.Hom.hom (affineOpenStructureStalkIso_germ U x)
  exact (extendScalarsRingEquivIso e ((ModuleCat.extendScalars f).obj M)).symm ≪≫
    (ModuleCat.extendScalarsComp f e.toRingHom).symm.app M ≪≫
      eqToIso (congrArg (fun g => (ModuleCat.extendScalars g).obj M) h)

/-- The actual stalk of the affine-open tilde sheaf, with the original ambient
structure-stalk action, is its scalar extension along the literal germ. -/
def affineOpenTildeStalkIso (M : ModuleCat.{u} Γ(X, U)) :
    (ModuleCat.restrictScalars (U.1.ι.stalkMap x).hom).obj
      ((functor x).obj
        ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj ((tilde.functor Γ(X, U)).obj M))) ≅
      (ModuleCat.extendScalars (X.presheaf.germ U.1 x.1 x.2).hom).obj M := by
  let p := U.2.isoSpec.hom x
  let S := (Spec Γ(X, U)).presheaf.stalk p
  let f := algebraMap Γ(X, U) S
  exact (ModuleCat.restrictScalars (U.1.ι.stalkMap x).hom).mapIso
      ((openRestrictionIso U.2.isoSpec.hom x).app ((tilde.functor Γ(X, U)).obj M)) ≪≫
    (ModuleCat.restrictScalarsComp (U.1.ι.stalkMap x).hom
      (inv (U.2.isoSpec.hom.stalkMap x)).hom).symm.app _ ≪≫
    (ModuleCat.restrictScalarsCongr
      (congrArg CommRingCat.Hom.hom (affineOpenStructureStalkIso_inv U x)).symm).app _ ≪≫
    (ModuleCat.restrictScalars (affineOpenStructureStalkIso U x).inv.hom).mapIso
      ((Affine.tildeStalkIso Γ(X, U) p).app M).symm ≪≫
    (ModuleCat.restrictScalars (affineOpenStructureStalkIso U x).inv.hom).mapIso
      (extendScalarsTensorIso f M).symm ≪≫
    affineOpenStalkExtensionIso U x M

/-- Finite affine coordinates give finite generation of the genuine affine-open
stalk, with no finite-length assertion. -/
theorem affineOpenTildeStalk_finite (M : ModuleCat.{u} Γ(X, U))
    [Module.Finite Γ(X, U) M] :
    Module.Finite (X.presheaf.stalk x.1)
      ((ModuleCat.restrictScalars (U.1.ι.stalkMap x).hom).obj
        ((functor x).obj
          ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
            ((tilde.functor Γ(X, U)).obj M)))) := by
  let f := (X.presheaf.germ U.1 x.1 x.2).hom
  let := f.toAlgebra
  let e := affineOpenTildeStalkIso U x M ≪≫ extendScalarsTensorIso f M
  exact Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap
    e.symm.toLinearEquiv.surjective

variable {D T P V : Scheme.{u}} (i : D ⟶ P) (j : T ⟶ P)
  [IsClosedImmersion i] [IsClosedImmersion j]
  (a : V ⟶ D) (b : V ⟶ T) (sq : IsPullback a b i j)

/-- The actual chart-sheaf stalk, restricted along its original open inclusion
stalk map to the actual original intersection structure ring. -/
abbrev closedIntersectionTorChartStalk (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (n : ℕ) : ModuleCat.{u} (V.presheaf.stalk w) :=
  (ModuleCat.restrictScalars (((a ≫ i) ⁻¹ᵁ U).ι.stalkMap ⟨w, hw⟩).hom).obj
    ((functor (X := ((a ≫ i) ⁻¹ᵁ U).toScheme) ⟨w, hw⟩).obj
      (closedIntersectionTorChartSheaf j a b i sq U n))

/-- The constructed chart-sheaf stalk is the existing supported geometric Tor,
through the literal chart inclusion and section germ in every degree. -/
def closedIntersectionTorChartStalkIso (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    closedIntersectionTorChartStalk i j a b sq U w hw n ≅
      closedIntersectionSupportedStalkTor i j a b sq w n :=
  affineOpenTildeStalkIso (closedIntersectionAffineOpen j a b i sq U) ⟨w, hw⟩
    (closedIntersectionAffineTor j a b i sq U n) ≪≫
      closedIntersectionAffineTorStalkIso i j a b sq U w hw n

/-- The same actual chart-sheaf stalk recovers the original ambient Tor after
restriction along the original ambient intersection stalk map. -/
def closedIntersectionTorChartAmbientStalkIso (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    (ModuleCat.restrictScalars ((a ≫ i).stalkMap w).hom).obj
      (closedIntersectionTorChartStalk i j a b sq U w hw n) ≅
      (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
        (sourceStalkModule i (a w))) :=
  (ModuleCat.restrictScalars ((a ≫ i).stalkMap w).hom).mapIso
    (closedIntersectionTorChartStalkIso i j a b sq U w hw n) ≪≫
      closedIntersectionSupportedStalkTorRestrictIso i j a b sq w n

/-- Noetherian affine ambient coordinates imply finite actual sheaf stalks. -/
theorem closedIntersectionTorChartStalk_finite (U : P.affineOpens)
    [IsNoetherianRing Γ(P, U)] (w : V) (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    Module.Finite (V.presheaf.stalk w)
      (closedIntersectionTorChartStalk i j a b sq U w hw n) := by
  have : Module.Finite Γ(V, (closedIntersectionAffineOpen j a b i sq U).1)
      (closedIntersectionAffineTor j a b i sq U n) :=
    closedIntersectionAffineTor_finite j a b i sq U n
  exact affineOpenTildeStalk_finite (closedIntersectionAffineOpen j a b i sq U) ⟨w, hw⟩
    (closedIntersectionAffineTor j a b i sq U n)

/-- Locally Noetherian ambient geometry supplies genuine chart-sheaf stalk finiteness. -/
instance closedIntersectionTorChartStalk_finite_of_locallyNoetherian
    [IsLocallyNoetherian P] (U : P.affineOpens)
    (w : V) (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    Module.Finite (V.presheaf.stalk w)
      (closedIntersectionTorChartStalk i j a b sq U w hw n) := by
  let := IsLocallyNoetherian.component_noetherian U
  exact closedIntersectionTorChartStalk_finite i j a b sq U w hw n

/-- Finiteness passes through the exact chart-sheaf stalk attachment to the
existing supported geometric Tor module. -/
theorem closedIntersectionSupportedStalkTor_finite (U : P.affineOpens)
    [IsNoetherianRing Γ(P, U)] (w : V) (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    Module.Finite (V.presheaf.stalk w) (closedIntersectionSupportedStalkTor i j a b sq w n) := by
  have := closedIntersectionTorChartStalk_finite i j a b sq U w hw n
  let e := closedIntersectionTorChartStalkIso i j a b sq U w hw n
  exact Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)

end AlgebraicGeometry.Scheme.Intersection

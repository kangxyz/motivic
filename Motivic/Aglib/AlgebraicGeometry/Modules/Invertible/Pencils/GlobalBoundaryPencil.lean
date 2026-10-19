/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.ProperQuasiAffine
public import Motivic.Aglib.AlgebraicGeometry.Modules.ZeroBaseChange
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Fibrewise

/-! # Global pencils of actual line-bundle maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules.Invertible.GlobalBoundaryPencil

/-- The global pencil is formed in the original module-sheaf category. -/
def pencil {X : Scheme.{u}} {M : X.Modules}
    (a b : M ⟶ SheafOfModules.unit X.ringCatSheaf) (t : Γ(X, ⊤)) :
    M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  a + (b - a) ≫ unitMul X t

@[simp] theorem pencil_zero {X : Scheme.{u}} {M : X.Modules}
    (a b : M ⟶ SheafOfModules.unit X.ringCatSheaf) : pencil a b 0 = a := by
  simp [pencil]

@[simp] theorem pencil_one {X : Scheme.{u}} {M : X.Modules}
    (a b : M ⟶ SheafOfModules.unit X.ringCatSheaf) : pencil a b 1 = b := by
  simp [pencil, unitMul_one]

/-- Equal boundary restrictions remain exactly equal along the global pencil.
This is equality of actual sheaf morphisms, not of Picard classes. -/
theorem pullback_pencil_eq_of_eq {X B : Scheme.{u}} (i : B ⟶ X) {M : X.Modules}
    (a b : M ⟶ SheafOfModules.unit X.ringCatSheaf) (t : Γ(X, ⊤))
    (h : (Scheme.Modules.pullback i).map a ≫ (pullbackUnitIso i).hom =
      (Scheme.Modules.pullback i).map b ≫ (pullbackUnitIso i).hom) :
    (Scheme.Modules.pullback i).map (pencil a b t) ≫ (pullbackUnitIso i).hom =
      (Scheme.Modules.pullback i).map a ≫ (pullbackUnitIso i).hom := by
  have hab := (cancel_mono (pullbackUnitIso i).hom).mp h
  simp [pencil, Functor.map_add, Functor.map_sub, hab]

/-- Original global scalar multiplication commutes with arbitrary scheme
pullback, using the canonical unit comparison. -/
theorem pullback_unitMul {X Y : Scheme.{u}} (f : X ⟶ Y) (t : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (unitMul Y t) ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso f).hom ≫ unitMul X (f.appTop t) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackUnitIso_homEquiv]
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change Γ(Y, U) at r
  change (f.app U) (r * (Y.presheaf.map (homOfLE le_top).op) t) =
    (f.app U r) * (X.presheaf.map (homOfLE le_top).op) (f.appTop t)
  rw [map_mul]
  congr 1
  have h : Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ f.app U =
      f.appTop ≫ X.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  exact congrArg (fun k => CommRingCat.Hom.hom k t) h

/-- Pullback carries the actual global pencil to the pencil of the actual
pulled-back maps and the pulled-back parameter. -/
theorem pullback_pencil {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (a b : M ⟶ SheafOfModules.unit Y.ringCatSheaf) (t : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (pencil a b t) ≫ (pullbackUnitIso f).hom =
      pencil ((Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom)
        ((Scheme.Modules.pullback f).map b ≫ (pullbackUnitIso f).hom) (f.appTop t) := by
  simp only [pencil, Functor.map_add, Functor.map_comp, Functor.map_sub,
    Preadditive.add_comp, Category.assoc, pullback_unitMul, Preadditive.sub_comp]

/-- Zero loci here are the actual image-ideal subschemes of the constructed map. -/
def zeroScheme {X : Scheme.{u}} (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) (t : Γ(X, ⊤)) : Scheme.{u} :=
  Scheme.Modules.Hom.zeroScheme (pencil a b t)


/-- Pulling back along a section retains the original module-to-unit map. -/
theorem section_pullback_map {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y)
    (h : s ≫ p = 𝟙 Y) {M : Y.Modules}
    (a : M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback s).map
        ((Scheme.Modules.pullback p).map a ≫ (pullbackUnitIso p).hom) ≫
        (pullbackUnitIso s).hom = (sectionPullbackIso s p h).hom.app M ≫ a := by
  have hu : (sectionPullbackIso s p h).hom.app
      (SheafOfModules.unit Y.ringCatSheaf) =
      (Scheme.Modules.pullback s).map (pullbackUnitIso p).hom ≫
        (pullbackUnitIso s).hom := by
    simp only [sectionPullbackIso, Iso.trans_hom, NatTrans.comp_app]
    rw [pullbackUnitIso_id, pullbackUnitIso_congr, pullbackUnitIso_comp]
  rw [Functor.map_comp, Category.assoc, ← hu]
  exact (sectionPullbackIso s p h).hom.naturality a

/-- Ordered pullback of a module-to-unit map agrees with composite pullback. -/
theorem pullback_map_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (a : M ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback g).map a ≫ (pullbackUnitIso g).hom) ≫
        (pullbackUnitIso f).hom =
    (Scheme.Modules.pullbackComp f g).hom.app M ≫
      (Scheme.Modules.pullback (f ≫ g)).map a ≫ (pullbackUnitIso (f ≫ g)).hom := by
  rw [Functor.map_comp, Category.assoc, ← pullbackUnitIso_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    (Scheme.Modules.pullbackComp f g).hom.naturality_assoc a
      (pullbackUnitIso (f ≫ g)).hom

theorem pullback_map_eq_comp_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Z.Modules} (a b : M ⟶ N) :
    (Scheme.Modules.pullback (f ≫ g)).map a =
      (Scheme.Modules.pullback (f ≫ g)).map b ↔
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a) =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map b) := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f g).hom.app M)]
  rw [← (Scheme.Modules.pullbackComp f g).hom.naturality a,
    ← (Scheme.Modules.pullbackComp f g).hom.naturality b]
  exact cancel_mono _

/-- The actual relative affine line over the compactified curve. -/
abbrev parameterSpace (X : Scheme.{u}) := AffineSpace (ULift.{u} Unit) X

/-- The actual parameterized map, in the pulled-back original line bundle. -/
def familyMap {X : Scheme.{u}} (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (pullbackLineBundle (parameterSpace X ↘ X) L).val ⟶
      SheafOfModules.unit (parameterSpace X).ringCatSheaf :=
  pencil ((Scheme.Modules.pullback (parameterSpace X ↘ X)).map a ≫
      (pullbackUnitIso (parameterSpace X ↘ X)).hom)
    ((Scheme.Modules.pullback (parameterSpace X ↘ X)).map b ≫
      (pullbackUnitIso (parameterSpace X ↘ X)).hom)
    (AffineSpace.coord X (ULift.up ()))

/-- Evaluation is the genuine affine-line section, not an abstract endpoint. -/
def endpoint (X : Scheme.{u}) (c : Γ(X, ⊤)) : X ⟶ parameterSpace X :=
  AffineSpace.homOfVector (𝟙 X) (fun _ ↦ c)

@[reassoc (attr := simp)] theorem endpoint_projection (X : Scheme.{u}) (c : Γ(X, ⊤)) :
    endpoint X c ≫ (parameterSpace X ↘ X) = 𝟙 X :=
  AffineSpace.homOfVector_over _ _

/-- The actual sheaf-map fibre at zero is the original first section. -/
theorem familyMap_zero {X : Scheme.{u}} (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback (endpoint X 0)).map (familyMap L a b) ≫
      (pullbackUnitIso (endpoint X 0)).hom =
    (sectionPullbackIso (endpoint X 0) (parameterSpace X ↘ X)
      (endpoint_projection X 0)).hom.app L.val ≫ a := by
  unfold familyMap
  rw [pullback_pencil]
  simp only [endpoint, AffineSpace.homOfVector_appTop_coord, pencil_zero]
  exact section_pullback_map _ _ _ a

/-- The actual sheaf-map fibre at one is the original second section. -/
theorem familyMap_one {X : Scheme.{u}} (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback (endpoint X 1)).map (familyMap L a b) ≫
      (pullbackUnitIso (endpoint X 1)).hom =
    (sectionPullbackIso (endpoint X 1) (parameterSpace X ↘ X)
      (endpoint_projection X 1)).hom.app L.val ≫ b := by
  unfold familyMap
  rw [pullback_pencil]
  simp only [endpoint, AffineSpace.homOfVector_appTop_coord, pencil_one]
  exact section_pullback_map _ _ _ b

/-- Exact equality on the original boundary fixes that whole boundary throughout
 the actual affine-line family. No reduction or pointwise replacement is used. -/
theorem familyMap_boundary {X B : Scheme.{u}} (i : B ⟶ X) (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : (Scheme.Modules.pullback i).map a ≫ (pullbackUnitIso i).hom =
      (Scheme.Modules.pullback i).map b ≫ (pullbackUnitIso i).hom) :
    (Scheme.Modules.pullback (AffineSpace.map (ULift.{u} Unit) i)).map (familyMap L a b) ≫
      (pullbackUnitIso (AffineSpace.map (ULift.{u} Unit) i)).hom =
    (Scheme.Modules.pullback (AffineSpace.map (ULift.{u} Unit) i)).map
      ((Scheme.Modules.pullback (parameterSpace X ↘ X)).map a ≫
        (pullbackUnitIso (parameterSpace X ↘ X)).hom) ≫
      (pullbackUnitIso (AffineSpace.map (ULift.{u} Unit) i)).hom := by
  apply pullback_pencil_eq_of_eq
  have hab := (cancel_mono (pullbackUnitIso i).hom).mp h
  have hc : (Scheme.Modules.pullback ((parameterSpace B ↘ B) ≫ i)).map a =
      (Scheme.Modules.pullback ((parameterSpace B ↘ B) ≫ i)).map b :=
    (pullback_map_eq_comp_iff _ _ a b).mpr (congrArg
      ((Scheme.Modules.pullback (parameterSpace B ↘ B)).map) hab)
  rw [← AffineSpace.map_over (n := ULift.{u} Unit) i] at hc
  have hd := (pullback_map_eq_comp_iff _ _ a b).mp hc
  simp only [Functor.map_comp, Category.assoc, hd]

/-- An invertible common boundary value stays invertible throughout the family. -/
theorem familyMap_boundary_isIso {X B : Scheme.{u}} (i : B ⟶ X) (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (h : (Scheme.Modules.pullback i).map a ≫ (pullbackUnitIso i).hom =
      (Scheme.Modules.pullback i).map b ≫ (pullbackUnitIso i).hom) :
    IsIso ((Scheme.Modules.pullback (AffineSpace.map (ULift.{u} Unit) i)).map
      (familyMap L a b) ≫ (pullbackUnitIso (AffineSpace.map (ULift.{u} Unit) i)).hom) := by
  rw [familyMap_boundary i L a b h, pullback_map_comp]
  have : IsIso ((Scheme.Modules.pullback ((parameterSpace B ↘ B) ≫ i)).map a) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp (parameterSpace B ↘ B) i) a).mp
      (inferInstanceAs (IsIso ((Scheme.Modules.pullback (parameterSpace B ↘ B)).map
        ((Scheme.Modules.pullback i).map a))))
  have : IsIso ((Scheme.Modules.pullback
      (AffineSpace.map (ULift.{u} Unit) i ≫ (parameterSpace X ↘ X))).map a) := by
    exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackCongr
      (AffineSpace.map_over (n := ULift.{u} Unit) i)) a).mpr this
  infer_instance

/-- The constructed zero family avoids the entire scheme-theoretic boundary. -/
theorem familyMap_boundary_zero_isEmpty {X B : Scheme.{u}} (i : B ⟶ X) (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (h : (Scheme.Modules.pullback i).map a ≫ (pullbackUnitIso i).hom =
      (Scheme.Modules.pullback i).map b ≫ (pullbackUnitIso i).hom) :
    IsEmpty (Limits.pullback (AffineSpace.map (ULift.{u} Unit) i)
      (Hom.zeroInclusion (familyMap L a b)) : Scheme.{u}) := by
  let E := pullbackLineBundle (parameterSpace X ↘ X) L
  let := lineBundle_isLocallyFree (parameterSpace X) E
  let : IsIso (Hom.pullbackToUnit (familyMap L a b)
      (AffineSpace.map (ULift.{u} Unit) i)) := familyMap_boundary_isIso i L a b h
  exact Hom.isEmpty_pullback_zeroInclusion (familyMap L a b)
    (AffineSpace.map (ULift.{u} Unit) i)

/-- The same construction works with any actual global parameter, in particular
with the polynomial coordinate on the correspondence library's literal line. -/
theorem pencil_finite_flat_on_open {X B U S : Scheme.{u}} (i : B ⟶ X)
    (q : X ⟶ S) [IsProper q] [IsAffine S]
    (j : U ⟶ X) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) (t : Γ(X, ⊤))
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (h : (Scheme.Modules.pullback i).map a ≫ (pullbackUnitIso i).hom =
      (Scheme.Modules.pullback i).map b ≫ (pullbackUnitIso i).hom)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit (pencil a b t) j) ≫ j ≫ q) ∧
      Mono (Hom.pullbackToUnit (pencil a b t) j) ∧
      Flat (Hom.zeroInclusion (Hom.pullbackToUnit (pencil a b t) j) ≫ j ≫ q) := by
  let := lineBundle_isLocallyFree X L
  have : IsIso (Hom.pullbackToUnit (pencil a b t) i) := by
    change IsIso ((Scheme.Modules.pullback i).map (pencil a b t) ≫ (pullbackUnitIso i).hom)
    rw [pullback_pencil_eq_of_eq i a b t h]
    infer_instance
  let : IsEmpty (Limits.pullback i (Hom.zeroInclusion (pencil a b t)) : Scheme.{u}) :=
    Hom.isEmpty_pullback_zeroInclusion (pencil a b t) i
  apply finite_mono_flat_on_open_of_proper q j L (pencil a b t)
  rintro x ⟨z, rfl⟩
  rcases hcover (Hom.zeroInclusion (pencil a b t) z) with hx | hx
  · exact hx
  · have hz : z ∈ Set.range (Limits.pullback.snd i (Hom.zeroInclusion (pencil a b t))) := by
      rw [Scheme.Pullback.range_snd]
      exact hx
    obtain ⟨w, _⟩ := hz
    exact isEmptyElim w

/-- A genuine global pencil with a common invertible boundary value produces a
finite flat Cartier zero family on the smooth quasi-affine retained open.
Only the retained open is smooth; properness belongs to the compactification. -/
theorem family_finite_flat_on_open {X B U S : Scheme.{u}} (i : B ⟶ X)
    (q : parameterSpace X ⟶ S) [IsProper q] [IsAffine S]
    (j : U ⟶ parameterSpace X) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle X)
    (a b : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    (h : (Scheme.Modules.pullback i).map a ≫ (pullbackUnitIso i).hom =
      (Scheme.Modules.pullback i).map b ≫ (pullbackUnitIso i).hom)
    (hcover : ∀ x : parameterSpace X, x ∈ Set.range j ∨
      x ∈ Set.range (AffineSpace.map (ULift.{u} Unit) i)) :
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit (familyMap L a b) j) ≫ j ≫ q) ∧
      Mono (Hom.pullbackToUnit (familyMap L a b) j) ∧
      Flat (Hom.zeroInclusion (Hom.pullbackToUnit (familyMap L a b) j) ≫ j ≫ q) := by
  apply finite_mono_flat_on_open_of_proper q j
    (pullbackLineBundle (parameterSpace X ↘ X) L) (familyMap L a b)
  rintro x ⟨z, rfl⟩
  rcases hcover (Hom.zeroInclusion (familyMap L a b) z) with hx | hx
  · exact hx
  · let : IsEmpty (Limits.pullback (AffineSpace.map (ULift.{u} Unit) i)
        (Hom.zeroInclusion (familyMap L a b)) : Scheme.{u}) :=
      familyMap_boundary_zero_isEmpty i L a b h
    have hz : z ∈ Set.range (Limits.pullback.snd
        (AffineSpace.map (ULift.{u} Unit) i) (Hom.zeroInclusion (familyMap L a b))) := by
      rw [Scheme.Pullback.range_snd]
      exact hx
    obtain ⟨w, _⟩ := hz
    exact isEmptyElim w

end AlgebraicGeometry.Scheme.Modules.Invertible.GlobalBoundaryPencil

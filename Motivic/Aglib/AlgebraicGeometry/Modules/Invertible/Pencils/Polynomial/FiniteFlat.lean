/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.Geometry

/-! # Finite-flat zeros of the literal polynomial pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible GlobalBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (b : X ⟶ Spec (.of R))

/-- Equality on the original boundary gives equality on its literal polynomial base change. -/
theorem familyMap_boundary {B : Scheme.{u}} (i : B ⟶ X) (L : LineBundle X)
    (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit c i) :
    Hom.pullbackToUnit (familyMap b L a c) (parameterMap b i) =
      Hom.pullbackToUnit (Hom.pullbackToUnit a (projection b)) (parameterMap b i) := by
  apply pullback_pencil_eq_of_eq
  have hab := (cancel_mono (pullbackUnitIso i).hom).mp h
  have hc : (Modules.pullback (projection (i ≫ b) ≫ i)).map a =
      (Modules.pullback (projection (i ≫ b) ≫ i)).map c :=
    (pullback_map_eq_comp_iff _ _ a c).mpr
      (congrArg ((Modules.pullback (projection (i ≫ b))).map) hab)
  rw [← parameterMap_projection b i] at hc
  have hd := (pullback_map_eq_comp_iff _ _ a c).mp hc
  simp only [Hom.pullbackToUnit, Functor.map_comp, Category.assoc, hd]

/-- The common invertible boundary value is invertible for the whole polynomial family. -/
theorem familyMap_boundary_isIso {B : Scheme.{u}} (i : B ⟶ X) (L : LineBundle X)
    (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((Modules.pullback i).map a)]
    (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit c i) :
    IsIso (Hom.pullbackToUnit (familyMap b L a c) (parameterMap b i)) := by
  rw [familyMap_boundary b i L a c h]
  change IsIso ((Modules.pullback (parameterMap b i)).map
    ((Modules.pullback (projection b)).map a ≫ (pullbackUnitIso (projection b)).hom) ≫ _)
  rw [pullback_map_comp]
  have : IsIso ((Modules.pullback (projection (i ≫ b) ≫ i)).map a) :=
    (NatIso.isIso_map_iff (Modules.pullbackComp (projection (i ≫ b)) i) a).mp
      (inferInstanceAs (IsIso ((Modules.pullback (projection (i ≫ b))).map
        ((Modules.pullback i).map a))))
  have : IsIso ((Modules.pullback (parameterMap b i ≫ projection b)).map a) := by
    exact (NatIso.isIso_map_iff (Modules.pullbackCongr (parameterMap_projection b i)) a).mpr this
  infer_instance

/-- The literal polynomial zero family is finite flat and regular on the
retained smooth quasi-affine open, proved from properness and boundary units. -/
theorem family_finite_flat_on_open {B U S : Scheme.{u}} (i : B ⟶ X)
    (q : parameterSpace b ⟶ S) [IsProper q] [IsAffine S]
    (j : U ⟶ parameterSpace b) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle X)
    (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((Modules.pullback i).map a)]
    (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit c i)
    (hcover : ∀ x : parameterSpace b, x ∈ Set.range j ∨ x ∈ Set.range (parameterMap b i)) :
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit (familyMap b L a c) j) ≫ j ≫ q) ∧
      Mono (Hom.pullbackToUnit (familyMap b L a c) j) ∧
      Flat (Hom.zeroInclusion (Hom.pullbackToUnit (familyMap b L a c) j) ≫ j ≫ q) := by
  apply finite_mono_flat_on_open_of_proper q j
    (pullbackLineBundle (projection b) L) (familyMap b L a c)
  rintro x ⟨z, rfl⟩
  rcases hcover (Hom.zeroInclusion (familyMap b L a c) z) with hx | hx
  · exact hx
  · have := familyMap_boundary_isIso b i L a c h
    let := lineBundle_isLocallyFree (parameterSpace b) (pullbackLineBundle (projection b) L)
    let : IsEmpty (Limits.pullback (parameterMap b i) (Hom.zeroInclusion (familyMap b L a c)) :
        Scheme.{u}) := Hom.isEmpty_pullback_zeroInclusion (familyMap b L a c) (parameterMap b i)
    have hz : z ∈ Set.range (pullback.snd (parameterMap b i)
        (Hom.zeroInclusion (familyMap b L a c))) := by
      rw [Scheme.Pullback.range_snd]
      exact hx
    obtain ⟨w, _⟩ := hz
    exact isEmptyElim w

/-- The canonical module comparison for restricting the polynomial family to an open. -/
def restrictionPullbackIso {D : Scheme.{u}} (j : D ⟶ X) :
    Modules.pullback (projection b) ⋙ Modules.pullback (parameterMap b j) ≅
      Modules.pullback j ⋙ Modules.pullback (projection (j ≫ b)) :=
  Modules.pullbackComp (parameterMap b j) (projection b) ≪≫
    Modules.pullbackCongr (parameterMap_projection b j) ≪≫
      (Modules.pullbackComp (projection (j ≫ b)) j).symm

/-- The comparison retains the actual unit maps, not just the bundle class. -/
theorem restrictionPullbackIso_unit {D : Scheme.{u}} (j : D ⟶ X) :
    (restrictionPullbackIso b j).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Modules.pullback (projection (j ≫ b))).map (pullbackUnitIso j).hom ≫
          (pullbackUnitIso (projection (j ≫ b))).hom =
      (Modules.pullback (parameterMap b j)).map (pullbackUnitIso (projection b)).hom ≫
        (pullbackUnitIso (parameterMap b j)).hom := by
  rw [← pullbackUnitIso_comp, ← pullbackUnitIso_comp]
  simp only [restrictionPullbackIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [pullbackUnitIso_congr]

/-- The actual twice-pulled module-to-unit map respects the comparison. -/
theorem restrictionPullbackIso_map {D : Scheme.{u}} (j : D ⟶ X) {M : X.Modules}
    (a : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Hom.pullbackToUnit (Hom.pullbackToUnit a (projection b)) (parameterMap b j) =
      (restrictionPullbackIso b j).hom.app M ≫
        Hom.pullbackToUnit (Hom.pullbackToUnit a j) (projection (j ≫ b)) := by
  simp only [Hom.pullbackToUnit, Functor.map_comp, Category.assoc]
  rw [← restrictionPullbackIso_unit b j]
  simpa only [Functor.comp_map, Category.assoc] using
    ((restrictionPullbackIso b j).hom.naturality_assoc a
      ((Modules.pullback (projection (j ≫ b))).map (pullbackUnitIso j).hom ≫
        (pullbackUnitIso (projection (j ≫ b))).hom))

/-- The literal polynomial coordinate is unchanged by the retained-open map. -/
theorem parameterMap_parameter {D : Scheme.{u}} (j : D ⟶ X) :
    (parameterMap b j).appTop (parameter b) = parameter (j ≫ b) := by
  unfold parameter
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, parameterMap_snd]

/-- Restricting the actual global family is the actual retained family with the
canonical comparison of its original source modules. -/
theorem familyMap_restriction {D : Scheme.{u}} (j : D ⟶ X) (L : LineBundle X)
    (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Hom.pullbackToUnit (familyMap b L a c) (parameterMap b j) =
      (restrictionPullbackIso b j).hom.app L.val ≫
        familyMap (j ≫ b) (pullbackLineBundle j L)
          (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j) := by
  change (Modules.pullback _).map (pencil _ _ _) ≫ _ = _
  rw [pullback_pencil, parameterMap_parameter]
  change pencil (Hom.pullbackToUnit (Hom.pullbackToUnit a (projection b)) (parameterMap b j))
    (Hom.pullbackToUnit (Hom.pullbackToUnit c (projection b)) (parameterMap b j)) _ = _
  rw [restrictionPullbackIso_map, restrictionPullbackIso_map]
  dsimp only [familyMap, pencil]
  rw [Preadditive.comp_add, ← Category.assoc, Preadditive.comp_sub]

/-- Actual zero-scheme identification for restriction of the literal polynomial family. -/
def restrictionZeroIso {D : Scheme.{u}} (j : D ⟶ X) (L : LineBundle X)
    (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Hom.zeroScheme (Hom.pullbackToUnit (familyMap b L a c) (parameterMap b j)) ≅
      Hom.zeroScheme (familyMap (j ≫ b) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) :=
  eqToIso (congrArg Hom.zeroScheme (familyMap_restriction b j L a c)) ≪≫
    zeroSchemePrecompIso ((restrictionPullbackIso b j).app L.val)
      (familyMap (j ≫ b) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j))

@[reassoc] theorem restrictionZeroIso_hom_inclusion {D : Scheme.{u}} (j : D ⟶ X)
    (L : LineBundle X) (a c : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (restrictionZeroIso b j L a c).hom ≫ Hom.zeroInclusion
        (familyMap (j ≫ b) (pullbackLineBundle j L)
          (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) =
      Hom.zeroInclusion (Hom.pullbackToUnit (familyMap b L a c) (parameterMap b j)) := by
  simp only [restrictionZeroIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    zeroSchemePrecompIso_hom_inclusion, Iso.app_hom]
  exact zeroScheme_congr_inclusion (familyMap_restriction b j L a c)

/-- Original proper compactification and smooth quasi-affine retained open give
finite-flat zeros for the actual restricted polynomial family. -/
theorem retained_family_finite_flat {S C D B : Scheme.{u}} (bS : S ⟶ Spec (.of R))
    [IsAffine S] (q : C ⟶ S) [IsProper q]
    (j : D ⟶ C) [IsOpenImmersion j] [D.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (i : B ⟶ C)
    (L : LineBundle C) (a c : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Modules.pullback i).map a)]
    (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit c i)
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i) :
    let f := familyMap (j ≫ q ≫ bS) (pullbackLineBundle j L)
      (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)
    let p := parameterMap (q ≫ bS) j ≫ parameterMap bS q
    IsFinite (Hom.zeroInclusion f ≫ p) ∧ Flat (Hom.zeroInclusion f ≫ p) := by
  have := parameterSpace_quasiAffine (j ≫ q ≫ bS)
  have : SmoothOfRelativeDimension 1 (parameterMap (q ≫ bS) j ≫ parameterMap bS q) :=
    MorphismProperty.of_isPullback
      ((parameterMap_isPullback (q ≫ bS) j).paste_horiz
        (parameterMap_isPullback bS q)).flip inferInstance
  obtain ⟨hf, _, hg⟩ := family_finite_flat_on_open (q ≫ bS) i (parameterMap bS q)
    (parameterMap (q ≫ bS) j) L a c h (parameter_cover (q ≫ bS) i j hcover)
  let e := restrictionZeroIso (q ≫ bS) j L a c
  have he : e.inv ≫
      Hom.zeroInclusion (Hom.pullbackToUnit (familyMap (q ≫ bS) L a c)
        (parameterMap (q ≫ bS) j)) =
      Hom.zeroInclusion (familyMap (j ≫ q ≫ bS) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) := by
    rw [Iso.inv_comp_eq]
    exact (restrictionZeroIso_hom_inclusion (q ≫ bS) j L a c).symm
  have hfin : IsFinite (e.inv ≫
      (Hom.zeroInclusion (Hom.pullbackToUnit (familyMap (q ≫ bS) L a c)
        (parameterMap (q ≫ bS) j)) ≫ parameterMap (q ≫ bS) j ≫ parameterMap bS q)) :=
    inferInstance
  have hflat : Flat (e.inv ≫
      (Hom.zeroInclusion (Hom.pullbackToUnit (familyMap (q ≫ bS) L a c)
        (parameterMap (q ≫ bS) j)) ≫ parameterMap (q ≫ bS) j ≫ parameterMap bS q)) :=
    inferInstance
  exact ⟨by simpa only [← Category.assoc e.inv, he] using hfin,
    by simpa only [← Category.assoc e.inv, he] using hflat⟩

/-- Canonical identification of parameter spaces for equal structural maps. -/
def parameterCongr {D : Scheme.{u}} {b₁ b₂ : D ⟶ Spec (.of R)} (h : b₁ = b₂) :
    parameterSpace b₁ ≅ parameterSpace b₂ := eqToIso (congrArg parameterSpace h)

@[reassoc (attr := simp)] theorem parameterCongr_projection {D : Scheme.{u}}
    {b₁ b₂ : D ⟶ Spec (.of R)} (h : b₁ = b₂) :
    (parameterCongr h).hom ≫ projection b₂ = projection b₁ := by
  subst b₂
  simp [parameterCongr]

@[reassoc (attr := simp)] theorem parameterCongr_snd {D : Scheme.{u}}
    {b₁ b₂ : D ⟶ Spec (.of R)} (h : b₁ = b₂) :
    (parameterCongr h).hom ≫ pullback.snd b₂ (Spec.map (CommRingCat.ofHom Polynomial.C)) =
      pullback.snd b₁ (Spec.map (CommRingCat.ofHom Polynomial.C)) := by
  subst b₂
  simp [parameterCongr]

/-- Literal composition of polynomial parameter maps includes the canonical
associativity identification of the source parameter scheme. -/
theorem parameterMap_comp {C D : Scheme.{u}} (q : C ⟶ X) (j : D ⟶ C) :
    (parameterCongr (Category.assoc j q b)).hom ≫
      parameterMap (q ≫ b) j ≫ parameterMap b q = parameterMap b (j ≫ q) := by
  apply pullback.hom_ext
  · change _ ≫ projection b = _ ≫ projection b
    simp only [Category.assoc, parameterMap_projection, parameterMap_projection_assoc,
      parameterCongr_projection_assoc]
  · simp only [Category.assoc, parameterMap_snd, parameterCongr_snd]

/-- Equal original structural maps identify their whole polynomial zero schemes. -/
def familyZeroCongr {D : Scheme.{u}} {b₁ b₂ : D ⟶ Spec (.of R)} (h : b₁ = b₂)
    (L : LineBundle D) (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    Hom.zeroScheme (familyMap b₁ L a c) ≅ Hom.zeroScheme (familyMap b₂ L a c) := by
  subst b₂
  exact Iso.refl _

@[reassoc] theorem familyZeroCongr_hom_inclusion {D : Scheme.{u}}
    {b₁ b₂ : D ⟶ Spec (.of R)} (h : b₁ = b₂) (L : LineBundle D)
    (a c : L.val ⟶ SheafOfModules.unit D.ringCatSheaf) :
    (familyZeroCongr h L a c).hom ≫ Hom.zeroInclusion (familyMap b₂ L a c) =
      Hom.zeroInclusion (familyMap b₁ L a c) ≫ (parameterCongr h).hom := by
  subst b₂
  simp [familyZeroCongr, parameterCongr]

/-- The original-base structural map of the actual retained family is finite
flat. This is the exact `familySource` expression used by finite correspondences. -/
theorem retained_familySource_finite_flat {S C D B : Scheme.{u}} (bS : S ⟶ Spec (.of R))
    [IsAffine S] (q : C ⟶ S) [IsProper q]
    (j : D ⟶ C) [IsOpenImmersion j] [D.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (i : B ⟶ C)
    (L : LineBundle C) (a c : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Modules.pullback i).map a)]
    (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit c i)
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i) :
    let f := familyMap ((j ≫ q) ≫ bS) (pullbackLineBundle j L)
      (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)
    IsFinite (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) := by
  obtain ⟨hf, hg⟩ := retained_family_finite_flat bS q j i L a c h hcover
  let e := familyZeroCongr (Category.assoc j q bS) (pullbackLineBundle j L)
    (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)
  have he : e.hom ≫ Hom.zeroInclusion (familyMap (j ≫ q ≫ bS) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) ≫
        parameterMap (q ≫ bS) j ≫ parameterMap bS q =
      Hom.zeroInclusion (familyMap ((j ≫ q) ≫ bS) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) ≫ parameterMap bS (j ≫ q) := by
    rw [familyZeroCongr_hom_inclusion_assoc]
    exact congrArg (fun m => Hom.zeroInclusion
      (familyMap ((j ≫ q) ≫ bS) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) ≫ m) (parameterMap_comp bS q j)
  have hfin : IsFinite (e.hom ≫ Hom.zeroInclusion
      (familyMap (j ≫ q ≫ bS) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) ≫
      parameterMap (q ≫ bS) j ≫ parameterMap bS q) := inferInstance
  have hflat : Flat (e.hom ≫ Hom.zeroInclusion
      (familyMap (j ≫ q ≫ bS) (pullbackLineBundle j L)
        (Hom.pullbackToUnit a j) (Hom.pullbackToUnit c j)) ≫
      parameterMap (q ≫ bS) j ≫ parameterMap bS q) := inferInstance
  exact ⟨he ▸ hfin, he ▸ hflat⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil

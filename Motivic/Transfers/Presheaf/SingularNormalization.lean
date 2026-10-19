/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.SingularComplex.Sheafification
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Normalization
public import Motivic.Aglib.CategoryTheory.FullSubcategoryHomotopy
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Normalization of singular complexes with actual transfers

The full simplex category, including codegeneracies, acts on actual singular
transfer presheaves. Normalize in the abelian category of ordinary presheaves
on `Cor`, then use the explicit Moore splitting to prove that each normalized
term remains additive in correspondences. The inclusion, retraction, and both
homotopies lift to the full subcategory of transfer presheaves. Applying actual
additive Nisnevich sheafification preserves this genuine homotopy equivalence.
No abelian-category instance for sheaves with transfers is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicTopology
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The full simplicial transfer presheaf, with maps for every simplex operator. -/
def singularSimplicial (P : PresheafWithTransfers.{v} k) :
    SimplicialObject (PresheafWithTransfers.{v} k) where
  obj n := singularTerm P n.unop.len
  map f := ⟨{
    app U := (SingularComplex.simplicial (Cor.simplexProductCosimplicial U.unop) P.obj).map f
    naturality U V α := by
      change transfer P (Cor.simplexExterior _ α.unop) ≫
          transfer P ((Cor.simplexProductCosimplicial V.unop).map f.unop) =
        transfer P ((Cor.simplexProductCosimplicial U.unop).map f.unop) ≫
          transfer P (Cor.simplexExterior _ α.unop)
      rw [← transfer_comp, ← transfer_comp]
      exact congrArg (transfer P) ((Cor.simplexExteriorNatTrans α.unop).naturality f.unop) }⟩
  map_id n := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (SingularComplex.simplicial (Cor.simplexProductCosimplicial U.unop) P.obj).map_id n
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (SingularComplex.simplicial (Cor.simplexProductCosimplicial U.unop) P.obj).map_comp f g

@[simp]
theorem singularSimplicial_obj (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (singularSimplicial P).obj (op ⦋n⦌) = (singularComplex P).X n := rfl

@[simp]
theorem singularSimplicial_δ (P : PresheafWithTransfers.{v} k) (n : ℕ)
    (i : Fin (n + 2)) : (singularSimplicial P).δ i = singularFace P n i := rfl

/-- Codegeneracies are genuine transfer-natural maps, not only objectwise maps. -/
@[simp]
theorem singularSimplicial_σ_app (P : PresheafWithTransfers.{v} k) (n : ℕ)
    (i : Fin (n + 1)) (U : Cor k) :
    ((singularSimplicial P).σ i).hom.app (op U) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).σ i))) := rfl

/-- Alternating faces of the full simplicial transfer object recover the original complex. -/
def singularSimplicialAlternatingIso (P : PresheafWithTransfers.{v} k) :
    (alternatingFaceMapComplex (PresheafWithTransfers.{v} k)).obj (singularSimplicial P) ≅
      singularComplex P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    obtain rfl : j + 1 = i := hij
    rw [singularComplex_d]
    change _ = (AlternatingFaceMapComplex.obj (singularSimplicial P)).d (j + 1) j
    rw [AlternatingFaceMapComplex.obj_d_eq]
    rfl)

/-- Forget only the bundled additivity property; every actual transfer is retained. -/
abbrev singularAmbientSimplicial (P : PresheafWithTransfers.{v} k) :
    SimplicialObject ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  singularSimplicial P ⋙ forget

/-- The ordinary Moore complex on the full correspondence category. -/
abbrev normalizedSingularAmbient (P : PresheafWithTransfers.{v} k) :
    ChainComplex ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  (normalizedMooreComplex _).obj (singularAmbientSimplicial P)

/-- The normalized summand is additive in every signed correspondence. -/
instance normalizedSingularAmbient_X_additive (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    ((normalizedSingularAmbient P).X n).Additive := by
  let i := (inclusionOfMooreComplexMap (singularAmbientSimplicial P)).f n
  let p := (DoldKan.PInftyToNormalizedMooreComplex (singularAmbientSimplicial P)).f n
  have h : i ≫ p = 𝟙 _ :=
    HomologicalComplex.congr_hom
      (DoldKan.splitMonoInclusionOfMooreComplexMap (singularAmbientSimplicial P)).id n
  let : (((alternatingFaceMapComplex _).obj (singularAmbientSimplicial P)).X n).Additive :=
    (singularTerm P n).property
  exact Functor.additive_of_retract i p h

/-- The normalized Moore singular complex has actual additive transfer actions. -/
def normalizedSingularComplex (P : PresheafWithTransfers.{v} k) :
    ChainComplex (PresheafWithTransfers.{v} k) ℕ :=
  HomologicalComplex.liftObjectProperty (additiveFunctor _ _) (normalizedSingularAmbient P)
    (fun n => normalizedSingularAmbient_X_additive P n)

/-- Lift the unnormalized ambient complex without changing any differential. -/
abbrev singularAmbientAlternatingLift (P : PresheafWithTransfers.{v} k) :
    ChainComplex (PresheafWithTransfers.{v} k) ℕ :=
  HomologicalComplex.liftObjectProperty (additiveFunctor _ _)
    ((alternatingFaceMapComplex _).obj (singularAmbientSimplicial P))
    (fun n => (singularTerm P n).property)

/-- The full simplicial alternating complex is the already constructed actual singular complex. -/
def singularAlternatingIso (P : PresheafWithTransfers.{v} k) :
    singularAmbientAlternatingLift P ≅ singularComplex P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    obtain rfl : j + 1 = i := hij
    rw [singularComplex_d]
    apply ObjectProperty.hom_ext
    change (∑ a : Fin (j + 2), (-1 : ℤ) ^ (a : ℕ) • singularFace P j a).hom = _
    change _ = (AlternatingFaceMapComplex.obj (singularAmbientSimplicial P)).d (j + 1) j
    rw [AlternatingFaceMapComplex.obj_d_eq]
    change forget.map (∑ a : Fin (j + 2), (-1 : ℤ) ^ (a : ℕ) • singularFace P j a) = _
    simp only [Functor.map_sum, Functor.map_zsmul]
    rfl)

/-- The Moore inclusion, its retraction, and actual homotopies all respect transfers. -/
def singularNormalizationHomotopyEquiv (P : PresheafWithTransfers.{v} k) :
    HomotopyEquiv (normalizedSingularComplex P) (singularComplex P) :=
  (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := singularAmbientSimplicial P)).liftObjectProperty (additiveFunctor _ _)
      (fun n => normalizedSingularAmbient_X_additive P n)
      (fun n => (singularTerm P n).property) |>.trans
        (HomotopyEquiv.ofIso (singularAlternatingIso P))

/-- The canonical actual normalization inclusion. -/
def singularNormalizationInclusion (P : PresheafWithTransfers.{v} k) :
    normalizedSingularComplex P ⟶ singularComplex P :=
  (singularNormalizationHomotopyEquiv P).hom

/-- The forward comparison retains the original Moore inclusion component. -/
@[simp]
theorem singularNormalizationInclusion_f_hom (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    ((singularNormalizationInclusion P).f n).hom =
      (inclusionOfMooreComplexMap (singularAmbientSimplicial P)).f n := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Whenever these homology objects are chosen, the actual inclusion is a quasi-isomorphism. -/
instance singularNormalizationInclusion_quasiIso (P : PresheafWithTransfers.{v} k)
    [∀ n, (normalizedSingularComplex P).HasHomology n]
    [∀ n, (singularComplex P).HasHomology n] :
    QuasiIso (singularNormalizationInclusion P) :=
  (singularNormalizationHomotopyEquiv P).quasiIso_hom

/-- Degreewise actual transfer sheafification of normalized chains. -/
def normalizedSingularSheafComplex (P : PresheafWithTransfers.{u + 1} k) :
    ChainComplex (SheafWithTransfers.{u + 1} k) ℕ :=
  ((nisnevichSheafify k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (normalizedSingularComplex P)

/-- Actual additive transfer sheafification carries both normalization homotopies. -/
def singularSheafNormalizationHomotopyEquiv (P : PresheafWithTransfers.{u + 1} k) :
    HomotopyEquiv (normalizedSingularSheafComplex P) (singularSheafComplex k P) :=
  (nisnevichSheafify k).mapHomotopyEquiv (singularNormalizationHomotopyEquiv P)

/-- Place normalized chain degree `r` in cochain degree `q-r`. -/
def normalizedSingularCochainComplex (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  (normalizedSingularComplex P).extend (ComplexShape.embeddingUpIntLE (q : ℤ))

/-- Zero extension preserves the actual normalization equivalence in every weight. -/
def singularCochainNormalizationHomotopyEquiv (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    HomotopyEquiv (normalizedSingularCochainComplex P q) (singularCochainComplex P q) :=
  (singularNormalizationHomotopyEquiv P).extend (ComplexShape.embeddingUpIntLE (q : ℤ))

/-- Normalized transfer cochains have the same genuine signed placement comparison. -/
def normalizedSingularCochainShiftIso (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    normalizedSingularCochainComplex P q ≅
      (normalizedSingularCochainComplex P 0)⟦-(q : ℤ)⟧ :=
  _root_.HomologicalComplex.ExtensionSignedShift.iso (normalizedSingularComplex P) q

/-- Actual sheafification of placed normalized transfer chains. -/
def normalizedSingularSheafCochainComplex (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  ((nisnevichSheafify k).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (normalizedSingularCochainComplex P q)

/-- The normalized and existing sheafified transfer cochains are actually homotopy equivalent. -/
def singularSheafCochainNormalizationHomotopyEquiv
    (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    HomotopyEquiv (normalizedSingularSheafCochainComplex P q)
      (singularSheafCochainComplex k P q) :=
  (nisnevichSheafify k).mapHomotopyEquiv (singularCochainNormalizationHomotopyEquiv P q)

/-- Signed shifts of the sheafified complexes preserve both normalization homotopies. -/
def singularSheafShiftedNormalizationHomotopyEquiv
    (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    HomotopyEquiv ((normalizedSingularSheafCochainComplex P 0)⟦-(q : ℤ)⟧)
      ((singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧) :=
  (singularSheafCochainNormalizationHomotopyEquiv P 0).shift (-(q : ℤ))

/-- Conditional only on chosen homology, the sheafified placed comparison is a quasi-isomorphism. -/
instance singularSheafCochainNormalization_quasiIso
    (P : PresheafWithTransfers.{u + 1} k) (q : ℕ)
    [∀ i, (normalizedSingularSheafCochainComplex P q).HasHomology i]
    [∀ i, (singularSheafCochainComplex k P q).HasHomology i] :
    QuasiIso (singularSheafCochainNormalizationHomotopyEquiv P q).hom :=
  (singularSheafCochainNormalizationHomotopyEquiv P q).quasiIso_hom

end Motivic.PresheafWithTransfers

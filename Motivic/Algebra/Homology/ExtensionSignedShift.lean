/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Degree placement and signed cochain shifts

Extending a nonnegative chain complex along `r ↦ q - r` preserves its
original differential. The usual cochain shift by `-q` multiplies its
differential by `(-1)^q`. The two constructions are naturally isomorphic,
with component `(-1)^(q*r)` on the original chain term of degree `r`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Motivic.ExtensionSignedShift

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]

/-- An isomorphism multiplied in both directions by an integer sign. -/
def signIso {X Y : A} (e : X ≅ Y) (n : ℤ) : X ≅ Y where
  hom := n.negOnePow • e.hom
  inv := n.negOnePow • e.inv
  hom_inv_id := by simp [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  inv_hom_id := by simp [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]

/-- The shifted weight-zero term identified with chain degree `r`. -/
def shiftedXIso (K : ChainComplex A ℕ) (q : ℕ) {i : ℤ} (r : ℕ)
    (h : (q : ℤ) - r = i) :
    (((K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).X i) ≅ K.X r :=
  K.extendXIso (ComplexShape.embeddingUpIntLE 0) (by
    change (0 : ℤ) - r = i + -(q : ℤ)
    omega)

/-- Both placements vanish in degrees strictly above the weight. -/
theorem isZero_shifted_X (K : ChainComplex A ℕ) (q : ℕ) (i : ℤ)
    (h : (q : ℤ) < i) :
    IsZero (((K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).X i) := by
  change IsZero ((K.extend (ComplexShape.embeddingUpIntLE 0)).X (i + -(q : ℤ)))
  apply K.isZero_extend_X
  exact (ComplexShape.notMem_range_embeddingUpIntLE_iff 0 _).2 (by omega)

/-- Component of the signed comparison in every integer degree. -/
def componentIso (K : ChainComplex A ℕ) (q : ℕ) (i : ℤ) :
    (K.extend (ComplexShape.embeddingUpIntLE (q : ℤ))).X i ≅
      (((K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).X i) :=
  if h : i ≤ (q : ℤ) then
    signIso
      (K.extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
          (i := ((q : ℤ) - i).toNat) (by
            change (q : ℤ) - ↑((q : ℤ) - i).toNat = i
            omega) ≪≫
        (shiftedXIso K q ((q : ℤ) - i).toNat (by omega)).symm)
      ((q : ℤ) * ((q : ℤ) - i))
  else
    IsZero.iso
      (K.isZero_extend_X _ i
        ((ComplexShape.notMem_range_embeddingUpIntLE_iff _ _).2 (by omega)))
      (isZero_shifted_X K q i (by omega))

/-- The comparison has sign `(-1)^(q*r)` at the chain term of degree `r`. -/
theorem componentIso_hom (K : ChainComplex A ℕ) (q r : ℕ) :
    (componentIso K q ((q : ℤ) - r)).hom =
      ((q : ℤ) * r).negOnePow •
        ((K.extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
          (i' := (q : ℤ) - r) (ComplexShape.embeddingUpIntLE_f (q : ℤ) r)).hom ≫
          (shiftedXIso K q r rfl).inv) := by
  unfold componentIso
  rw [dite_eq_left (by omega)]
  dsimp only [signIso, Iso.trans_hom, Iso.symm_hom]
  simp only [sub_sub_cancel]
  congr 4 <;> first | omega | exact proof_irrel_heq _ _


/-- The shifted differential carries exactly mathlib's shift sign. -/
theorem shifted_d (K : ChainComplex A ℕ) (q r s : ℕ) :
    ((K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
        ((q : ℤ) - r) ((q : ℤ) - s) =
      (-(q : ℤ)).negOnePow •
        ((shiftedXIso K q r rfl).hom ≫ K.d r s ≫ (shiftedXIso K q s rfl).inv) := by
  rw [CochainComplex.shiftFunctor_obj_d']
  congr 1
  exact K.extend_d_eq (ComplexShape.embeddingUpIntLE 0)
    (by change (0 : ℤ) - r = (q : ℤ) - r + -(q : ℤ); omega)
    (by change (0 : ℤ) - s = (q : ℤ) - s + -(q : ℤ); omega)

/-- The degreewise signs compensate for the signed differential. -/
theorem componentIso_comm_succ (K : ChainComplex A ℕ) (q r : ℕ) :
    (componentIso K q ((q : ℤ) - (r + 1 : ℕ))).hom ≫
        ((K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
          ((q : ℤ) - (r + 1 : ℕ)) ((q : ℤ) - r) =
      (K.extend (ComplexShape.embeddingUpIntLE (q : ℤ))).d
          ((q : ℤ) - (r + 1 : ℕ)) ((q : ℤ) - r) ≫
        (componentIso K q ((q : ℤ) - r)).hom := by
  rw [componentIso_hom, componentIso_hom, shifted_d,
    K.extend_d_eq (ComplexShape.embeddingUpIntLE (q : ℤ))
      (i := r + 1) (j := r) (i' := (q : ℤ) - (r + 1 : ℕ))
      (j' := (q : ℤ) - r) rfl rfl]
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul,
    Iso.inv_hom_id_assoc, smul_smul, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
    Int.negOnePow_add, Int.negOnePow_neg]
  rw [mul_left_comm, Int.units_mul_self, mul_one]

/-- The actual signed comparison isomorphism of cochain complexes. -/
def iso (K : ChainComplex A ℕ) (q : ℕ) :
    K.extend (ComplexShape.embeddingUpIntLE (q : ℤ)) ≅
      (K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents (componentIso K q) (by
    intro i j hij
    change i + 1 = j at hij
    by_cases hj : j ≤ (q : ℤ)
    · let r := ((q : ℤ) - j).toNat
      have hr : (q : ℤ) - r = j := by dsimp [r]; omega
      have hi : (q : ℤ) - (r + 1 : ℕ) = i := by omega
      rw [← hi, ← hr]
      exact componentIso_comm_succ K q r
    · exact (isZero_shifted_X K q j (by omega)).eq_of_tgt _ _)

/-- Explicit signed component of the cochain comparison. -/
theorem iso_hom_f (K : ChainComplex A ℕ) (q r : ℕ) :
    (iso K q).hom.f ((q : ℤ) - r) =
      ((q : ℤ) * r).negOnePow •
        ((K.extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
          (i' := (q : ℤ) - r) (ComplexShape.embeddingUpIntLE_f (q : ℤ) r)).hom ≫
          (shiftedXIso K q r rfl).inv) :=
  componentIso_hom K q r

/-- The shifted extension of a chain map has the original component. -/
theorem shiftedMap_f {K L : ChainComplex A ℕ} (φ : K ⟶ L) (q r : ℕ) :
    ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-(q : ℤ))).map
        (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE 0))).f
        ((q : ℤ) - r) =
      (shiftedXIso K q r rfl).hom ≫ φ.f r ≫ (shiftedXIso L q r rfl).inv := by
  rw [CochainComplex.shiftFunctor_map_f']
  exact HomologicalComplex.extendMap_f φ (ComplexShape.embeddingUpIntLE 0)
    (by change (0 : ℤ) - r = (q : ℤ) - r + -(q : ℤ); omega)

/-- The signed comparison commutes with every chain map. -/
theorem iso_naturality {K L : ChainComplex A ℕ} (φ : K ⟶ L) (q : ℕ) :
    HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE (q : ℤ)) ≫
        (iso L q).hom =
      (iso K q).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-(q : ℤ))).map
          (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE 0)) := by
  ext i
  change (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE (q : ℤ))).f i ≫
      (componentIso L q i).hom = (componentIso K q i).hom ≫ _
  by_cases hi : i ≤ (q : ℤ)
  · let r := ((q : ℤ) - i).toNat
    have hr : (q : ℤ) - r = i := by dsimp [r]; omega
    rw [← hr, HomologicalComplex.extendMap_f φ (ComplexShape.embeddingUpIntLE (q : ℤ))
      (i := r) (i' := (q : ℤ) - r) rfl, componentIso_hom, componentIso_hom, shiftedMap_f]
    simp [Category.assoc]
  · exact (K.isZero_extend_X (ComplexShape.embeddingUpIntLE (q : ℤ)) i
      ((ComplexShape.notMem_range_embeddingUpIntLE_iff _ _).2 (by omega))).eq_of_src _ _

/-- Natural signed comparison between extension at weight `q` and shifted weight zero. -/
def naturalIso (q : ℕ) :
    (ComplexShape.embeddingUpIntLE (q : ℤ)).extendFunctor A ≅
      (ComplexShape.embeddingUpIntLE 0).extendFunctor A ⋙
        CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-(q : ℤ)) :=
  NatIso.ofComponents (fun K => iso K q) (fun φ => iso_naturality φ q)

end Motivic.ExtensionSignedShift

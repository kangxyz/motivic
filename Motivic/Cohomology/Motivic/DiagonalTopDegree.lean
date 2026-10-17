/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.FieldTopDegree
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The actual diagonal field group as a zero-cycle quotient

For every weight over every field, the literal reduced torus zero-cycles modulo
its degree-one singular differential compute the original derived diagonal
motivic cohomology. The signed cochain differential is explicitly `(-1)^q`
times the singular differential; the sign disappears only on its image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.DiagonalTopDegree

open PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original base-field object in the actual correspondence category. -/
abbrev point : Cor k := Cor.mk (SmoothSite.base (Spec (.of k)))

/-- The genuine singular chain group, retaining the actual identity-axis quotient. -/
abbrev chains (q r : ℕ) := sections (reducedTorus k q) (Cor.simplexProduct (point k) r)

/-- The genuine alternating boundary on the original reduced torus. -/
def boundary (q : ℕ) : chains k q 1 →+ chains k q 0 :=
  ((singularObj (reducedTorus k q) (point k)).d 1 0).hom

/-- The defining two endpoint terms have their original alternating signs. -/
theorem boundary_eq_endpoints (q : ℕ) (x : chains k q 1) :
    boundary k q x =
      transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ 0) x -
        transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ 1) x := by
  have h : (singularObj (reducedTorus k q) (point k)).d 1 0 = _ :=
    SingularComplex.obj_d_one_zero _ _
  exact ConcreteCategory.congr_hom h x

/-- The literal quotient `C₀ / im(d₁)`, before any derived comparison. -/
abbrev zeroHomology (q : ℕ) := chains k q 0 ⧸ (boundary k q).range

/-- The signed raw top term has no outgoing differential. -/
theorem raw_outgoing_d_zero (q : ℕ) :
    (motivicRawBaseComplex k q).d q ((q : ℤ) + 1) = 0 :=
  (FieldTopDegree.isZero_raw_X k ((q : ℤ) + 1) q (by omega)).eq_of_tgt _ _

/-- The canonical class of a top raw term in its original homology. -/
def rawClass (q : ℕ) : (motivicRawBaseComplex k q).X q ⟶
    (motivicRawBaseComplex k q).homology q :=
  ((motivicRawBaseComplex k q).iCyclesIso q ((q : ℤ) + 1)
      ((ComplexShape.up ℤ).next_eq' (by simp)) (raw_outgoing_d_zero k q)).inv ≫
    (motivicRawBaseComplex k q).homologyπ q

/-- The canonical raw class annihilates the actual signed preceding differential. -/
theorem differential_rawClass (q : ℕ) :
    (motivicRawBaseComplex k q).d ((q : ℤ) - 1) q ≫ rawClass k q = 0 := by
  rw [rawClass, ← (motivicRawBaseComplex k q).toCycles_i ((q : ℤ) - 1) q]
  simp only [Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
    HomologicalComplex.toCycles_comp_homologyπ]

/-- Every actual raw homology class has a top-term representative. -/
theorem rawClass_surjective (q : ℕ) : Function.Surjective (rawClass k q) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  unfold rawClass
  infer_instance

/-- The kernel is exactly the preceding signed raw differential, not an assumed relation. -/
theorem rawClass_eq_zero_iff (q : ℕ) (x : (motivicRawBaseComplex k q).X q) :
    rawClass k q x = 0 ↔ ∃ y : (motivicRawBaseComplex k q).X ((q : ℤ) - 1),
      (motivicRawBaseComplex k q).d ((q : ℤ) - 1) q y = x := by
  let K := motivicRawBaseComplex k q
  let S := ShortComplex.mk (K.toCycles ((q : ℤ) - 1) q) (K.homologyπ q)
    (K.toCycles_comp_homologyπ ((q : ℤ) - 1) q)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.homologyIsCokernel ((q : ℤ) - 1) q
      ((ComplexShape.up ℤ).prev_eq' (by simp)))
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := S.ab_exact_iff.mp hS
      (((K.iCyclesIso q ((q : ℤ) + 1)
        ((ComplexShape.up ℤ).next_eq' (by simp)) (raw_outgoing_d_zero k q)).inv) x) hx
    refine ⟨y, ?_⟩
    have h := congrArg (K.iCycles q) hy
    simpa only [S, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCyclesIso_inv_hom_id, ConcreteCategory.id_apply] using h
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom (differential_rawClass k q) y

/-- The genuine shift has precisely the sign `(-1)^q` in every occupied degree. -/
theorem raw_d (q r t : ℕ) :
    (motivicRawBaseComplex k q).d (Indexing.singularDegree q r)
        (Indexing.singularDegree q t) =
      (-1 : ℤ) ^ q • ((motivicRawBaseComplexXIso k q r).hom ≫
        (singularObj (reducedTorus k q) (point k)).d r t ≫
          (motivicRawBaseComplexXIso k q t).inv) := by
  let E := toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))
  calc
    _ = E.map (((singularCochainComplex (reducedTorus k q) 0)⟦-(q : ℤ)⟧).d
        (Indexing.singularDegree q r) (Indexing.singularDegree q t)) := by
      simp only [CochainComplex.shiftFunctor_obj_d', Units.smul_def,
        CategoryTheory.Functor.map_zsmul]
      rfl
    _ = _ := by
      change E.map
          ((((singularComplex (reducedTorus k q)).extend
            (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
              ((q : ℤ) - r) ((q : ℤ) - t)) =
        (-1 : ℤ) ^ q •
          (E.map (ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q r rfl).hom ≫
            E.map ((singularComplex (reducedTorus k q)).d r t) ≫
            E.map (ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q t rfl).inv)
      simpa only [Units.smul_def, CategoryTheory.Functor.map_zsmul,
        CategoryTheory.Functor.map_comp, Int.negOnePow_neg, Int.coe_negOnePow_natCast] using
        congrArg (fun f => E.map f)
          (ExtensionSignedShift.shifted_d (singularComplex (reducedTorus k q)) q r t)

/-- The top term isomorphism with its degree arithmetic resolved. -/
def topTermIso (q : ℕ) : (motivicRawBaseComplex k q).X q ≅ chains k q 0 :=
  eqToIso (by rw [Indexing.singularDegree_zero]) ≪≫ motivicRawBaseComplexXIso k q 0

/-- The preceding term isomorphism with its degree arithmetic resolved. -/
def previousTermIso (q : ℕ) :
    (motivicRawBaseComplex k q).X ((q : ℤ) - 1) ≅ chains k q 1 :=
  motivicRawBaseComplexXIso k q 1

/-- The top signed differential is the transported actual singular boundary. -/
theorem raw_d_top (q : ℕ) :
    (motivicRawBaseComplex k q).d ((q : ℤ) - 1) q =
      (-1 : ℤ) ^ q • ((previousTermIso k q).hom ≫ AddCommGrpCat.ofHom (boundary k q) ≫
        (topTermIso k q).inv) := by
  let e : (motivicRawBaseComplex k q).X q ≅
      (motivicRawBaseComplex k q).X (Indexing.singularDegree q 0) :=
    eqToIso (by rw [Indexing.singularDegree_zero])
  have h := congrArg (fun f => f ≫ e.inv) (raw_d k q 1 0)
  have he : (motivicRawBaseComplex k q).d (Indexing.singularDegree q 1)
      (Indexing.singularDegree q 0) ≫ e.inv =
        (motivicRawBaseComplex k q).d ((q : ℤ) - 1) q := by
    exact (motivicRawBaseComplex k q).d_comp_eqToHom
      (by change (q : ℤ) - 1 + 1 = q; omega)
      (by change (q : ℤ) - 1 + 1 = (q : ℤ) - 0; omega)
  rw [he] at h
  simpa only [Preadditive.zsmul_comp, Category.assoc, topTermIso, previousTermIso,
    boundary, Iso.trans_inv, AddCommGrpCat.ofHom_hom] using h

/-- A literal zero-cycle has its class in the original signed raw homology. -/
def singularClass (q : ℕ) : chains k q 0 →+
    (motivicRawBaseComplex k q).homology q :=
  (rawClass k q).hom.comp (topTermIso k q).inv.hom

private theorem sign_squared (q : ℕ) : (-1 : ℤ) ^ q * (-1 : ℤ) ^ q = 1 := by
  rw [← mul_pow]
  simp

/-- The original raw class vanishes exactly on genuine singular boundaries. -/
theorem singularClass_eq_zero_iff (q : ℕ) (x : chains k q 0) :
    singularClass k q x = 0 ↔ ∃ y : chains k q 1, boundary k q y = x := by
  rw [singularClass, AddMonoidHom.comp_apply, rawClass_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(-1 : ℤ) ^ q • (previousTermIso k q).hom y, ?_⟩
    have h := congrArg (topTermIso k q).hom hy
    rw [raw_d_top] at h
    change (topTermIso k q).hom
      ((-1 : ℤ) ^ q • (topTermIso k q).inv
        (boundary k q ((previousTermIso k q).hom y))) =
      (topTermIso k q).hom ((topTermIso k q).inv x) at h
    simpa only [map_zsmul, Iso.inv_hom_id_apply] using h
  · rintro ⟨y, rfl⟩
    refine ⟨(-1 : ℤ) ^ q • (previousTermIso k q).inv y, ?_⟩
    rw [raw_d_top]
    change (-1 : ℤ) ^ q • (topTermIso k q).inv
      (boundary k q ((previousTermIso k q).hom
        ((-1 : ℤ) ^ q • (previousTermIso k q).inv y))) = _
    simp only [map_zsmul, Iso.inv_hom_id_apply, ← mul_zsmul, sign_squared, one_zsmul]

/-- Every genuine singular boundary vanishes in the actual raw homology. -/
theorem singularClass_boundary (q : ℕ) (x : chains k q 1) :
    singularClass k q (boundary k q x) = 0 :=
  (singularClass_eq_zero_iff k q _).2 ⟨x, rfl⟩

/-- The original singular-class map is surjective. -/
theorem singularClass_surjective (q : ℕ) : Function.Surjective (singularClass k q) :=
  (rawClass_surjective k q).comp (ConcreteCategory.bijective_of_isIso (topTermIso k q).inv).2

/-- Its kernel is the actual image of the two-face singular boundary. -/
theorem singularClass_ker (q : ℕ) : (singularClass k q).ker = (boundary k q).range := by
  ext x
  exact singularClass_eq_zero_iff k q x

/-- Literal reduced torus `C₀ / im(d₁)` is canonically the original raw homology. -/
def quotientToRawEquiv (q : ℕ) : zeroHomology k q ≃+
    (motivicRawBaseComplex k q).homology q :=
  (QuotientAddGroup.quotientAddEquivOfEq (singularClass_ker k q).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (singularClass k q) (singularClass_surjective k q))

/-- The equivalence preserves each literal zero-cycle class. -/
theorem quotientToRawEquiv_mk (q : ℕ) (x : chains k q 0) :
    quotientToRawEquiv k q (QuotientAddGroup.mk x) = singularClass k q x := rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The literal quotient maps directly to the originally defined derived `H^{q,q}`. -/
def quotientToMotivicEquiv (q : ℕ) : zeroHomology k q ≃+
    motivicCohomology k q q (SmoothSite.base (Spec (.of k))) :=
  (quotientToRawEquiv k q).trans (motivicRawBaseEvaluationComparison k q q).symm

/-- The comparison sends a coset to the derived class of the same actual zero-cycle. -/
theorem quotientToMotivicEquiv_mk (q : ℕ) (x : chains k q 0) :
    motivicRawBaseEvaluationComparison k q q
      (quotientToMotivicEquiv k q (QuotientAddGroup.mk x)) = singularClass k q x := by
  exact (motivicRawBaseEvaluationComparison k q q).apply_symm_apply _

end Motivic.DiagonalTopDegree

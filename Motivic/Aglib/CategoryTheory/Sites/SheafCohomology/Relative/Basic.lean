/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.FreeSheafMonomorphisms
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Relative Ext for a monomorphism of site objects

The relative source of `j : U ⟶ X` is the actual cokernel of the map between
the existing section-representing free abelian sheaves. When `j` is mono,
their genuine short exact sequence gives the ordinary relative Ext sequence.
Its arrows from `Hⁿ(X,F)` to `Hⁿ(U,F)` are exactly the existing restrictions.

The six-term sequence uses precomposition with the extension class, as in
Mathlib's `Ext.contravariantSequence`. The signed connecting homomorphism
`Ext.δ` is also supplied, with its sign and exact lifting statements explicit.

For an open immersion this is a relative Ext construction for `(X,U)`.
No identification with closed-support cohomology, small-site cohomology or
purity is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w t v u

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
variable {U X : C} (j : U ⟶ X)

/-- The actual relative source is the sheaf cokernel of the free-section map. -/
def relativeSource : Sheaf J AddCommGrpCat.{max v t} :=
  cokernel ((Hypercohomology.freeAbelianSheafFunctor J).map j)

/-- The canonical quotient from the free sheaf on the larger site object. -/
abbrev relativeSourceπ : Hypercohomology.freeAbelianSheaf J X ⟶ relativeSource J j :=
  cokernel.π ((Hypercohomology.freeAbelianSheafFunctor J).map j)

/-- The genuine free-section presentation of the relative source. -/
def relativePresentation : ShortComplex (Sheaf J AddCommGrpCat.{max v t}) :=
  ShortComplex.cokernelSequence ((Hypercohomology.freeAbelianSheafFunctor J).map j)

/-- Actual Hom-injectivity, free abelian groups and sheafification make this short exact. -/
theorem relativePresentation_shortExact [Mono j] :
    (relativePresentation J j).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono ((Hypercohomology.freeAbelianSheafFunctor J).map j)
    infer_instance
  epi_g := by
    change Epi (cokernel.π ((Hypercohomology.freeAbelianSheafFunctor J).map j))
    infer_instance

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Relative cohomology here means the actual Ext group of the displayed relative source. -/
def relativeH (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) : AddCommGrpCat.{w} :=
  AddCommGrpCat.of (Ext (relativeSource J j) F n)

/-- Forget the relative condition by the actual quotient map of representing sheaves. -/
def relativeForget (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    relativeH J j F n ⟶ H J F n X :=
  AddCommGrpCat.ofHom ((Ext.mk₀ (relativeSourceπ J j)).precomp F (zero_add n))

/-- The relative-to-ordinary map is the actual Ext composition with the quotient. -/
theorem relativeForget_apply (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (x : relativeH J j F n) :
    relativeForget J j F n x = (Ext.mk₀ (relativeSourceπ J j)).comp x (zero_add n) := rfl

/-- The relative sequence starts injectively in degree zero. -/
theorem relativeForget_zero_mono (F : Sheaf J AddCommGrpCat.{max v t}) :
    Mono (relativeForget J j F 0) := by
  have : Epi (relativeSourceπ J j) := by
    change Epi (cokernel.π ((Hypercohomology.freeAbelianSheafFunctor J).map j))
    infer_instance
  exact Ext.mono_precomp_mk₀_of_epi F (relativeSourceπ J j)

variable [Mono j]

/-- The genuine extension class of the free-section presentation. -/
def relativeExtClass : Ext (relativeSource J j) (Hypercohomology.freeAbelianSheaf J U) 1 :=
  (relativePresentation_shortExact J j).extClass

/-- The unsigned connecting map used by Mathlib's contravariant Ext sequence. -/
def relativeConnecting (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    H J F n U ⟶ relativeH J j F (n + 1) :=
  AddCommGrpCat.ofHom ((relativeExtClass J j).precomp F (Nat.add_comm 1 n))

/-- The standard signed connecting map, using Mathlib's existing `Ext.δ` convention. -/
def relativeBoundary (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    H J F n U ⟶ relativeH J j F (n + 1) :=
  AddCommGrpCat.ofHom (Ext.δ (relativePresentation_shortExact J j) n (n + 1) rfl)

/-- The distinction between the two connecting conventions is precisely this sign. -/
theorem relativeBoundary_apply (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (x : H J F n U) :
    relativeBoundary J j F n x =
      Int.negOnePow (n + 1) • relativeConnecting J j F n x := rfl

/-- The actual six-term relative Ext sequence in two consecutive degrees. -/
def relativeSequence (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{w} 5 :=
  Ext.contravariantSequence (relativePresentation_shortExact J j) F n (n + 1)
    (Nat.add_comm 1 n)

/-- Both ordinary arrows are literally the original site restriction maps. -/
theorem relativeSequence_eq (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    relativeSequence J j F n =
      ComposableArrows.mk₅ (relativeForget J j F n)
        ((presheaf J F n).map j.op) (relativeConnecting J j F n)
        (relativeForget J j F (n + 1)) ((presheaf J F (n + 1)).map j.op) := rfl

/-- Exactness is the existing contravariant Ext exact-sequence theorem. -/
theorem relativeSequence_exact (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    (relativeSequence J j F n).Exact :=
  Ext.contravariantSequence_exact (relativePresentation_shortExact J j) F n (n + 1)
    (Nat.add_comm 1 n)

/-- Vanishing on the smaller site object is exactly the relative image condition. -/
theorem relative_lift_of_restriction_zero (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (x : H J F n X) (hx : (presheaf J F n).map j.op x = 0) :
    ∃ z : relativeH J j F n, relativeForget J j F n z = x :=
  Ext.contravariant_sequence_exact₂ (relativePresentation_shortExact J j) F x hx

/-- A class with zero signed boundary extends across the actual restriction map. -/
theorem restriction_lift_of_relativeBoundary_zero
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (x : H J F n U)
    (hx : relativeBoundary J j F n x = 0) :
    ∃ y : H J F n X, (presheaf J F n).map j.op y = x :=
  Ext.δ_exact₁ (relativePresentation_shortExact J j) F x rfl hx

/-- Relative classes vanishing ordinarily are in the image of the signed boundary. -/
theorem relativeBoundary_lift_of_forget_zero (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (z : relativeH J j F (n + 1)) (hz : relativeForget J j F (n + 1) z = 0) :
    ∃ x : H J F n U, relativeBoundary J j F n x = z :=
  Ext.δ_exact₃ (relativePresentation_shortExact J j) F z hz rfl

end CategoryTheory.Sheaf.LargeCohomology

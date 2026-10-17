/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.RelativeSheafCohomology

/-!
# Naturality of actual relative sheaf cohomology

A commuting square of site objects induces a map of the actual cokernels of
free abelian sheaves, and hence an actual restriction on relative Ext. Maps
of the corresponding short exact presentations give naturality of the
connecting maps. The standard signed boundary is natural in every degree,
both in the square of site objects and in the coefficient sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w t v u

namespace Motivic.SheafCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
variable {U X V Y : C} (j : U ⟶ X) (j' : V ⟶ Y)
  (a : U ⟶ V) (b : X ⟶ Y) (h : j ≫ b = a ≫ j')

/-- A square of site maps induces the actual map of the free-sheaf cokernels. -/
def relativeSourceMap : relativeSource J j ⟶ relativeSource J j' :=
  cokernel.map ((Hypercohomology.freeAbelianSheafFunctor J).map j)
    ((Hypercohomology.freeAbelianSheafFunctor J).map j')
    ((Hypercohomology.freeAbelianSheafFunctor J).map a)
    ((Hypercohomology.freeAbelianSheafFunctor J).map b)
    (by rw [← Functor.map_comp, ← Functor.map_comp, h])

/-- The relative source map commutes with the actual quotient maps. -/
@[reassoc (attr := simp)]
theorem relativeSourceπ_naturality :
    relativeSourceπ J j ≫ relativeSourceMap J j j' a b h =
      (Hypercohomology.freeAbelianSheafFunctor J).map b ≫ relativeSourceπ J j' :=
  cokernel.π_desc _ _ _

/-- The induced map between the genuine three-term free-sheaf presentations. -/
def relativePresentationMap : relativePresentation J j ⟶ relativePresentation J j' where
  τ₁ := (Hypercohomology.freeAbelianSheafFunctor J).map a
  τ₂ := (Hypercohomology.freeAbelianSheafFunctor J).map b
  τ₃ := relativeSourceMap J j j' a b h
  comm₁₂ := by
    change (Hypercohomology.freeAbelianSheafFunctor J).map a ≫
        (Hypercohomology.freeAbelianSheafFunctor J).map j' =
      (Hypercohomology.freeAbelianSheafFunctor J).map j ≫
        (Hypercohomology.freeAbelianSheafFunctor J).map b
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  comm₂₃ := (relativeSourceπ_naturality J j j' a b h).symm

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Relative restriction is Ext precomposition with the actual cokernel map. -/
def relativeRestriction (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    relativeH J j' F n ⟶ relativeH J j F n :=
  AddCommGrpCat.ofHom ((Ext.mk₀ (relativeSourceMap J j j' a b h)).precomp F (zero_add n))

/-- Relative restriction acts by genuine Ext composition. -/
theorem relativeRestriction_apply (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ)
    (x : relativeH J j' F n) :
    relativeRestriction J j j' a b h F n x =
      (Ext.mk₀ (relativeSourceMap J j j' a b h)).comp x (zero_add n) := rfl

/-- Naturality of the extension classes is induced by the actual presentation map. -/
theorem relativeExtClass_naturality [Mono j] [Mono j'] :
    (relativeExtClass J j).comp
        (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map a)) (add_zero 1) =
      (Ext.mk₀ (relativeSourceMap J j j' a b h)).comp (relativeExtClass J j') (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality
    (relativePresentation_shortExact J j) (relativePresentation_shortExact J j')
    (relativePresentationMap J j j' a b h)

/-- Unsigned connecting maps commute with actual restrictions. -/
theorem relativeConnecting_restriction [Mono j] [Mono j']
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (x : H J F n V) :
    relativeRestriction J j j' a b h F (n + 1) (relativeConnecting J j' F n x) =
      relativeConnecting J j F n ((presheaf J F n).map a.op x) := by
  change Ext (Hypercohomology.freeAbelianSheaf J V) F n at x
  change (Ext.mk₀ (relativeSourceMap J j j' a b h)).comp
      ((relativeExtClass J j').comp x (Nat.add_comm 1 n)) (zero_add (n + 1)) =
    (relativeExtClass J j).comp
      ((Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map a)).comp x (zero_add n))
      (Nat.add_comm 1 n)
  rw [← Ext.comp_assoc _ _ _ (zero_add 1) (Nat.add_comm 1 n) (by omega),
    ← relativeExtClass_naturality J j j' a b h,
    Ext.comp_assoc_of_second_deg_zero]

/-- The standard signed boundary is natural in the square, in every degree. -/
theorem relativeBoundary_restriction [Mono j] [Mono j']
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (x : H J F n V) :
    relativeRestriction J j j' a b h F (n + 1) (relativeBoundary J j' F n x) =
      relativeBoundary J j F n ((presheaf J F n).map a.op x) := by
  simp only [relativeBoundary_apply, Units.smul_def, map_zsmul]
  rw [relativeConnecting_restriction]

variable {F G : Sheaf J AddCommGrpCat.{max v t}}

/-- Changing coefficients is actual Ext postcomposition with the coefficient map. -/
def relativeCoefficientMap (η : F ⟶ G) (n : ℕ) :
    relativeH J j F n ⟶ relativeH J j G n :=
  AddCommGrpCat.ofHom ((Ext.mk₀ η).postcomp (relativeSource J j) (add_zero n))

/-- The coefficient map acts by genuine Ext composition. -/
theorem relativeCoefficientMap_apply (η : F ⟶ G) (n : ℕ) (x : relativeH J j F n) :
    relativeCoefficientMap J j η n x = x.comp (Ext.mk₀ η) (add_zero n) := rfl

/-- Unsigned connecting maps commute with the existing ordinary coefficient map. -/
theorem relativeConnecting_coefficient [Mono j] (η : F ⟶ G) (n : ℕ) (x : H J F n U) :
    relativeCoefficientMap J j η (n + 1) (relativeConnecting J j F n x) =
      relativeConnecting J j G n (((presheafFunctor J n).map η).app (op U) x) := by
  change ((relativeExtClass J j).comp x (Nat.add_comm 1 n)).comp
      (Ext.mk₀ η) (add_zero (n + 1)) =
    (relativeExtClass J j).comp (x.comp (Ext.mk₀ η) (add_zero n)) (Nat.add_comm 1 n)
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ _

/-- The standard signed boundary is natural in the coefficients, in every degree. -/
theorem relativeBoundary_coefficient [Mono j] (η : F ⟶ G) (n : ℕ) (x : H J F n U) :
    relativeCoefficientMap J j η (n + 1) (relativeBoundary J j F n x) =
      relativeBoundary J j G n (((presheafFunctor J n).map η).app (op U) x) := by
  simp only [relativeBoundary_apply, Units.smul_def, map_zsmul]
  rw [relativeConnecting_coefficient]

end Motivic.SheafCohomology

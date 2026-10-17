/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FlatPolynomialComponentRegularity
public import Motivic.AlgebraicGeometry.Graph.Transversality
public import Motivic.Aglib.Algebra.Homology.KoszulTorRegularBlockReduction

/-!
# Removing the actual smooth graph block before an endpoint equation

The graph of a map into a smooth separated scheme has an actual regular stalk
kernel. Its actual stalk quotient sends the parameter pulled from the first
factor to the original parameter, so regular-block elimination leaves precisely
the singleton `t - a`. The source of the graph need not be flat over its target.
For a reduced component of a whole flat polynomial family, the surviving scalar
is regular by dominance, without component flatness over a relative base.

This is a local graph-block comparison. It does not yet identify the four-factor
correspondence Tor modules or prove the relative-base endpoint correspondence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence
open scoped Polynomial

universe u

namespace AlgebraicGeometry.FiniteFlatCurve

/-- The endpoint scalar is transported through the literal composite stalk map. -/
theorem scalar_comp {k : Type u} [Field k] {C P : Scheme.{u}}
    (j : C ⟶ P) (f : P ⟶ Spec (.of k[X])) (a : k) (x : C) :
    scalar (j ≫ f) a x = j.stalkMap x (scalar f a (j x)) := by
  simp only [scalar, Scheme.Hom.stalkMap_comp, CommRingCat.comp_apply]
  rfl

end AlgebraicGeometry.FiniteFlatCurve

namespace Motivic.Graph

variable {k : Type u} [Field k] {C X : Scheme.{u}}
  (h : C ⟶ X) (b : X ⟶ Spec (.of k))
  (f : C ⟶ Spec (.of (Polynomial k)))

/-- The parameter on the actual graph ambient is pulled from its source factor. -/
abbrev polynomialParameter : pullback (h ≫ b) b ⟶ Spec (.of (Polynomial k)) :=
  pullback.fst (h ≫ b) b ≫ f

/-- The actual graph-stalk surjection sends the retained endpoint equation to
exactly the original scalar, with its original scheme structure map. -/
theorem polynomialScalar_graph (a : k) (x : C) :
    (correspondenceGraph h b).stalkMap x
        (FiniteFlatCurve.scalar (polynomialParameter h b f) a (correspondenceGraph h b x)) =
      FiniteFlatCurve.scalar f a x := by
  rw [← FiniteFlatCurve.scalar_comp]
  simp only [polynomialParameter, correspondenceGraph_fst_assoc]

/-- A chosen actual graph kernel block is removed in every homological degree.
The remaining equation is identified with the original parameter, not an
unspecified scalar or an abstract isomorphic quotient. -/
theorem polynomialBlock_length [IsSeparated b]
    (a : k) (x : C)
    (t : List ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x)))
    (ht : IsWeaklyRegular
      ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x)) t)
    (hker : RingHom.ker ((correspondenceGraph h b).stalkMap x).hom = Ideal.ofList t)
    (n : ℕ) :
    Module.length ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x))
      ((Koszul.coefficientComplex
        (ModuleCat.of
          ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x))
          ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x)))
        (t ++ [FiniteFlatCurve.scalar (polynomialParameter h b f) a
          (correspondenceGraph h b x)])).homology n) =
      Module.length (C.presheaf.stalk x)
        ((Koszul.coefficientComplex (ModuleCat.of (C.presheaf.stalk x) (C.presheaf.stalk x))
          [FiniteFlatCurve.scalar f a x]).homology n) := by
  have he := Koszul.regularBlockHomology_length
    ((correspondenceGraph h b).stalkMap x).hom
    ((correspondenceGraph h b).stalkMap_surjective x) t
    [FiniteFlatCurve.scalar (polynomialParameter h b f) a (correspondenceGraph h b x)]
    hker ht n
  have hs : ((correspondenceGraph h b).stalkMap x).hom
      (FiniteFlatCurve.scalar (polynomialParameter h b f) a (correspondenceGraph h b x)) =
        FiniteFlatCurve.scalar f a x := polynomialScalar_graph h b f a x
  rw [List.map_singleton, hs] at he
  exact he

/-- Smoothness supplies the genuine graph kernel block, valid for arbitrary
sources, and the complete comparison keeps its literal appended singleton. -/
theorem exists_polynomialBlock [Smooth b] [IsSeparated b] (a : k) (x : C) :
    ∃ t : List ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x)),
      IsRegular ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x)) t ∧
      RingHom.ker ((correspondenceGraph h b).stalkMap x).hom = Ideal.ofList t ∧
      ∀ n : ℕ,
        Module.length ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x))
          ((Koszul.coefficientComplex
            (ModuleCat.of
              ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x))
              ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b x)))
            (t ++ [FiniteFlatCurve.scalar (polynomialParameter h b f) a
              (correspondenceGraph h b x)])).homology n) =
          Module.length (C.presheaf.stalk x)
            ((Koszul.coefficientComplex
              (ModuleCat.of (C.presheaf.stalk x) (C.presheaf.stalk x))
              [FiniteFlatCurve.scalar f a x]).homology n) := by
  obtain ⟨t, ht, hker⟩ := exists_regular_kernel_of_smooth h b x
  exact ⟨t, ht, hker, polynomialBlock_length h b f a x t ht.toIsWeaklyRegular hker⟩

end Motivic.Graph

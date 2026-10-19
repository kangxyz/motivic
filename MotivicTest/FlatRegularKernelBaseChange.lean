/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.FlatBaseChange
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of flat transport of actual regular kernel equations

These consumers exercise literal image lists in arbitrary flat Cartesian
squares and ring squares, including equality with the full base-changed
kernel. Smooth triple products exercise the actual correspondence ambient
construction. The nonreduced coefficient example checks that no reducedness
or domain hypothesis was added to flat transport.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.MotivicTest.FlatRegularKernelBaseChange
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

/-- An actual Cartesian square transports equations into its literal source-stalk kernel. -/
theorem actualCartesianImages {W D Q P : Scheme.{u}}
    {a : W ⟶ D} {b : W ⟶ Q} {i : D ⟶ P} {q : Q ⟶ P} [Flat q]
    (sq : IsPullback a b i q) (z : W)
    (rs : List (P.presheaf.stalk (i (a z))))
    (hrs : IsRegular (P.presheaf.stalk (i (a z))) rs)
    (hker : RingHom.ker (i.stalkMap (a z)).hom = Ideal.ofList rs) :
    IsRegular (Q.presheaf.stalk (b z)) (rs.map (Diagonal.baseChangeStalkMap sq z).hom) ∧
      Ideal.ofList (rs.map (Diagonal.baseChangeStalkMap sq z).hom) ≤
        RingHom.ker (b.stalkMap z).hom := by
  have hk : Ideal.ofList rs ≤ RingHom.ker (i.stalkMap (a z)).hom := hker.ge
  exact ⟨Diagonal.mapped_equations_isRegular sq z hrs.toIsWeaklyRegular hk,
    Diagonal.mapped_equations_le_kernel sq z hk⟩

/-- Flat transport works over a nonreduced ring and still uses the actual ring maps. -/
theorem nonreducedBase (rs : List (ZMod 4)) (hrs : IsWeaklyRegular (ZMod 4) rs) :
    IsWeaklyRegular (ZMod 4) (rs.map (RingHom.id (ZMod 4))) :=
  isWeaklyRegular_map_of_flat _ (RingHom.Flat.id _) hrs

/-- The literal image list generates the full actual Cartesian stalk kernel. -/
theorem actualCartesianKernel {W D Q P : Scheme.{u}}
    {a : W ⟶ D} {b : W ⟶ Q} {i : D ⟶ P} {q : Q ⟶ P}
    [IsClosedImmersion i] [Flat q] (sq : IsPullback a b i q) (z : W)
    (rs : List (P.presheaf.stalk (i (a z))))
    (hrs : IsRegular (P.presheaf.stalk (i (a z))) rs)
    (hker : RingHom.ker (i.stalkMap (a z)).hom = Ideal.ofList rs) :
    IsRegular (Q.presheaf.stalk (b z)) (rs.map (Diagonal.baseChangeStalkMap sq z).hom) ∧
      RingHom.ker (b.stalkMap z).hom =
        Ideal.ofList (rs.map (Diagonal.baseChangeStalkMap sq z).hom) :=
  Diagonal.mapped_equations_regular_kernel sq z hrs hker

/-- Smooth structure maps give actual triple-inclusion regular kernels over an arbitrary base. -/
theorem smoothTripleKernel {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [Smooth f] [Smooth g] [IsSeparated g] [Smooth h] (x : correspondenceTripleProduct f g h) :
    ∃ rs : List ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceTripleInclusion f g h x)),
      IsRegular ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceTripleInclusion f g h x)) rs ∧
          RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap x).hom = Ideal.ofList rs :=
  exists_regular_kernel_correspondenceTripleInclusion f g h x

/-- The full geometric kernel statement also applies over the nonreduced scheme `Spec (ZMod 4)`. -/
theorem nonreducedTripleKernel :
    let S := Spec (CommRingCat.of (ZMod 4))
    ∀ x : correspondenceTripleProduct (𝟙 S) (𝟙 S) (𝟙 S),
      ∃ rs : List ((correspondenceIntersectionAmbient (𝟙 S) (𝟙 S) (𝟙 S)).presheaf.stalk
        (correspondenceTripleInclusion (𝟙 S) (𝟙 S) (𝟙 S) x)),
        IsRegular ((correspondenceIntersectionAmbient (𝟙 S) (𝟙 S) (𝟙 S)).presheaf.stalk
          (correspondenceTripleInclusion (𝟙 S) (𝟙 S) (𝟙 S) x)) rs ∧
            RingHom.ker ((correspondenceTripleInclusion (𝟙 S) (𝟙 S) (𝟙 S)).stalkMap x).hom =
              Ideal.ofList rs := by
  intro S x
  exact exists_regular_kernel_correspondenceTripleInclusion (𝟙 S) (𝟙 S) (𝟙 S) x

end Motivic.MotivicTest.FlatRegularKernelBaseChange

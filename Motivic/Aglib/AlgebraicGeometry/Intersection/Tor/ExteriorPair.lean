/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.Aglib.AlgebraicGeometry.Intersection.PointedStalkTor
public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.TripleIdeals
public import Motivic.Aglib.Algebra.Homology.Koszul.FlatLocalMultiplicity
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.FlatBaseChange

/-!
# Stalk transport for exterior pairs
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.Products.StalkTransport
open _root_.AlgebraicGeometry.Scheme.StalkTransport

/-- A pointed actual stalk map retains the flatness of its scheme morphism. -/
theorem _root_.AlgebraicGeometry.Scheme.StalkTransport.pointedMap_flat {X Y : Scheme.{u}} (f : X ⟶
    Y) [Flat f]
    (x : X) (y : Y) (h : y = f x) : (pointedMap f x y h).hom.Flat := by
  subst y
  simpa only [pointedMap_image] using Flat.stalkMap f x

/-- Equal-point transport preserves the local nature of an actual stalk map. -/
instance _root_.AlgebraicGeometry.Scheme.StalkTransport.pointedMap_isLocalHom {X Y : Scheme.{u}} (f
    : X ⟶ Y)
    (x : X) (y : Y) (h : y = f x) : IsLocalHom (pointedMap f x y h).hom := by
  subst y
  rw [pointedMap_image]
  infer_instance

end AlgebraicGeometry.Scheme.Products.StalkTransport

namespace AlgebraicGeometry.Scheme.Intersection

open _root_.AlgebraicGeometry.Scheme.StalkTransport

variable {D T P D' T' P' : Scheme.{u}}
  (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)
  (i' : D' ⟶ P') (d' : D') (j' : T' ⟶ P') (t' : T') (hp' : i' d' = j' t')
  (uD : D' ⟶ D) (uT : T' ⟶ T) (uP : P' ⟶ P)
  (sq : IsPullback uD i' i uP) (hj : uT ≫ j = j' ≫ uP)
  (hd : d = uD d') (ht : t = uT t')
  [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion j]
  [IsClosedImmersion j'] [Flat uP] [Flat uT]

omit [IsClosedImmersion i'] in
/-- The very same original diagonal list remains regular and generates the
actual exterior diagonal kernel after its literal pointed stalk map. -/
theorem exteriorPairList_regular_kernel (s : List (ambientStalk i d))
    (hs : IsRegular (ambientStalk i d) s)
    (hker : RingHom.ker (i.stalkMap d).hom = Ideal.ofList s) :
    let g := pointedMap uP (i' d') (i d)
      (neighborhoodAmbientPoint i d i' d' uD uP sq.w hd)
    IsRegular (ambientStalk i' d') (s.map g.hom) ∧
      RingHom.ker (i'.stalkMap d').hom = Ideal.ofList (s.map g.hom) := by
  subst d
  exact Diagonal.mapped_equations_regular_kernel sq d' hs hker

omit [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion j]
  [IsClosedImmersion j'] [Flat uP] [Flat uT] in
include hj in
/-- The original scheme square proves equality of the literal coefficient
lists after both actual stalk routes. -/
theorem exteriorPairList_coefficient_square (s : List (ambientStalk i d)) :
    (s.map (pointedMap uP (i' d') (i d)
      (neighborhoodAmbientPoint i d i' d' uD uP sq.w hd)).hom).map
        (coefficientStalkMap i' d' j' t' hp').hom =
      (s.map (coefficientStalkMap i d j t hp).hom).map
        (pointedMap uT t' t ht).hom := by
  simp only [List.map_map]
  congr 1
  funext r
  exact (ConcreteCategory.congr_hom
    (neighborhoodCoefficientStalkMap_square i d j t hp i' d' j' t' hp'
      uD uT uP sq.w hj hd ht) r).symm

include sq hj hd in
/-- Flat exterior coefficient projection compares every actual Tor degree.
The source diagonal uses the transported original pair list throughout. -/
theorem exteriorPairStalkTor_length
    (hregular : ∃ s : List (ambientStalk i d),
      IsRegular (ambientStalk i d) s ∧
        RingHom.ker (i.stalkMap d).hom = Ideal.ofList s) (n : ℕ) :
    Module.length (ambientStalk i' d')
        ((((Tor (ModuleCat (ambientStalk i' d')) n).obj
          (coefficientStalkModule i' d' j' t' hp')).obj (sourceStalkModule i' d'))) =
      Module.length (ambientStalk i d)
        ((((Tor (ModuleCat (ambientStalk i d)) n).obj
          (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d))) *
        Module.length (T'.presheaf.stalk t')
          (_root_.ChainComplex.Koszul.coefficientClosedFiber (pointedMap uT t' t ht).hom) := by
  obtain ⟨s, hs, hker⟩ := hregular
  let g := pointedMap uP (i' d') (i d)
    (neighborhoodAmbientPoint i d i' d' uD uP sq.w hd)
  obtain ⟨hs', hker'⟩ := exteriorPairList_regular_kernel i d i' d' uD uP sq hd s hs hker
  rw [(torIsoHomology i' d' j' t' hp' (s.map g.hom) hker' hs' n).toLinearEquiv.length_eq,
    (torIsoHomology i d j t hp s hker hs n).toLinearEquiv.length_eq]
  exact _root_.ChainComplex.Koszul.coordinateFlatLocalHomology_length
    (coefficientStalkMap i d j t hp).hom (coefficientStalkMap_surjective i d j t hp)
    (coefficientStalkMap i' d' j' t' hp').hom (coefficientStalkMap_surjective i' d' j' t' hp')
    (pointedMap uT t' t ht).hom (pointedMap_flat uT t' t ht)
    s (s.map g.hom)
    (exteriorPairList_coefficient_square i d j t hp i' d' j' t' hp'
      uD uT uP sq hj hd ht s) n

/-- A genuine Cartesian closed-immersion square identifies the two local
closed fibers by the actual support quotient and its exact stalk kernel. -/
theorem exteriorClosedFiber_length {V D P Q : Scheme.{u}}
    (a : V ⟶ D) (b : V ⟶ Q) (i : D ⟶ P) (q : Q ⟶ P)
    [IsClosedImmersion i] (sq : IsPullback a b i q) (w : V) :
    Module.length (Q.presheaf.stalk (b w))
        (_root_.ChainComplex.Koszul.coefficientClosedFiber (Diagonal.baseChangeStalkMap sq w).hom) =
      Module.length (V.presheaf.stalk w)
        (_root_.ChainComplex.Koszul.coefficientClosedFiber (a.stalkMap w).hom) := by
  have : IsClosedImmersion b := MorphismProperty.of_isPullback sq inferInstance
  exact Module.closedFiberQuotient_length
    (i.stalkMap (a w)).hom (i.stalkMap_surjective (a w))
    (b.stalkMap w).hom (b.stalkMap_surjective w)
    (Diagonal.baseChangeStalkMap sq w).hom (a.stalkMap w).hom
    (congrArg CommRingCat.Hom.hom (Diagonal.baseChangeStalkMap_comp sq w)).symm
    (Diagonal.baseChange_stalk_kernel sq w)

end AlgebraicGeometry.Scheme.Intersection

namespace AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- Projection of the actual exterior diagonal to the original pair is Cartesian. -/
theorem correspondenceFirstDiagonal_pair_isPullback :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h))
      (correspondenceFirstDiagonalInclusion f g h i)
      (correspondenceTripleInclusion f g h)
      (pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) := by
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback
      (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) ?_
    (correspondenceFirstDiagonalInclusion_fst f g h i).symm
  simpa [correspondenceTripleTarget, correspondenceAmbientTarget] using
    (IsPullback.of_hasPullback
      (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h))


end AlgebraicGeometry.Scheme.Products

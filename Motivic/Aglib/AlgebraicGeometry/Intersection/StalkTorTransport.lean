/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.CoefficientStalkTransport
public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedSpecTor

/-!
# Actual intersection Tor under open-neighborhood transport

A commuting diagram of open immersions identifies the ambient, source, and
coefficient stalks by their actual pointed stalk maps. The two scalar squares
are proved from scheme-map composition, including every point equality.
These constructed scalar-compatible module isomorphisms transport actual
categorical Tor in all degrees. The coefficient remains the first argument.
Scheme isomorphisms are a special case, and the comparison can be composed
with the closed affine coordinate-to-stalk comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.StalkTransport

variable {X Y Z W : Scheme.{u}}

/-- At its actual image point, the pointed stalk map is the literal stalk map. -/
@[simp]
theorem pointedMap_image (f : X ⟶ Y) (x : X) :
    pointedMap f x (f x) rfl = f.stalkMap x := by
  change Y.presheaf.stalkSpecializes (specializes_refl (f x)) ≫ f.stalkMap x = _
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/-- A commuting scheme square yields a commuting square of actual pointed
stalk maps, with separately specified equalities for all four points. -/
theorem pointedMap_square (f : X ⟶ Y) (g : Y ⟶ W) (f' : X ⟶ Z) (g' : Z ⟶ W)
    (h : f ≫ g = f' ≫ g') (x : X) (y : Y) (z : Z) (w : W)
    (hy : y = f x) (hz : z = f' x) (hwy : w = g y) (hwz : w = g' z) :
    pointedMap g y w hwy ≫ pointedMap f x y hy =
      pointedMap g' z w hwz ≫ pointedMap f' x z hz := by
  rw [pointedMap_comp, pointedMap_comp]
  exact pointedMap_congr _ _ h _ _ _ _

/- The actual pointed stalk map of an open immersion is an isomorphism. -/

/-- The ring equivalence induced by the literal pointed stalk map of an open immersion. -/
def pointedStalkEquiv (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (y : Y) (h : y = f x) :
    Y.presheaf.stalk y ≃+* X.presheaf.stalk x :=
  (asIso (pointedMap f x y h)).commRingCatIsoToRingEquiv

/-- The constructed ring equivalence has the literal pointed stalk map as its forward map. -/
@[simp]
theorem pointedStalkEquiv_apply (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (y : Y) (h : y = f x) (r : Y.presheaf.stalk y) :
    pointedStalkEquiv f x y h r = pointedMap f x y h r := rfl

end AlgebraicGeometry.Scheme.StalkTransport

namespace AlgebraicGeometry.Scheme.Intersection

open _root_.AlgebraicGeometry.Scheme.StalkTransport

variable {D T P D' T' P' : Scheme.{u}}
  (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)
  (i' : D' ⟶ P') (d' : D') (j' : T' ⟶ P') (t' : T') (hp' : i' d' = j' t')
  (uD : D' ⟶ D) (uT : T' ⟶ T) (uP : P' ⟶ P)
  (hi : uD ≫ i = i' ≫ uP) (hj : uT ≫ j = j' ≫ uP)
  (hd : d = uD d') (ht : t = uT t')

include hi hd in
/-- The source square and point equality identify the two ambient image points. -/
theorem neighborhoodAmbientPoint : i d = uP (i' d') := by
  rw [hd]
  exact congrArg (fun f : D' ⟶ P ↦ f d') hi

/-- The actual source scalar maps commute with the pointed neighborhood maps. -/
theorem neighborhoodSourceStalkMap_square :
    i.stalkMap d ≫ pointedMap uD d' d hd =
      pointedMap uP (i' d') (i d) (neighborhoodAmbientPoint i d i' d' uD uP hi hd) ≫
        i'.stalkMap d' := by
  simpa only [pointedMap_image] using
    pointedMap_square uD i i' uP hi d' d (i' d') (i d) hd rfl rfl
      (neighborhoodAmbientPoint i d i' d' uD uP hi hd)

include hj in
/-- The coefficient square keeps both common-ambient-point transports. -/
theorem neighborhoodCoefficientStalkMap_square :
    coefficientStalkMap i d j t hp ≫ pointedMap uT t' t ht =
      pointedMap uP (i' d') (i d) (neighborhoodAmbientPoint i d i' d' uD uP hi hd) ≫
        coefficientStalkMap i' d' j' t' hp' :=
  pointedMap_square uT j j' uP hj t' t (i' d') (i d) ht hp' hp
    (neighborhoodAmbientPoint i d i' d' uD uP hi hd)

variable [IsOpenImmersion uD] [IsOpenImmersion uT] [IsOpenImmersion uP]

/-- The actual ambient stalk ring equivalence induced by the open neighborhood. -/
def neighborhoodAmbientStalkEquiv : ambientStalk i d ≃+* ambientStalk i' d' :=
  pointedStalkEquiv uP (i' d') (i d) (neighborhoodAmbientPoint i d i' d' uD uP hi hd)

/-- The actual source stalk module comparison has the literal pointed stalk map
and the scalar compatibility proved by the source scheme square. -/
def neighborhoodSourceStalkModuleIso :
    sourceStalkModule i d ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd).toRingHom).obj
          (sourceStalkModule i' d') := by
  apply _root_.ModuleCat.TorComparison.ringModuleIso
    (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd)
    (pointedStalkEquiv uD d' d hd) (i.stalkMap d).hom (i'.stalkMap d').hom
  intro r
  exact ConcreteCategory.congr_hom
    (neighborhoodSourceStalkMap_square i d i' d' uD uP hi hd) r

/-- The actual coefficient module comparison uses the same ambient ring
equivalence and preserves the specified common-point scalar action. -/
def neighborhoodCoefficientStalkModuleIso :
    coefficientStalkModule i d j t hp ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd).toRingHom).obj
          (coefficientStalkModule i' d' j' t' hp') := by
  apply _root_.ModuleCat.TorComparison.ringModuleIso
    (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd)
    (pointedStalkEquiv uT t' t ht) (coefficientStalkMap i d j t hp).hom
    (coefficientStalkMap i' d' j' t' hp').hom
  intro r
  exact ConcreteCategory.congr_hom
    (neighborhoodCoefficientStalkMap_square i d j t hp i' d' j' t' hp'
      uD uT uP hi hj hd ht) r

/-- The source module comparison is the actual pointed neighborhood stalk map. -/
theorem neighborhoodSourceStalkModuleIso_hom_apply (x : D.presheaf.stalk d) :
    (neighborhoodSourceStalkModuleIso i d i' d' uD uP hi hd).hom x =
      pointedMap uD d' d hd x := rfl

omit [IsOpenImmersion uD] in
/-- The coefficient module comparison is the actual pointed neighborhood stalk map. -/
theorem neighborhoodCoefficientStalkModuleIso_hom_apply (x : T.presheaf.stalk t) :
    (neighborhoodCoefficientStalkModuleIso i d j t hp i' d' j' t' hp'
      uD uT uP hi hj hd ht).hom x = pointedMap uT t' t ht x := rfl

/-- Actual intersection Tor is invariant under commuting open-neighborhood
maps. Every scalar and module comparison is constructed from actual stalk maps. -/
def neighborhoodStalkTorIso (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk i d)) n).obj
      (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d) ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd).toRingHom).obj
          (((Tor (ModuleCat (ambientStalk i' d')) n).obj
            (coefficientStalkModule i' d' j' t' hp')).obj (sourceStalkModule i' d')) :=
  _root_.ModuleCat.TorComparison.torIsoOfScalarIso
    (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd) _ _ _ _
    (neighborhoodCoefficientStalkModuleIso i d j t hp i' d' j' t' hp'
      uD uT uP hi hj hd ht)
    (neighborhoodSourceStalkModuleIso i d i' d' uD uP hi hd) n

section ClosedAffineCharts

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- Actual intersection Tor on commuting affine open charts is the localized
coordinate Tor of two surjective coordinate maps. Both ambient scalar
restrictions are the constructed actual stalk equivalences. -/
def closedChartStalkTorIso (f : R →+* A) (hf : Function.Surjective f)
    (p : PrimeSpectrum A) (g : R →+* B) (hg : Function.Surjective g)
    (q : PrimeSpectrum B) (hpq : p.comap f = q.comap g)
    (vD : Spec (.of A) ⟶ D) (vT : Spec (.of B) ⟶ T) (vP : Spec (.of R) ⟶ P)
    [IsOpenImmersion vD] [IsOpenImmersion vT] [IsOpenImmersion vP]
    (hD : vD ≫ i = Spec.map (CommRingCat.ofHom f) ≫ vP)
    (hT : vT ≫ j = Spec.map (CommRingCat.ofHom g) ≫ vP)
    (hpd : d = vD p) (hqt : t = vT q) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk i d)) n).obj
      (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d) ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d (Spec.map (CommRingCat.ofHom f)) p
          vD vP hD hpd).toRingHom).obj
        ((ModuleCat.restrictScalars (specAmbientStalkEquiv f p).toRingHom).obj
          (ModuleCat.of (Localization.AtPrime (p.comap f).asIdeal)
            (LocalizedModule (p.comap f).asIdeal.primeCompl
              (((Tor (ModuleCat R) n).obj (specCoordinateModule g)).obj
                (specCoordinateModule f))))) :=
  neighborhoodStalkTorIso i d j t hp (Spec.map (CommRingCat.ofHom f)) p
    (Spec.map (CommRingCat.ofHom g)) q hpq vD vT vP hD hT hpd hqt n ≪≫
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d (Spec.map (CommRingCat.ofHom f)) p
          vD vP hD hpd).toRingHom).mapIso (closedSpecStalkTorIso f hf p g hg q hpq n)

end ClosedAffineCharts

end AlgebraicGeometry.Scheme.Intersection

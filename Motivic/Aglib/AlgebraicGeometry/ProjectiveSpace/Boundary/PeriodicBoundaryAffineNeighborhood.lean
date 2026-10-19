/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.PeriodicBoundaryTwists
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.GlobalSectionMaps
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.TwistSectionBoundaryUnitOpen

/-!
# An affine neighborhood from one positive boundary twist frame

Serre lifting is applied at a sufficiently large multiple of the given period.
The prescribed value comes from tensor powers of the same frame. The resulting
positive-twist unit open contains the entire closed boundary on the unchanged base.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.PeriodicBoundaryAffineNeighborhood`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.FiniteSourceBoundaryAffineNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.QuasiCoherent
open Scheme.CoherentGraph

universe u
namespace AlgebraicGeometry.ProjectiveSpace

/-- A single positive-period boundary frame produces an actual positive twist section
and an affine open containing the entire boundary, without changing the parameter. -/
theorem exists_affine_unitOpen_of_periodic_boundary_frame
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {Z : Scheme.{u}} (z : Z ⟶ ProjectiveSpace R ι) [IsClosedImmersion z]
    (d0 : ℕ) (hd0 : 0 < d0)
    (ed : (Modules.pullback z).obj (twistingSheaf R ι (d0 : ℤ)) ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    ∃ k : ℕ, 0 < k ∧ ∃ s : Γ(twistingSheaf R ι ((d0 * k : ℕ) : ℤ), ⊤),
      IsIso (pullbackSectionMap z ((unitHomGlobalSectionsEquiv _
        (twistingLineBundle R ι ((d0 * k : ℕ) : ℤ)).val).symm s)) ∧
      IsAffineOpen (twistSectionUnitOpen R ι (d0 * k) s) ∧
      Set.range z ⊆ twistSectionUnitOpen R ι (d0 * k) s := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let X := ProjectiveSpace R ι
  let O := SheafOfModules.unit X.ringCatSheaf
  have hO : affineLocallyFiniteType X O := by
    let eO : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ O := coproductUniqueIso _
    let := finiteLocallyFree_of_iso eO
    exact coherent_of_finiteLocallyFree _
  obtain ⟨B, hB⟩ := finiteMap_exists_global_section_map R ι n e (𝟙 X) z O hO
  let k := B + 1
  let d := d0 * k
  have hdB : B ≤ d := (Nat.le_succ B).trans (Nat.le_mul_of_pos_left k hd0)
  have hd : 0 < d := Nat.mul_pos hd0 (Nat.succ_pos B)
  let T := twistingSheaf R ι (d : ℤ)
  let L := (Modules.pullback (𝟙 X)).obj T
  let eL : L ≅ T := (Modules.pullbackId X).app T
  let eP : (Modules.pullback z).obj T ≅ SheafOfModules.unit Z.ringCatSheaf := by
    simpa only [T, d, Nat.cast_mul] using periodicTwistUnitIso R ι z (d0 : ℤ) ed k
  let eZ : (Modules.pullback z).obj L ≅ SheafOfModules.unit Z.ringCatSheaf :=
    (Modules.pullback z).mapIso eL ≪≫ eP
  let eQ : (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
      ((Modules.pullback z).obj O) ≅ SheafOfModules.unit Z.ringCatSheaf :=
    tensorSheafIso Z eZ (pullbackUnitIso z) ≪≫ tensorSheafLeftUnit Z _
  obtain ⟨b, hb⟩ := hB d hdB eQ.inv
  let E := pullbackLineBundle (𝟙 X) (twistingLineBundle R ι (d : ℤ))
  have hbI := isIso_pullbackSection_of_tensor_eq z E O b eQ.inv hb
  let σ : O ⟶ T := b ≫ (tensorSheafRightUnit X L).hom ≫ eL.hom
  have hσ : IsIso (pullbackSectionMap z σ) := by
    change IsIso ((pullbackUnitIso z).inv ≫ (Modules.pullback z).map
      (b ≫ (tensorSheafRightUnit X L).hom ≫ eL.hom))
    rw [Functor.map_comp, ← Category.assoc]
    infer_instance
  let s : Γ(T, ⊤) := unitHomGlobalSectionsEquiv X T σ
  have hs : IsIso (pullbackSectionMap z ((unitHomGlobalSectionsEquiv _
      (twistingLineBundle R ι (d : ℤ)).val).symm s)) := by
    change IsIso (pullbackSectionMap z ((unitHomGlobalSectionsEquiv X T).symm s))
    simpa only [s, Equiv.symm_apply_apply] using hσ
  refine ⟨k, Nat.succ_pos B, s, hs, ?_, ?_⟩
  · exact isAffineOpen_twistSectionUnitOpen R ι (e.symm 0) d hd s
  · exact range_subset_twistSectionUnitOpen_of_pullback_isIso R ι d z s

end AlgebraicGeometry.ProjectiveSpace

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors, kangxyz
-/

import Motivic
import MotivicTest
import Lean.Util.CollectAxioms
/-! Adapted from the public Quillen 0.5.0 audit at commit
4444574cd12bdaab888bd65c79ffba79ce0640ce.

Audit every project-origin kernel declaration, including private helpers, and
every Motivic-namespaced declaration. Imported module name inventories avoid
forcing unrelated ConstantInfo values. The exact defining-origin predicate is
rechecked after deduplication, and local stage-2 declarations are included.
Transitive axiom collection and the allowed foundations are unchanged. -/

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "Exhaustive axiom audit requires legacy (.private) transitive imports"
  let selected (name : Name) : Bool :=
    let projectModule := match env.getModuleIdxFor? name with
      | some index => ((`Motivic).isPrefixOf env.header.moduleNames[index.toNat]! ||
          (`MotivicTest).isPrefixOf env.header.moduleNames[index.toNat]!)
      | none => false
    projectModule || (`Motivic).isPrefixOf name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let projectModule := ((`Motivic).isPrefixOf env.header.moduleNames[i]! ||
      (`MotivicTest).isPrefixOf env.header.moduleNames[i]!)
    for name in env.header.moduleData[i]!.constNames do
      if projectModule || (`Motivic).isPrefixOf name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError
          "Selected audit declaration {name} is missing from the checked kernel environment"
      count := count + 1
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo
    m!"Audited {count} project declarations (including private helpers): \
      only standard Lean logical foundations."

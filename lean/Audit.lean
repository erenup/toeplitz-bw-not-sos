import Lean

/-! Check every declaration defined in the imported project modules, including private
and generated declarations, using its transitive axiom dependency closure. -/
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modules := env.header.moduleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for module in modules do
    if module.getRoot == `ToeplitzSOS || module == `ToeplitzSOSRelease then
      IO.println s!"MODULE {module}"
  for (name, _) in env.constants.toList do
    let belongs := match env.getModuleIdxFor? name with
      | some index => (modules[index.toNat]!).getRoot == `ToeplitzSOS || modules[index.toNat]! == `ToeplitzSOSRelease
      | none => name.getRoot == `AuditTest
    if belongs then
      count := count + 1
      let axioms ← liftCoreM (collectAxioms name)
      let bad := axioms.filter fun ax => !allowed.contains ax
      unless bad.isEmpty do
        throwError "unexpected axioms for {name}: {bad}"
  if count == 0 then throwError "no project declarations checked"
  IO.println s!"CHECKED {count}"
  IO.println "PASS: axiom audit"

import Lean.CoreM
import Lean.Replay
import Lean.Util.CollectAxioms

/-!
Independent execution checker for target module declarations in Lean 4.35.
Imported dependencies are reused, not kernel-replayed by this invocation.
The caller must build project dependencies in an isolated workspace first.
Uses the current Kernel.Environment.replay API and audits every target constant.
-/
open Lean
namespace IndependentFVLTReplay435

instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def axiomsOf (env : Environment) (n : Name) : Array Name :=
  (collectAxioms n : ReaderT Environment Id (Array Name)).run env

-- Defense in depth; exact source-path/import-closure exclusion belongs to the runner.
-- 436: no substring test (435's `"g1"` substring also matched Ray.Multibrot.Log1p,
-- ...Seg1..., ...Padding1...). G1 = the ten modules inventoried as
-- `EXCLUDED: G1 hold #950` (g1_packed, g1_symmetry), listed exactly below; the
-- anchored per-component prefix "codexg1" mirrors that inventory's rule.
def g1ProjectModules : Array String := #[
  "CodexG1ListBenchV1", "CodexG1PackedAllV1", "CodexG1PackedBenchInputV1",
  "CodexG1PackedBenchV1", "CodexG1PackedKernelV1", "CodexG1PackedMachineV1",
  "CodexG1CompactPrefixV1", "CodexG1ForcingPeriodSixV1", "CodexG1PrefixQuotientV1",
  "CodexG1SymmetryTransferV1"]

def nameStringComponents : Name -> List String
  | .str p s => s :: nameStringComponents p
  | .num p _ => nameStringComponents p
  | .anonymous => []

def isG1ProjectName (n : Name) : Bool :=
  let s := n.toString
  !(s.startsWith "Mathlib." || s.startsWith "Lean." || s.startsWith "Init." ||
    s.startsWith "Std.") &&
  (nameStringComponents n).any (fun c => g1ProjectModules.contains c || c.toLower.startsWith "codexg1")

structure Loaded where
  env : Environment
  constants : Std.HashMap Name ConstantInfo
  importedModules : Array Name
  parts : Nat

unsafe def loadAndReplay (moduleName : Name) : IO Loaded := do
  if isG1ProjectName moduleName then
    throw <| IO.userError s!"Excluded G1 target: {moduleName}"
  let file ← findOLean moduleName
  let mut files := #[file]
  let server := OLeanLevel.server.adjustFileName file
  if ← server.pathExists then
    files := files.push server
    let privateFile := OLeanLevel.private.adjustFileName file
    if ← privateFile.pathExists then files := files.push privateFile
  let parts ← readModuleDataParts files
  let some (data, _) := parts[0]? | throw <| IO.userError "Empty target module data"
  if data.isModule && files.size != 3 then
    throw <| IO.userError "Modern module requires exported/server/private parts for full audit"
  let (_, state) ← importModulesCore data.imports |>.run
  let env ← finalizeImport state data.imports {} 0 false false (isModule := true)
  let importedModules := env.header.moduleNames
  for n in importedModules do
    if isG1ProjectName n then throw <| IO.userError s!"Excluded G1 project import: {n}"
  -- Lean's official checker uses the final part: it subsumes all prior parts.
  let some finalPart := parts[parts.size-1]? | throw <| IO.userError "No final module part"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for n in finalPart.1.constNames, ci in finalPart.1.constants do
    constants := constants.insert n ci
  let checked ← Lean.Kernel.Environment.replay constants env.toKernelEnv
  return { env := Environment.ofKernelEnv checked, constants, importedModules, parts := parts.size }

unsafe def check (moduleName : Name) : IO (Json × UInt32) := do
  let result ← loadAndReplay moduleName
  let mut failures : Array String := #[]
  let mut audit : Array Json := #[]
  let mut unsafeCount := 0
  let mut partialCount := 0
  for (n, ci) in result.constants do
    if ci.isUnsafe then
      unsafeCount := unsafeCount + 1
      failures := failures.push s!"Target unsafe constant (kernel replay skips it): {n}"
    if ci.isPartial then
      partialCount := partialCount + 1
      failures := failures.push s!"Target partial constant (kernel replay skips it): {n}"
    match ci with
    | .axiomInfo _ => failures := failures.push s!"Target introduces axiom: {n}"
    | _ => pure ()
    let axs := axiomsOf result.env n
    let bad := axs.filter (fun a => !allowedAxioms.contains a)
    if !bad.isEmpty then failures := failures.push s!"Disallowed axioms in {n}: {bad}"
    audit := audit.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
      ("axioms", toJson (axs.map (·.toString)))]
  let verdict := if failures.isEmpty then "PASS" else "FAIL"
  return (Json.mkObj [
    ("module",toJson moduleName.toString), ("verdict",toJson verdict),
    ("targetConstants",toJson result.constants.size),
    ("unsafeConstants",toJson unsafeCount), ("partialConstants",toJson partialCount),
    ("auditedConstants",toJson audit.size), ("declarations",toJson audit),
    ("moduleDataParts",toJson result.parts),
    ("importedModules",toJson (result.importedModules.map (·.toString))),
    ("kernelReplayCompleted",toJson true),
    ("fullDependencyReplay",toJson false),
    ("g1Excluded",toJson true), ("failures",toJson failures)],
    if failures.isEmpty then 0 else 1)

unsafe def main (args : List String) : IO UInt32 := do
  let [moduleName] := args | throw <| IO.userError "Expected exactly one target module name"
  initSearchPath (← findSysroot)
  try
    let (report, code) ← check moduleName.toName
    IO.println report.compress
    return code
  catch e =>
    IO.println <| (Json.mkObj [("module",toJson moduleName),
      ("verdict",toJson "FAIL"), ("kernelReplayCompleted",toJson false),
      ("error",toJson (toString e))]).compress
    return 1

end IndependentFVLTReplay435
unsafe def main := IndependentFVLTReplay435.main

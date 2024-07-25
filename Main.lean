/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Util.Paths
import Lean.Elab.Frontend
import AstExport

/-! # `lake exe ast-export` command

This command will export the AST of a lean file or project.

-/

def help : String := "AST export tool
Usage:
  lake exe ast-export <MODULE>..      # export modules reachable from these
  lake exe ast-export --one <MODULE>  # only export the given module

Arguments:
  <MODULE>  A module path like `Mathlib.Tactic.Basic`.
"

open Lean Elab Command Frontend

open System (FilePath)
variable (srcSearchPath : SearchPath) (pkg : Name) in
partial def visit (mod : Name) :
    StateT (HashMap Name (FilePath × Task (Except IO.Error Unit))) IO Unit := do
  if !pkg.isPrefixOf mod || (← get).contains mod then return
  let some fileName ← srcSearchPath.findModuleWithExt "lean" mod
      | throw <| .userError s!"{mod} not found"
  let (deps, _, _) ← parseImports (← IO.FS.readFile fileName) (some fileName.1)
  for dep in deps do
    visit dep.module
  let task ← IO.asTask do
    let out ← IO.Process.output {
      cmd := (← IO.appPath).toString
      args := #["--one", mod.toString]
    }
    if out.exitCode ≠ 0 then
      throw <| IO.userError
        s!"failure processing {mod} with exit code {out.exitCode}:\n{out.stderr}"
    IO.print out.stdout
  modify fun s => s.insert mod (fileName, task)

/-- The main entry point. See `help` for more information on arguments. -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let srcSearchPath ← initSrcSearchPath
  match args with
  | ["--one", mainModuleName] =>
    let mainModuleName := String.toName mainModuleName
    enableInitializersExecution
    let ast ← ASTExport.getASTForModule srcSearchPath mainModuleName
    let path := Lean.modToFilePath ".lake/build/lib" mainModuleName "out.json"
    IO.FS.writeFile path (toJson ast).pretty
    println! "wrote to {path}"
  | mods =>
    let mods := if mods.isEmpty then [`Mathlib] else mods.map String.toName
    -- Only submodules of `pkg` will be edited or have info reported on them
    let pkg := mods[0]!.components.head!
    let (_, mods) ← (mods.mapM (visit srcSearchPath pkg)).run {}
    mods.forM fun _ (_, task) =>
      match task.get with
      | .error e => throw e
      | .ok () => pure ()

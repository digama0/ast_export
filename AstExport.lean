/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Util.Paths
import Lean.Elab.Frontend

namespace ASTExport

open Lean Elab Command Frontend

instance : ToJson String.Pos := ⟨fun p => toJson p.1⟩
deriving instance ToJson for String.Range

instance : ToJson Substring where
  toJson s := toJson s.toString

instance : ToJson SourceInfo where
  toJson
  | .original leading pos trailing endPos =>
    json% { "leading": $leading, "pos": [$pos, $endPos], "trailing": $trailing }
  | .synthetic pos endPos false =>
    json% { "pos": [$pos, $endPos], "synthetic": true }
  | .synthetic pos endPos true =>
    json% { "pos": [$pos, $endPos], "canonical": true }
  | .none => .null

partial def Syntax.toJson : Syntax → Json
  | .missing => "missing"
  | .node info kind args =>
    have : ToJson Syntax := ⟨Syntax.toJson⟩
    if kind == nullKind then json% $args else
    json% { "info": $info, "kind": $kind, "args": $args }
  | .atom info val => json% { "info": $info, "val": $val }
  | .ident info rawVal val _ => json% { "info": $info, "rawVal": $rawVal, "val": $val }

instance : ToJson Syntax := ⟨Syntax.toJson⟩

instance : ToJson (TSyntax k) where
  toJson stx := toJson stx.raw

structure LeanFile where
  header : TSyntax ``Parser.Module.header
  commands : Array (TSyntax `command)
  deriving ToJson

partial def getASTForModule (srcSearchPath : SearchPath) (mainModuleName : Name) : IO LeanFile := do
  let some fileName ← srcSearchPath.findModuleWithExt "lean" mainModuleName
    | throw <| .userError s!"{mainModuleName} not found"
  let input ← IO.FS.readFile fileName
  let inputCtx := Parser.mkInputContext input fileName.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- allow `env` to be leaked, which would live until the end of the process anyway
  let opts := {}
  let (env, messages) ← processHeader (leakEnv := true) header opts messages inputCtx
  let env := env.setMainModule mainModuleName
  let mut commandState := Command.mkState env messages opts
  commandState := { commandState with infoState.enabled := true }
  let rec processCommands (commands : Array (TSyntax `command)) :
      FrontendM (Array (TSyntax `command)) := do
    updateCmdPos
    let cmdState ← getCommandState
    let ictx ← getInputContext
    let pstate ← getParserState
    let scope := cmdState.scopes.head!
    let pmctx := {
      env := cmdState.env, options := scope.opts
      currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps, messages) := profileit "parsing" scope.opts fun _ =>
      Parser.parseCommand ictx pmctx pstate cmdState.messages
    modify fun s => { s with commands := s.commands.push cmd }
    setParserState ps
    setMessages messages
    let edits ← runCommandElabM do
      let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
      Command.elabCommandTopLevel cmd
      let mut msgs := (← get).messages
      modify ({ · with messages := initMsgs ++ msgs })
      pure <| commands.push ⟨cmd⟩
    if Parser.isTerminalCommand cmd then return commands
    processCommands edits
  let (commands, _) ← (processCommands #[]).run { inputCtx := inputCtx }
    |>.run { commandState, parserState, cmdPos := parserState.pos }
  return { header := ⟨header⟩, commands : LeanFile }

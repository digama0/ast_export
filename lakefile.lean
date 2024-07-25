import Lake
open Lake DSL

package ast_export

lean_lib AstExport

@[default_target]
lean_exe «ast-export» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Module

namespace Lean
namespace Elab

def headerToImports (header : Syntax) : List Import :=
let header  := header.asNode;
let imports := if (header.getArg 0).isNone then [{Import . module := `Init.Default}] else [];
imports ++ (header.getArg 1).getArgs.toList.map (fun stx =>
  -- `stx` is of the form `(Module.import "import" "runtime"? id)
  let runtime := !(stx.getArg 1).isNone;
  let id      := stx.getIdAt 2;
  { module := normalizeModuleName id, runtimeOnly := runtime })

def processHeader (header : Syntax) (messages : MessageLog) (ctx : Parser.ParserContextCore) (trustLevel : UInt32 := 0) : IO (Environment × MessageLog) :=
catch
  (do env ← importModules (headerToImports header) trustLevel;
      pure (env, messages))
  (fun e => do
     env ← mkEmptyEnvironment;
     let spos := header.getPos.getD 0;
     let pos  := ctx.fileMap.toPosition spos;
     pure (env, messages.add { fileName := ctx.fileName, data := toString e, pos := pos }))

@[export lean_parse_imports]
def parseImports (input : String) (fileName : Option String := none) : IO (List Import × Position × MessageLog) :=
do env ← mkEmptyEnvironment;
   let fileName := fileName.getD "<input>";
   let ctx := Parser.mkParserContextCore env input fileName;
   match Parser.parseHeader env ctx with
   | (header, parserState, messages) => do
     pure (headerToImports header, ctx.fileMap.toPosition parserState.pos, messages)

@[export lean_print_deps]
def printDeps (deps : List Import) : IO Unit :=
deps.forM $ fun dep => do
  fname ← findOLean dep.module;
  IO.println fname

end Elab
end Lean

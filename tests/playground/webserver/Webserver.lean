-- -*- origami-fold-style: triple-braces -*-
import Lean

-- namespace Webserver {{{
namespace Webserver

structure State :=
  (verb : String)
  (path : String)
  (status := "200 OK")
  (outHeaders : Array String := #[])
  (out : String := "")
  (tryNextHandler := false)

abbrev HandlerM := StateT State IO
abbrev Handler := HandlerM Unit

def checkVerb (verb : String) : Handler := do
  let st ← get
  if st.verb != verb then
    throw $ IO.userError "invalid verb"

def checkPathLiteral (p : String) : Handler := do
  let st ← get
  if p.isPrefixOf st.path then
    set { st with path := st.path.extract p.bsize st.path.bsize }
  else
    throw $ IO.userError "invalid path"

def getPathPart : HandlerM String := do
  let st ← get
  let stop := st.path.posOf '/'
  set { st with path := st.path.extract stop st.path.bsize }
  pure $ st.path.extract 0 stop

def checkPathConsumed : Handler := do
  let st ← get
  if st.path != "" then
    throw $ IO.userError "invalid path"

def write (out : String) : Handler := do
  modify fun st => { st with out := st.out ++ out }

def redirect (url : String) : Handler := do
  modify fun st => { st with status := "307 Temporary Redirect", outHeaders := #["Location: " ++ url] }

def notFound : Handler := do
  modify fun st => { st with status := "404 Not Found" }
  write "whoops"

def mkHandlersRef : IO (IO.Ref (List Handler)) :=
  IO.mkRef ∅

@[init mkHandlersRef]
constant handlersRef : IO.Ref (List Handler)

def registerHandler (h : Handler) : IO Unit := do
  handlersRef.modify fun hs => h::hs

partial def parseHeaders (hIn : IO.FS.Stream) : IO Unit := do
  let line ← hIn.getLine
  if line == "" || line == "\r\n" then pure () else parseHeaders hIn

partial def run (hIn hOut : IO.FS.Stream) : IO Unit := do
  let line ← hIn.getLine
  if line != "" then
    let [verb, path, proto] ← line.splitOn " "
      | panic! "failed to parse request: " ++ line
    let stderr ← IO.getStderr
    stderr.putStrLn $ "=> " ++ verb ++ " " ++ path
    let headers ← parseHeaders hIn
    let handlers ← handlersRef.get
    let (_, st) ← handlers.foldr (· <|> ·) notFound { verb, path }
    stderr.putStrLn $ "<= " ++ st.status
    hOut.putStrLn $ "HTTP/1.1 " ++ st.status
    hOut.putStrLn "Content-Type: text/html"
    hOut.putStrLn $ "Content-Length: " ++ toString st.out.bsize
    st.outHeaders.forM hOut.putStrLn
    hOut.putStrLn ""
    hOut.putStr st.out
    hOut.flush
    run hIn hOut

end Webserver
--}}}


open Lean
open Lean.Parser
open Lean.PrettyPrinter

-- declare_syntax_cat element {{{
declare_syntax_cat element
declare_syntax_cat child

syntax "<" ident "/>" : element
syntax "<" ident ">" child* "</" ident ">" : element

-- "JSXTextCharacter : SourceCharacter but not one of {, <, > or }"
def text : Parser := -- {{{
  withAntiquot (mkAntiquot "text" `LX.text) {
    fn := fun c s =>
      let startPos := s.pos
      let s := takeWhile1Fn (not ∘ "{<>}$".contains) "HTML text" c s
      mkNodeToken `LX.text startPos c s } -- }}}

@[combinator_formatter text] def text.formatter : Formatter := pure ()
@[combinator_parenthesizer text] def text.parenthesizer : Parenthesizer := pure ()

syntax text         : child
syntax "{" term "}" : child
syntax element      : child

syntax:max element : term

macro_rules
  | `(<$n/>) => quote ("<" ++ toString n.getId ++ "/>")
  | `(<$n>$cs*</$m>) => -- {{{
    if n.getId == m.getId then do
      let cs ← cs.mapM fun c => match c with
        | `(child|$t:text)    => pure $ quote t[0].getAtomVal!
        | `(child|{$t})       => pure t
        | `(child|$e:element) => `($e:element)
        | _                   => unreachable!
      let cs := cs.push (quote ("</" ++ toString m.getId ++ ">"))
      cs.foldlM (fun s e => `($s ++ $e)) (quote ("<" ++ toString n.getId ++ ">"))
    else Macro.throwError ("expected </" ++ toString n.getId ++ ">")
-- }}}
-- }}}

-- open Webserver {{{
open Webserver

def pathLiteral : Parser := -- {{{
  withAntiquot (mkAntiquot "pathLiteral" `pathLiteral) {
  fn := fun c s =>
    let startPos := s.pos
    let s := takeWhile1Fn (fun c => c == '/' || c.isAlphanum) "URL path" c s
    mkNodeToken `pathLiteral startPos c s } -- }}}

@[combinator_formatter pathLiteral] def pathLiteral.formatter : Formatter := pure ()
@[combinator_parenthesizer pathLiteral] def pathLiteral.parenthesizer : Parenthesizer := pure ()

declare_syntax_cat pathItem
syntax pathLiteral : pathItem
syntax "{" ident "}" : pathItem
declare_syntax_cat path
syntax pathItem* : path

declare_syntax_cat verb
syntax "GET" : verb
syntax "POST" : verb

macro v:verb p:path " => " t:term : command => do -- {{{
  let `(path| $[$pis:pathItem]* ) ← p
    | unreachable!
  let t ← `(do checkPathConsumed; $t:term)
  let t ← pis.foldrM (fun pi t => match pi with
    | `(pathItem|$l:pathLiteral) => `(do checkPathLiteral $(quote l[0].getAtomVal!); $t:term)
    | `(pathItem|{$id}) => `(do let $id:ident ← getPathPart; $t:term)
    | _ => Macro.throwError s!"unknown pathItem '{Syntax.formatStx pi}'") t
  `(def handler : Handler := do
      checkVerb $(quote v[0].getAtomVal!)
      $t:term

    @[init] def reg : IO Unit := registerHandler handler)
-- }}}

GET / => redirect "/greet/stranger"

GET /greet/{name} => write
  <html>
    <h1>Hello, {name}!</h1>
  </html>

def main : IO Unit := do
  let hIn ← IO.getStdin
  let hOut ← IO.getStdout
  Webserver.run hIn hOut
-- }}}

#check let name := "PLDI"
       (<h1>Hello, {name}!</h1>)

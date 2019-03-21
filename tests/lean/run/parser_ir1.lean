import init.Lean.Ir.Parser init.Lean.Ir.Format
import init.Lean.Ir.elimPhi init.Lean.Ir.typeCheck
import init.Lean.Ir.extractCpp

open Lean.Parser
open Lean.Parser.MonadParsec
open Lean.Ir

abbreviation m := ExceptT String IO

def checkDecl (d : Decl) : m Unit :=
match typeCheck d with
| Except.ok _    := pure ()
| Except.error e := IO.println (toString e)

def showResult (p : Parsec' Decl) (s : String) : m Unit :=
match Parsec.parse p s with
| Except.ok d    := IO.println (Lean.toFmt d) *> checkDecl d
| Except.error e := IO.println e

def IR1 := "
def succ (x : UInt32) : UInt32 :=
main: one : UInt32 := 1; x1 : UInt32 := add x one; ret x1;
"

#eval showResult (whitespace *> parseDef) IR1

def IR2 := "
def addN (x : UInt32) (y : UInt32) (n : UInt32) : UInt32 :=
main: jmp loop;
loop:
  r1   : UInt32 := phi x r2;
  y1   : UInt32 := phi y y1;
  n1   : UInt32 := phi n n2;
  r2   : UInt32 := add r1 y1;
  one  : UInt32 := 1;
  n2   : UInt32 := sub n1 one;
  zero : UInt32 := 0;
  c    : Bool   := Eq n2 zero;
  case c [loop, end];
end:
  r3   : UInt32 := phi r2;
  ret r3;
"

#eval showResult (whitespace *> parseDef) IR2

def tstElimPhi (s : String) : m Unit :=
do d ← MonadExcept.liftExcept $ Parsec.parse (whitespace *> parseDef) s,
   checkDecl d,
   IO.println (Lean.toFmt (elimPhi d))

#exit

#eval tstElimPhi IR2

def IR3 := "
def mkStruct (d1 : object) (d2 : UInt32) (d3 : Usize) (d4 : UInt32) (d5 : Bool) (d6 : Bool) : object :=
main:
  o := cnstr 0 1 18;
  set o 0 d1;
  sset o 8 d3;
  sset o 16 d2;
  sset o 20 d4;
  sset o 24 d5;
  sset o 25 d6;
  ret o;
"
#eval showResult (whitespace *> parseDef) IR3

def tstExtractCpp (s : String) : m Unit :=
do d ← MonadExcept.liftExcept $ Parsec.parse (whitespace *> parseDef) s,
   checkDecl d,
   match extractCpp [elimPhi d] with
   | Except.ok code := IO.println code
   | Except.error s := IO.println s

#eval tstExtractCpp IR3
#eval tstExtractCpp IR2

def IR4 := "
def swap (d1 : object) (d2 : object) : object object :=
main:
  r1 := cnstr 0 2 0;
  r2 := cnstr 0 2 0;
  set r1 0 d1;
  set r1 1 d2;
  inc d1;
  inc d2;
  set r2 0 d2;
  set r2 1 d1;
  ret r1 r2;
"

#eval tstExtractCpp IR4

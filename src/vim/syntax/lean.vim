" Vim syntax file
" Language:		Lean
" Filename extensions:	*.lean, *.ilean
" Maintainer:		Simon Cruanes
" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
        syntax clear
"elseif exists("b:current_syntax")
"	finish
endif

if version >= 600
  setlocal iskeyword=@,48-57,_,-,!,#,$,%
else
  set iskeyword=@,48-57,_,-,!,#,$,%
endif

" tabs = evil
set expandtab

syn case match

" keywords
syn keyword leanKeyword import prelude tactic_hint protected private noncomputable
syn keyword leanKeyword def definition renaming hiding exposing parameter parameters
syn keyword leanKeyword begin proof qed conjecture constant constants hypothesis lemma
syn keyword leanKeyword corollary variable variables premise premises theory print theorem proposition
syn keyword leanKeyword example abstract open as export override axiom axioms inductive
syn keyword leanKeyword with structure record universe universes alias help environment options
syn keyword leanKeyword precedence reserve match infix infixl infixr notation postfix prefix
syn keyword leanKeyword tactic_infix tactic_infixl tactic_infixr tactic_notation tactic_postfix
syn keyword leanKeyword meta run_command do
syn keyword leanKeyword tactic_prefix eval check end reveal this suppose using namespace section
syn keyword leanKeyword fields find_decl attribute local set_option extends include omit classes
syn keyword leanKeyword instances coercions attributes raw migrate replacing calc have show suffices
syn keyword leanKeyword by in at let forall fun exists if dif then else assume assert take obtain from

syn match leanOp        ":"
syn match leanOp        "="

" constants
syn keyword leanConstant "#" "@" "->" "∼" "↔" "/" "==" ":=" "<->" "/\\" "\\/" "∧" "∨" ">>=" ">>"
syn keyword leanConstant ≠ < > ≤ ≥ ¬ <= >= ⁻¹ ⬝ ▸ + * - / λ
syn keyword leanConstant → ∃ ∀ Π ←

" modifiers (pragmas)
syn keyword leanModifier contained containedin=leanBracketEncl persistent notation visible instance trans_instance class parsing_only
syn keyword leanModifier contained containedin=leanBracketEncl coercion unfold_full constructor reducible irreducible semireducible
syn keyword leanModifier contained containedin=leanBracketEncl wf whnf multiple_instances none decls declarations coercions
syn keyword leanModifier contained containedin=leanBracketEncl classes symm subst refl trans simp congr notations
syn keyword leanModifier contained containedin=leanBracketEncl begin_end_hints tactic_hints reduce_hints unfold_hints aliases eqv
syn keyword leanModifier contained containedin=leanBracketEncl localrefinfo

" delimiters

syn match       leanBraceErr   "}"
syn match       leanParenErr   ")"
syn match       leanBrackErr   "\]"

syn region      leanEncl            matchgroup=leanDelim start="(" end=")" contains=ALLBUT,leanParenErr,leanModifier keepend
syn region      leanBracketEncl     matchgroup=leanDelim start="\[" end="\]" contains=ALLBUT,leanBrackErr keepend
syn region      leanEncl            matchgroup=leanDelim start="{"  end="}" contains=ALLBUT,leanBraceErr,leanModifier keepend

" FIXME(gabriel): distinguish backquotes in notations from names
" syn region      leanNotation        start=+`+    end=+`+

syn keyword	leanTodo	containedin=leanComment TODO FIXME BUG FIX

syn region      leanComment	start=+/-+ end=+-/+ contains=leanTodo
syn match       leanComment     contains=leanTodo +--.*+

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_lean_syntax_inits")
  if version < 508
    let did_lean_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink leanTodo               Todo

  HiLink leanComment		Comment

  HiLink leanKeyword            Keyword
  HiLink leanConstant           Constant
  HiLink leanModifier           Special
  HiLink leanDelim              Keyword  " Delimiter is bad
  HiLink leanOp                 Keyword

  HiLink leanNotation           String

  HiLink leanBraceError         Error
  HiLink leanParenError         Error
  HiLink leanBracketError       Error

  delcommand HiLink
end

let b:current_syntax = "lean"

" vim: ts=8 sw=8

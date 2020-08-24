// Lean compiler output
// Module: Lean.Syntax
// Imports: Init Lean.Data.Name Lean.Data.Format
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Syntax_reprint___main___closed__1;
lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq___main___at_Lean_Syntax_structEq___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Prod_hasQuote___rarg___closed__1;
lean_object* l_Lean_Syntax_reprint___main___boxed(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hasQuote___closed__1;
lean_object* l___private_Lean_Syntax_4__updateFirst___main(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_Lean_Syntax_getTailWithPos(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_4__updateFirst(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint___boxed(lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_structEq___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Syntax_7__quoteName___main(lean_object*);
lean_object* l_Lean_Syntax_modifyArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__5;
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l_Lean_Syntax_ifNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_2__updateLeadingAux(lean_object*, lean_object*);
lean_object* l_Lean_Substring_HasQuote___closed__4;
lean_object* l_Lean_Syntax_HasToString;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__2;
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object*, lean_object*);
lean_object* l_Lean_Array_hasQuote___rarg___closed__2;
lean_object* l___private_Lean_Syntax_8__quoteList___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_structHasBeq___closed__1;
lean_object* l_Array_isEqvAux___main___at_Lean_Syntax_structEq___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_7__quoteName(lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs(lean_object*);
lean_object* l___private_Lean_Syntax_3__updateLast(lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__1;
lean_object* l_Lean_Substring_HasQuote(lean_object*);
lean_object* l_List_beq___main___at_Lean_Syntax_structEq___main___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Substring_HasQuote___closed__2;
lean_object* l_Lean_Substring_HasQuote___closed__1;
lean_object* l_Lean_Syntax_getAtomVal_x21___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Substring_HasQuote___boxed(lean_object*);
lean_object* l_Lean_Syntax_reprint___main(lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2;
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__1;
lean_object* l_Lean_Syntax_mrewriteBottomUp(lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Prod_hasQuote___rarg___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__6;
lean_object* l_Lean_Syntax_setAtomVal(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_3__updateLast___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs___boxed(lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1;
lean_object* l_Lean_Syntax_Lean_HasFormat(lean_object*);
extern lean_object* l_Nat_HasOfNat___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_SyntaxNode_getKind(lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs(lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Syntax_structEq___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__8;
lean_object* l___private_Lean_Syntax_5__reprintLeaf___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNode(lean_object*);
lean_object* l___private_Lean_Syntax_3__updateLast___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__4;
lean_object* l_Lean_SyntaxNode_getIdAt(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__6;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_replaceInfo___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__2;
lean_object* l___private_Lean_Syntax_8__quoteList___main(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateTrailing(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Syntax_mreplace___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_6__formatInfo(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l_Lean_Syntax_structEq___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg(lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeMissing(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_String_HasQuote(lean_object*);
lean_object* l_Lean_Syntax_formatStx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceInfo___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__5;
lean_object* l_Lean_Syntax_formatStxAux___main___closed__3;
lean_object* l_Lean_Syntax_copyInfo___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos___boxed(lean_object*);
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Array_hasQuote___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__9;
lean_object* l___private_Lean_Syntax_4__updateFirst___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hasQuote;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_Lean_Syntax_replaceInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isMissing___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__4;
lean_object* l_Lean_Syntax_mreplace(lean_object*);
uint8_t l_Lean_Syntax_structEq___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1;
lean_object* l___private_Lean_Syntax_4__updateFirst___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_3__updateLast___main(lean_object*);
lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_Array_hasQuote___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_9__quoteOption(lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object*);
lean_object* l_Lean_Array_hasQuote___rarg___closed__1;
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1___boxed(lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailWithPos___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l_Lean_List_hasQuote(lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7;
lean_object* l_Lean_Syntax_getTailInfo___main___boxed(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Syntax_ifNode___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode___boxed(lean_object*);
uint8_t l_List_beq___main___at_Lean_Syntax_structEq___main___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2___boxed(lean_object*);
lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateTrailing___main(lean_object*, lean_object*);
lean_object* l_Lean_Option_hasQuote(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailWithPos___main___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_unreachIsNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
extern lean_object* l_Lean_formatDataValue___closed__2;
lean_object* l___private_Lean_Syntax_4__updateFirst___main___at_Lean_Syntax_setHeadInfoAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_Syntax_setArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Array_hasQuote(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object*);
extern lean_object* l_Lean_Format_paren___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Prod_hasQuote___rarg___closed__3;
lean_object* l___private_Lean_Syntax_5__reprintLeaf(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setHeadInfoAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Syntax_HasToString___closed__2;
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs___rarg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList(lean_object*);
lean_object* l_Lean_List_hasQuote___rarg(lean_object*);
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1;
lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__5;
lean_object* l_Lean_Syntax_setTailInfoAux___main(lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Nat_HasQuote(lean_object*);
lean_object* lean_mk_syntax_atom(lean_object*);
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkCAppStx(lean_object*, lean_object*);
lean_object* lean_mk_syntax_num_lit(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_HasToString___closed__1;
lean_object* l_Lean_Syntax_structHasBeq;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_mrewriteBottomUp___main(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg___lambda__1(lean_object*);
lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_HasToString___lambda__1(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos___main(lean_object*);
lean_object* lean_mk_syntax_list(lean_object*);
uint8_t l_List_beq___main___at_Lean_Syntax_structEq___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Prod_hasQuote___rarg___closed__4;
lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__1;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__6;
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_mk_syntax_str_lit(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_Syntax_isAntiquot___closed__1;
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__4;
lean_object* l___private_Lean_Syntax_1__updateInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Prod_hasQuote___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_HasQuote;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_6__formatInfo___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Prod_hasQuote(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_4__updateFirst___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
extern lean_object* l_String_Inhabited;
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__1;
lean_object* l_Lean_Syntax_isQuot___boxed(lean_object*);
lean_object* l_Lean_Syntax_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_mkNode(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isQuot___closed__1;
lean_object* l_Lean_Syntax_getTailInfo___main(lean_object*);
lean_object* l_Lean_SyntaxNode_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__7;
lean_object* l_Lean_Substring_HasQuote___closed__3;
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__3;
lean_object* l_Lean_Option_hasQuote___rarg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_2);
return x_7;
}
}
}
uint8_t l_Lean_Syntax_isMissing(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Syntax_isMissing___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isMissing(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_isQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quot");
return x_1;
}
}
uint8_t l_Lean_Syntax_isQuot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_Syntax_isQuot___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isQuot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_isAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot");
return x_1;
}
}
uint8_t l_Lean_Syntax_isAntiquot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_Syntax_isAntiquot___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAntiquot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_unreachIsNodeMissing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_unreachIsNodeAtom(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_unreachIsNodeIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_unreachIsNodeIdent(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_SyntaxNode_getKind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SyntaxNode_getKind(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_withArgs___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_SyntaxNode_withArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SyntaxNode_withArgs___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SyntaxNode_getNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_inhabited;
x_5 = lean_array_get(x_4, x_3, x_2);
return x_5;
}
}
lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SyntaxNode_getArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SyntaxNode_getArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SyntaxNode_getArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* _init_l_Lean_Syntax_getAtomVal_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getAtomVal_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getAtomVal!: not an atom");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getAtomVal_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Syntax_getAtomVal_x21___closed__1;
x_2 = lean_unsigned_to_nat(80u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Syntax_getAtomVal_x21___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_getAtomVal_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_String_Inhabited;
x_4 = l_Lean_Syntax_getAtomVal_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_getAtomVal_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getAtomVal_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_setAtomVal(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_ifNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_apply_1(x_2, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_ifNode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_ifNode___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_ifNodeKind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_name_eq(x_5, x_2);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Syntax_ifNodeKind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_ifNodeKind___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_ifNodeKind___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_ifNodeKind___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Syntax_asNode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_2; 
x_2 = l_Lean_mkOptionalNode___closed__1;
return x_2;
}
}
}
lean_object* l_Lean_Syntax_asNode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_asNode(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Syntax_asNode(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_setArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_modifyArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_setArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_set(x_5, x_2, x_3);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_array_set(x_8, x_2, x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_setArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_setArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_modifyArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_5, x_2);
x_9 = lean_box(0);
x_10 = lean_array_fset(x_5, x_2, x_9);
x_11 = lean_apply_1(x_3, x_8);
x_12 = lean_array_fset(x_10, x_2, x_11);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_array_fget(x_14, x_2);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_14, x_2, x_19);
x_21 = lean_apply_1(x_3, x_18);
x_22 = lean_array_fset(x_20, x_2, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_modifyArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_getIdAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getIdAt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mreplace___main___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__2___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = x_3;
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_10 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_7, x_9, x_8);
x_11 = x_10;
x_12 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__3), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_4);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_14);
return x_17;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
x_13 = lean_apply_1(x_2, x_3);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__4), 6, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_box(0);
x_4 = x_16;
goto block_9;
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mreplace___main___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_mreplace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mreplace___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mreplace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mrewriteBottomUp___main___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = x_5;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_7, x_9, x_8);
x_11 = x_10;
x_12 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__2), 3, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_apply_1(x_2, x_3);
return x_14;
}
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mrewriteBottomUp___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = x_4;
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_7 = l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(x_1, x_6, x_5);
x_8 = x_7;
lean_ctor_set(x_2, 1, x_8);
x_9 = lean_apply_1(x_1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = x_11;
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_14 = l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(x_1, x_13, x_12);
x_15 = x_14;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_1(x_1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_apply_1(x_1, x_2);
return x_18;
}
}
}
lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_1__updateInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_free_object(x_3);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_ctor_set(x_5, 2, x_13);
lean_ctor_set(x_5, 1, x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_3, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_19 = x_5;
} else {
 lean_dec_ref(x_5);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 3, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_3, 0, x_21);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_17);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_23);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_26 = x_1;
} else {
 lean_dec_ref(x_1);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 3, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
if (lean_is_scalar(x_26)) {
 x_32 = lean_alloc_ctor(0, 3, 0);
} else {
 x_32 = x_26;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
return x_32;
}
}
}
}
}
lean_object* l___private_Lean_Syntax_2__updateLeadingAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Syntax_1__updateInfo(x_3, x_2);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_4, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Syntax_1__updateInfo(x_3, x_2);
lean_ctor_set(x_1, 0, x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_21 = x_4;
} else {
 lean_dec_ref(x_4);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Syntax_1__updateInfo(x_3, x_2);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
}
case 3:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l___private_Lean_Syntax_1__updateInfo(x_27, x_2);
lean_ctor_set(x_1, 0, x_36);
lean_ctor_set(x_28, 0, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l___private_Lean_Syntax_1__updateInfo(x_27, x_2);
lean_ctor_set(x_1, 0, x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_1);
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_47 = x_28;
} else {
 lean_dec_ref(x_28);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_46, 2);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Syntax_1__updateInfo(x_27, x_2);
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
}
}
default: 
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_2);
return x_54;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = x_2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = x_8;
x_12 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_1, x_15);
x_17 = x_13;
x_18 = lean_array_fset(x_10, x_1, x_17);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_18;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_1, 1);
x_40 = x_39;
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2), 3, 2);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_40);
x_43 = x_42;
x_44 = lean_apply_1(x_43, x_2);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set(x_1, 1, x_46);
lean_ctor_set(x_44, 0, x_1);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_1, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_52 = x_51;
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2), 3, 2);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_52);
x_55 = x_54;
x_56 = lean_apply_1(x_55, x_2);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_57);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_3 = x_62;
goto block_37;
}
block_37:
{
lean_dec(x_3);
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Syntax_1__updateInfo(x_4, x_2);
lean_ctor_set(x_1, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Syntax_1__updateInfo(x_4, x_2);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
case 3:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Syntax_1__updateInfo(x_19, x_2);
lean_ctor_set(x_1, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_1, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l___private_Lean_Syntax_1__updateInfo(x_19, x_2);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
default: 
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_2);
return x_36;
}
}
}
}
}
lean_object* l_Lean_Syntax_updateLeading(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_updateTrailing___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_1);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = l_Lean_Syntax_inhabited;
x_14 = lean_array_get(x_13, x_4, x_12);
x_15 = l_Lean_Syntax_updateTrailing___main(x_1, x_14);
x_16 = lean_array_set(x_4, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_16);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_5);
x_19 = l_Lean_Syntax_inhabited;
x_20 = lean_array_get(x_19, x_4, x_18);
x_21 = l_Lean_Syntax_updateTrailing___main(x_1, x_20);
x_22 = lean_array_set(x_4, x_18, x_21);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
case 2:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = l_Lean_SourceInfo_updateTrailing(x_25, x_1);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = l_Lean_SourceInfo_updateTrailing(x_27, x_1);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
default: 
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = l_Lean_SourceInfo_updateTrailing(x_32, x_1);
lean_ctor_set(x_2, 0, x_33);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_38 = l_Lean_SourceInfo_updateTrailing(x_34, x_1);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
return x_39;
}
}
}
}
}
lean_object* l_Lean_Syntax_updateTrailing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_updateTrailing___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_getPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailWithPos___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = lean_array_fget(x_1, x_8);
x_10 = l_Lean_Syntax_getTailWithPos___main(x_9);
if (lean_obj_tag(x_10) == 0)
{
x_2 = x_8;
x_3 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
}
lean_object* l_Lean_Syntax_getTailWithPos___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailWithPos___main___spec__1(x_3, x_4, lean_box(0));
lean_dec(x_3);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
}
}
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailWithPos___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailWithPos___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_getTailWithPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailWithPos___main(x_1);
return x_2;
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = lean_array_fget(x_1, x_8);
x_10 = l_Lean_Syntax_getTailInfo___main(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
x_2 = x_8;
x_3 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
}
lean_object* l_Lean_Syntax_getTailInfo___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(x_3, x_4, lean_box(0));
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
lean_object* l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_getTailInfo___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getTailInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_3__updateLast___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_inc(x_1);
x_9 = lean_array_get(x_1, x_2, x_8);
lean_inc(x_3);
x_10 = lean_apply_1(x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_array_set(x_2, x_8, x_13);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_array_set(x_2, x_8, x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
}
}
lean_object* l___private_Lean_Syntax_3__updateLast___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_3__updateLast___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_3__updateLast___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Syntax_3__updateLast___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Syntax_3__updateLast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_3__updateLast___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_Syntax_inhabited;
x_9 = lean_array_get(x_8, x_2, x_7);
lean_inc(x_1);
x_10 = l_Lean_Syntax_setTailInfoAux___main(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_array_set(x_2, x_7, x_13);
lean_dec(x_7);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_array_set(x_2, x_7, x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
}
}
lean_object* l_Lean_Syntax_setTailInfoAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_2);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_array_get_size(x_15);
x_17 = l___private_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(x_1, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
case 2:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 0);
lean_dec(x_24);
lean_ctor_set(x_2, 0, x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 0);
lean_dec(x_30);
lean_ctor_set(x_2, 0, x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_setTailInfoAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_setTailInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_setTailInfoAux___main(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l_Lean_Syntax_unsetTrailing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 2);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 2, x_6);
x_7 = l_Lean_Syntax_setTailInfo(x_1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_Syntax_setTailInfo(x_1, x_11);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Syntax_4__updateFirst___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_1, x_3);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_fset(x_1, x_3, x_13);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_fset(x_1, x_3, x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
lean_object* l___private_Lean_Syntax_4__updateFirst___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_4__updateFirst___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_4__updateFirst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Syntax_4__updateFirst___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Syntax_4__updateFirst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Syntax_4__updateFirst___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_4__updateFirst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Syntax_4__updateFirst(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_4__updateFirst___main___at_Lean_Syntax_setHeadInfoAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_Syntax_setHeadInfoAux___main(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_fset(x_2, x_3, x_13);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_fset(x_2, x_3, x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
lean_object* l_Lean_Syntax_setHeadInfoAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Syntax_4__updateFirst___main___at_Lean_Syntax_setHeadInfoAux___main___spec__1(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_2);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Syntax_4__updateFirst___main___at_Lean_Syntax_setHeadInfoAux___main___spec__1(x_1, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
case 2:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 0);
lean_dec(x_24);
lean_ctor_set(x_2, 0, x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 0);
lean_dec(x_30);
lean_ctor_set(x_2, 0, x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_setHeadInfoAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_setHeadInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_setHeadInfoAux___main(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l_Lean_Syntax_setInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
case 3:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_12 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_replaceInfo___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Syntax_replaceInfo___main(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_replaceInfo___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = x_4;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_umapMAux___main___at_Lean_Syntax_replaceInfo___main___spec__1(x_1, x_6, x_5);
x_8 = x_7;
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = x_10;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_umapMAux___main___at_Lean_Syntax_replaceInfo___main___spec__1(x_1, x_12, x_11);
x_14 = x_13;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Syntax_setInfo(x_1, x_2);
return x_16;
}
}
}
lean_object* l_Lean_Syntax_replaceInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_replaceInfo___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_copyInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getHeadInfo___main(x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Syntax_setInfo(x_4, x_1);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_copyInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_copyInfo(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_5__reprintLeaf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_String_Iterator_HasRepr___closed__2;
x_6 = lean_string_append(x_5, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; 
x_7 = lean_string_append(x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 2);
x_12 = lean_string_utf8_extract(x_9, x_10, x_11);
x_13 = lean_string_append(x_6, x_12);
lean_dec(x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_string_utf8_extract(x_16, x_17, x_18);
x_20 = lean_string_append(x_19, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_String_Iterator_HasRepr___closed__2;
x_22 = lean_string_append(x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_23, 0);
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 2);
x_27 = lean_string_utf8_extract(x_24, x_25, x_26);
x_28 = lean_string_append(x_20, x_27);
lean_dec(x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Syntax_5__reprintLeaf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Syntax_5__reprintLeaf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_Lean_Syntax_reprint___main(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_string_append(x_4, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_Lean_Syntax_reprint___main(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_string_dec_eq(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_3 = x_15;
goto _start;
}
}
}
}
}
lean_object* _init_l_Lean_Syntax_reprint___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_reprint___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint___main___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_choiceKind;
x_6 = lean_name_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_splitAux___main___closed__1;
x_9 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(x_4, x_4, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Syntax_inhabited;
x_14 = lean_array_get(x_13, x_4, x_11);
x_15 = l_Lean_Syntax_reprint___main(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(x_4, x_4, x_18, x_17);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = l___private_Lean_Syntax_5__reprintLeaf(x_21, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_string_utf8_extract(x_27, x_28, x_29);
x_31 = l___private_Lean_Syntax_5__reprintLeaf(x_26, x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_reprint___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_reprint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_reprint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Syntax_6__formatInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_6__formatInfo(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Format_join___closed__1;
x_7 = x_37;
goto block_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 2);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_string_utf8_extract(x_39, x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_43 = l_String_quote(x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = 0;
x_46 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_45);
x_7 = x_47;
goto block_36;
}
block_36:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_8);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_25; 
x_25 = l_Lean_Format_join___closed__1;
x_10 = x_25;
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = l_Nat_repr(x_26);
x_28 = l_addParenHeuristic(x_27);
lean_dec(x_27);
x_29 = l_Option_HasRepr___rarg___closed__2;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Option_HasRepr___rarg___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_35 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_8);
x_10 = x_35;
goto block_24;
}
block_24:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_8);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Format_join___closed__1;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_string_utf8_extract(x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_19 = l_String_quote(x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_8);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_8);
return x_23;
}
}
}
}
}
}
lean_object* l___private_Lean_Syntax_6__formatInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Syntax_6__formatInfo(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 0;
lean_inc(x_2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
x_9 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_4, x_2);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<missing>");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("..");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_formatStxAux___main___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Format_sbracket___closed__2;
x_3 = l_Lean_Syntax_formatStxAux___main___closed__4;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Syntax_formatStxAux___main___closed__6;
x_3 = l_Lean_Format_sbracket___closed__3;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_sbracket___closed__1;
x_2 = l_Lean_Syntax_formatStxAux___main___closed__7;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__8;
x_2 = lean_format_group(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Syntax_formatStxAux___main___closed__2;
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
x_10 = l_Lean_nullKind;
x_11 = lean_name_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_12 = l_Lean_mkAppStx___closed__4;
x_13 = lean_box(0);
x_14 = l_Lean_Name_replacePrefix___main(x_6, x_12, x_13);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_14);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_array_get_size(x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_9);
x_49 = l_Array_toList___rarg(x_7);
lean_dec(x_7);
x_50 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_2, x_3, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(1);
x_53 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_51, x_52);
lean_dec(x_51);
x_54 = 0;
x_55 = l_Lean_Format_paren___closed__2;
x_56 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_54);
x_57 = l_Lean_Format_paren___closed__3;
x_58 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_54);
x_59 = l_Lean_Format_paren___closed__1;
x_60 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_format_group(x_60);
return x_61;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_9);
x_21 = x_9;
goto block_48;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_21 = x_62;
goto block_48;
}
}
block_48:
{
uint8_t x_22; 
x_22 = lean_nat_dec_lt(x_21, x_9);
lean_dec(x_9);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = l_Array_toList___rarg(x_7);
lean_dec(x_7);
x_24 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_2, x_3, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(1);
x_27 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_25, x_26);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Lean_Format_paren___closed__2;
x_30 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_28);
x_31 = l_Lean_Format_paren___closed__3;
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_28);
x_33 = l_Lean_Format_paren___closed__1;
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_format_group(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_7);
lean_dec(x_1);
x_36 = l_Lean_Syntax_formatStxAux___main___closed__5;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(1);
x_39 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_37, x_38);
lean_dec(x_37);
x_40 = 0;
x_41 = l_Lean_Format_paren___closed__2;
x_42 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_40);
x_43 = l_Lean_Format_paren___closed__3;
x_44 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_40);
x_45 = l_Lean_Format_paren___closed__1;
x_46 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_format_group(x_46);
return x_47;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_6);
x_63 = lean_array_get_size(x_7);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_lt(x_64, x_63);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_9);
x_66 = l_Array_toList___rarg(x_7);
lean_dec(x_7);
x_67 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_2, x_3, x_66);
x_68 = lean_box(1);
x_69 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_67, x_68);
lean_dec(x_67);
x_70 = 0;
x_71 = l_Lean_Format_sbracket___closed__2;
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_70);
x_73 = l_Lean_Format_sbracket___closed__3;
x_74 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_70);
x_75 = l_Lean_Format_sbracket___closed__1;
x_76 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_format_group(x_76);
return x_77;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_78; 
x_78 = lean_nat_dec_lt(x_9, x_9);
lean_dec(x_9);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = l_Array_toList___rarg(x_7);
lean_dec(x_7);
x_80 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_2, x_3, x_79);
x_81 = lean_box(1);
x_82 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_80, x_81);
lean_dec(x_80);
x_83 = 0;
x_84 = l_Lean_Format_sbracket___closed__2;
x_85 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_83);
x_86 = l_Lean_Format_sbracket___closed__3;
x_87 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_83);
x_88 = l_Lean_Format_sbracket___closed__1;
x_89 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_format_group(x_89);
return x_90;
}
else
{
lean_object* x_91; 
lean_dec(x_7);
x_91 = l_Lean_Syntax_formatStxAux___main___closed__9;
return x_91;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_nat_dec_lt(x_92, x_9);
lean_dec(x_9);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_94 = l_Array_toList___rarg(x_7);
lean_dec(x_7);
x_95 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6(x_1, x_2, x_3, x_94);
x_96 = lean_box(1);
x_97 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_95, x_96);
lean_dec(x_95);
x_98 = 0;
x_99 = l_Lean_Format_sbracket___closed__2;
x_100 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set_uint8(x_100, sizeof(void*)*2, x_98);
x_101 = l_Lean_Format_sbracket___closed__3;
x_102 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_98);
x_103 = l_Lean_Format_sbracket___closed__1;
x_104 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_format_group(x_104);
return x_105;
}
else
{
lean_object* x_106; 
lean_dec(x_7);
lean_dec(x_1);
x_106 = l_Lean_Syntax_formatStxAux___main___closed__9;
return x_106;
}
}
}
}
}
case 2:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_1);
x_107 = lean_ctor_get(x_4, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_4, 1);
lean_inc(x_108);
lean_dec(x_4);
x_109 = l_String_quote(x_108);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = l___private_Lean_Syntax_6__formatInfo(x_2, x_107, x_110);
return x_111;
}
default: 
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_1);
x_112 = lean_ctor_get(x_4, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_4, 2);
lean_inc(x_113);
lean_dec(x_4);
x_114 = l_System_FilePath_dirName___closed__1;
x_115 = l_Lean_Name_toStringWithSep___main(x_114, x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = 0;
x_118 = l_Lean_formatDataValue___closed__2;
x_119 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_117);
x_120 = l___private_Lean_Syntax_6__formatInfo(x_2, x_112, x_119);
return x_120;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__6(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Syntax_formatStxAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Syntax_formatStxAux___main(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Syntax_formatStxAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Syntax_formatStxAux(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Syntax_formatStx(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux___main(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_formatStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Syntax_formatStx(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_Lean_HasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux___main(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_HasToString___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux___main(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Syntax_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_HasToString___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_HasToString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Syntax_HasToString___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_HasToString___closed__2;
return x_1;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Syntax_structEq___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_Syntax_structEq___main(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
uint8_t l_List_beq___main___at_Lean_Syntax_structEq___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_string_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
uint8_t l_List_beq___main___at_Lean_Syntax_structEq___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_name_eq(x_10, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_List_beq___main___at_Lean_Syntax_structEq___main___spec__3(x_11, x_13);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
}
}
uint8_t l_Lean_Syntax_structEq___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_name_eq(x_5, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_array_get_size(x_8);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_isEqvAux___main___at_Lean_Syntax_structEq___main___spec__1(x_6, x_8, lean_box(0), x_6, x_8, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_string_dec_eq(x_18, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = l_Substring_beq(x_22, x_25);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_name_eq(x_23, x_26);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
uint8_t x_32; 
x_32 = l_List_beq___main___at_Lean_Syntax_structEq___main___spec__2(x_24, x_27);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = 0;
return x_33;
}
}
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Syntax_structEq___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Syntax_structEq___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_List_beq___main___at_Lean_Syntax_structEq___main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___main___at_Lean_Syntax_structEq___main___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_beq___main___at_Lean_Syntax_structEq___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___main___at_Lean_Syntax_structEq___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_structEq___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_structEq___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Syntax_structEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_structEq___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_structEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_structEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_structHasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_structEq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_structHasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_structHasBeq___closed__1;
return x_1;
}
}
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_Traverser_down(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_Syntax_getNumArgs(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_Syntax_getArg(x_3, x_2);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_box(0);
x_15 = l_Lean_Syntax_setArg(x_3, x_2, x_14);
x_16 = lean_array_push(x_13, x_15);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_array_push(x_17, x_2);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
}
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Nat_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Syntax_Traverser_up(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_6);
x_8 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_2);
x_9 = l_Lean_Syntax_getNumArgs(x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
x_11 = lean_array_pop(x_2);
x_12 = lean_array_pop(x_6);
if (x_10 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Syntax_setArg(x_8, x_7, x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_Traverser_left(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_array_get_size(x_2);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = l_Lean_Syntax_Traverser_up(x_1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_Traverser_down(x_6, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Syntax_Traverser_right(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_array_get_size(x_2);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = l_Lean_Syntax_Traverser_up(x_1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_Traverser_down(x_6, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* _init_l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1;
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Syntax_Traverser_setCur(x_2, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_setCur(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Syntax_Traverser_down(x_2, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goDown(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Syntax_Traverser_up(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goUp(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Syntax_Traverser_left(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Syntax_Traverser_right(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goRight___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goRight___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goRight(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_inhabited;
x_5 = lean_array_get(x_4, x_3, x_2);
x_6 = l_Lean_Syntax_getId(x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SyntaxNode_getIdAt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_mk_syntax_atom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SourceInfo_inhabited___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* lean_mk_syntax_list(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_nullKind;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_mkAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SourceInfo_inhabited___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_mkNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_mk_syntax_str_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SourceInfo_inhabited___closed__1;
x_3 = l_Lean_mkStxStrLit(x_1, x_2);
return x_3;
}
}
lean_object* lean_mk_syntax_num_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_SourceInfo_inhabited___closed__1;
x_5 = l_Lean_mkStxLit(x_3, x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Syntax_HasQuote() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasOfNat___closed__1;
return x_1;
}
}
lean_object* l_Lean_String_HasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SourceInfo_inhabited___closed__1;
x_3 = l_Lean_mkStxStrLit(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Nat_HasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_SourceInfo_inhabited___closed__1;
x_5 = l_Lean_mkStxLit(x_3, x_2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Substring_HasQuote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String");
return x_1;
}
}
lean_object* _init_l_Lean_Substring_HasQuote___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Substring_HasQuote___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Substring_HasQuote___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toSubstring");
return x_1;
}
}
lean_object* _init_l_Lean_Substring_HasQuote___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Substring_HasQuote___closed__2;
x_2 = l_Lean_Substring_HasQuote___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Substring_HasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
x_6 = l_Lean_SourceInfo_inhabited___closed__1;
x_7 = l_Lean_mkStxStrLit(x_5, x_6);
x_8 = l_Lean_mkOptionalNode___closed__2;
x_9 = lean_array_push(x_8, x_7);
x_10 = l_Lean_Substring_HasQuote___closed__4;
x_11 = l_Lean_mkCAppStx(x_10, x_9);
return x_11;
}
}
lean_object* l_Lean_Substring_HasQuote___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Substring_HasQuote(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Syntax_7__quoteName___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_7__quoteName___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymous");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_7__quoteName___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkNameStr");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_7__quoteName___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Lean_Syntax_7__quoteName___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_7__quoteName___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkNameNum");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_7__quoteName___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Lean_Syntax_7__quoteName___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_7__quoteName___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lean_mkAppStx___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l___private_Lean_Syntax_7__quoteName___main___closed__1;
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l___private_Lean_Syntax_7__quoteName___main___closed__2;
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_mkCIdentFrom(x_8, x_7);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Syntax_7__quoteName___main(x_10);
x_13 = l_Lean_SourceInfo_inhabited___closed__1;
x_14 = l_Lean_mkStxStrLit(x_11, x_13);
x_15 = l_Lean_mkAppStx___closed__9;
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_array_push(x_16, x_14);
x_18 = l___private_Lean_Syntax_7__quoteName___main___closed__4;
x_19 = l_Lean_mkCAppStx(x_18, x_17);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l___private_Lean_Syntax_7__quoteName___main(x_20);
x_23 = l_Nat_repr(x_21);
x_24 = l_Lean_numLitKind;
x_25 = l_Lean_SourceInfo_inhabited___closed__1;
x_26 = l_Lean_mkStxLit(x_24, x_23, x_25);
x_27 = l_Lean_mkAppStx___closed__9;
x_28 = lean_array_push(x_27, x_22);
x_29 = lean_array_push(x_28, x_26);
x_30 = l___private_Lean_Syntax_7__quoteName___main___closed__6;
x_31 = l_Lean_mkCAppStx(x_30, x_29);
return x_31;
}
}
}
}
lean_object* l___private_Lean_Syntax_7__quoteName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Syntax_7__quoteName___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Name_hasQuote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Syntax_7__quoteName), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Name_hasQuote() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_hasQuote___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Prod_hasQuote___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod");
return x_1;
}
}
lean_object* _init_l_Lean_Prod_hasQuote___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Prod_hasQuote___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Prod_hasQuote___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
lean_object* _init_l_Lean_Prod_hasQuote___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Prod_hasQuote___rarg___closed__2;
x_2 = l_Lean_Prod_hasQuote___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Prod_hasQuote___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_Prod_hasQuote___rarg___closed__4;
x_12 = l_Lean_mkCAppStx(x_11, x_10);
return x_12;
}
}
lean_object* l_Lean_Prod_hasQuote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Prod_hasQuote___rarg), 3, 0);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nil");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2;
x_2 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cons");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2;
x_2 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__5;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l___private_Lean_Syntax_8__quoteList___main___rarg(x_1, x_5);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7;
x_12 = l_Lean_mkCAppStx(x_11, x_10);
return x_12;
}
}
}
lean_object* l___private_Lean_Syntax_8__quoteList___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_8__quoteList___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_8__quoteList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Syntax_8__quoteList___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_8__quoteList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_8__quoteList___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_List_hasQuote___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_8__quoteList___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_List_hasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_List_hasQuote___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Array_hasQuote___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toArray");
return x_1;
}
}
lean_object* _init_l_Lean_Array_hasQuote___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2;
x_2 = l_Lean_Array_hasQuote___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Array_hasQuote___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Array_toList___rarg(x_2);
x_4 = l___private_Lean_Syntax_8__quoteList___main___rarg(x_1, x_3);
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_4);
x_7 = l_Lean_Array_hasQuote___rarg___closed__2;
x_8 = l_Lean_mkCAppStx(x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Array_hasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Array_hasQuote___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Array_hasQuote___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Array_hasQuote___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__2;
x_2 = l_Option_HasRepr___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
x_2 = lean_mk_syntax_ident(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some");
return x_1;
}
}
lean_object* _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__2;
x_2 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Syntax_9__quoteOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__4;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_mkOptionalNode___closed__2;
x_7 = lean_array_push(x_6, x_5);
x_8 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_9 = l_Lean_mkCAppStx(x_8, x_7);
return x_9;
}
}
}
lean_object* l___private_Lean_Syntax_9__quoteOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_9__quoteOption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Option_hasQuote___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_9__quoteOption___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Option_hasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
lean_object* initialize_Lean_Data_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Syntax(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Syntax_isQuot___closed__1 = _init_l_Lean_Syntax_isQuot___closed__1();
lean_mark_persistent(l_Lean_Syntax_isQuot___closed__1);
l_Lean_Syntax_isAntiquot___closed__1 = _init_l_Lean_Syntax_isAntiquot___closed__1();
lean_mark_persistent(l_Lean_Syntax_isAntiquot___closed__1);
l_Lean_Syntax_getAtomVal_x21___closed__1 = _init_l_Lean_Syntax_getAtomVal_x21___closed__1();
lean_mark_persistent(l_Lean_Syntax_getAtomVal_x21___closed__1);
l_Lean_Syntax_getAtomVal_x21___closed__2 = _init_l_Lean_Syntax_getAtomVal_x21___closed__2();
lean_mark_persistent(l_Lean_Syntax_getAtomVal_x21___closed__2);
l_Lean_Syntax_getAtomVal_x21___closed__3 = _init_l_Lean_Syntax_getAtomVal_x21___closed__3();
lean_mark_persistent(l_Lean_Syntax_getAtomVal_x21___closed__3);
l_Lean_Syntax_reprint___main___closed__1 = _init_l_Lean_Syntax_reprint___main___closed__1();
lean_mark_persistent(l_Lean_Syntax_reprint___main___closed__1);
l___private_Lean_Syntax_6__formatInfo___closed__1 = _init_l___private_Lean_Syntax_6__formatInfo___closed__1();
lean_mark_persistent(l___private_Lean_Syntax_6__formatInfo___closed__1);
l_Lean_Syntax_formatStxAux___main___closed__1 = _init_l_Lean_Syntax_formatStxAux___main___closed__1();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__1);
l_Lean_Syntax_formatStxAux___main___closed__2 = _init_l_Lean_Syntax_formatStxAux___main___closed__2();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__2);
l_Lean_Syntax_formatStxAux___main___closed__3 = _init_l_Lean_Syntax_formatStxAux___main___closed__3();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__3);
l_Lean_Syntax_formatStxAux___main___closed__4 = _init_l_Lean_Syntax_formatStxAux___main___closed__4();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__4);
l_Lean_Syntax_formatStxAux___main___closed__5 = _init_l_Lean_Syntax_formatStxAux___main___closed__5();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__5);
l_Lean_Syntax_formatStxAux___main___closed__6 = _init_l_Lean_Syntax_formatStxAux___main___closed__6();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__6);
l_Lean_Syntax_formatStxAux___main___closed__7 = _init_l_Lean_Syntax_formatStxAux___main___closed__7();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__7);
l_Lean_Syntax_formatStxAux___main___closed__8 = _init_l_Lean_Syntax_formatStxAux___main___closed__8();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__8);
l_Lean_Syntax_formatStxAux___main___closed__9 = _init_l_Lean_Syntax_formatStxAux___main___closed__9();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__9);
l_Lean_Syntax_HasToString___closed__1 = _init_l_Lean_Syntax_HasToString___closed__1();
lean_mark_persistent(l_Lean_Syntax_HasToString___closed__1);
l_Lean_Syntax_HasToString___closed__2 = _init_l_Lean_Syntax_HasToString___closed__2();
lean_mark_persistent(l_Lean_Syntax_HasToString___closed__2);
l_Lean_Syntax_HasToString = _init_l_Lean_Syntax_HasToString();
lean_mark_persistent(l_Lean_Syntax_HasToString);
l_Lean_Syntax_structHasBeq___closed__1 = _init_l_Lean_Syntax_structHasBeq___closed__1();
lean_mark_persistent(l_Lean_Syntax_structHasBeq___closed__1);
l_Lean_Syntax_structHasBeq = _init_l_Lean_Syntax_structHasBeq();
lean_mark_persistent(l_Lean_Syntax_structHasBeq);
l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1);
l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1);
l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1);
l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1);
l_Lean_Syntax_HasQuote = _init_l_Lean_Syntax_HasQuote();
lean_mark_persistent(l_Lean_Syntax_HasQuote);
l_Lean_Substring_HasQuote___closed__1 = _init_l_Lean_Substring_HasQuote___closed__1();
lean_mark_persistent(l_Lean_Substring_HasQuote___closed__1);
l_Lean_Substring_HasQuote___closed__2 = _init_l_Lean_Substring_HasQuote___closed__2();
lean_mark_persistent(l_Lean_Substring_HasQuote___closed__2);
l_Lean_Substring_HasQuote___closed__3 = _init_l_Lean_Substring_HasQuote___closed__3();
lean_mark_persistent(l_Lean_Substring_HasQuote___closed__3);
l_Lean_Substring_HasQuote___closed__4 = _init_l_Lean_Substring_HasQuote___closed__4();
lean_mark_persistent(l_Lean_Substring_HasQuote___closed__4);
l___private_Lean_Syntax_7__quoteName___main___closed__1 = _init_l___private_Lean_Syntax_7__quoteName___main___closed__1();
lean_mark_persistent(l___private_Lean_Syntax_7__quoteName___main___closed__1);
l___private_Lean_Syntax_7__quoteName___main___closed__2 = _init_l___private_Lean_Syntax_7__quoteName___main___closed__2();
lean_mark_persistent(l___private_Lean_Syntax_7__quoteName___main___closed__2);
l___private_Lean_Syntax_7__quoteName___main___closed__3 = _init_l___private_Lean_Syntax_7__quoteName___main___closed__3();
lean_mark_persistent(l___private_Lean_Syntax_7__quoteName___main___closed__3);
l___private_Lean_Syntax_7__quoteName___main___closed__4 = _init_l___private_Lean_Syntax_7__quoteName___main___closed__4();
lean_mark_persistent(l___private_Lean_Syntax_7__quoteName___main___closed__4);
l___private_Lean_Syntax_7__quoteName___main___closed__5 = _init_l___private_Lean_Syntax_7__quoteName___main___closed__5();
lean_mark_persistent(l___private_Lean_Syntax_7__quoteName___main___closed__5);
l___private_Lean_Syntax_7__quoteName___main___closed__6 = _init_l___private_Lean_Syntax_7__quoteName___main___closed__6();
lean_mark_persistent(l___private_Lean_Syntax_7__quoteName___main___closed__6);
l_Lean_Name_hasQuote___closed__1 = _init_l_Lean_Name_hasQuote___closed__1();
lean_mark_persistent(l_Lean_Name_hasQuote___closed__1);
l_Lean_Name_hasQuote = _init_l_Lean_Name_hasQuote();
lean_mark_persistent(l_Lean_Name_hasQuote);
l_Lean_Prod_hasQuote___rarg___closed__1 = _init_l_Lean_Prod_hasQuote___rarg___closed__1();
lean_mark_persistent(l_Lean_Prod_hasQuote___rarg___closed__1);
l_Lean_Prod_hasQuote___rarg___closed__2 = _init_l_Lean_Prod_hasQuote___rarg___closed__2();
lean_mark_persistent(l_Lean_Prod_hasQuote___rarg___closed__2);
l_Lean_Prod_hasQuote___rarg___closed__3 = _init_l_Lean_Prod_hasQuote___rarg___closed__3();
lean_mark_persistent(l_Lean_Prod_hasQuote___rarg___closed__3);
l_Lean_Prod_hasQuote___rarg___closed__4 = _init_l_Lean_Prod_hasQuote___rarg___closed__4();
lean_mark_persistent(l_Lean_Prod_hasQuote___rarg___closed__4);
l___private_Lean_Syntax_8__quoteList___main___rarg___closed__1 = _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Syntax_8__quoteList___main___rarg___closed__1);
l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2 = _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Syntax_8__quoteList___main___rarg___closed__2);
l___private_Lean_Syntax_8__quoteList___main___rarg___closed__3 = _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Syntax_8__quoteList___main___rarg___closed__3);
l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4 = _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4);
l___private_Lean_Syntax_8__quoteList___main___rarg___closed__5 = _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Syntax_8__quoteList___main___rarg___closed__5);
l___private_Lean_Syntax_8__quoteList___main___rarg___closed__6 = _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Syntax_8__quoteList___main___rarg___closed__6);
l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7 = _init_l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7);
l_Lean_Array_hasQuote___rarg___closed__1 = _init_l_Lean_Array_hasQuote___rarg___closed__1();
lean_mark_persistent(l_Lean_Array_hasQuote___rarg___closed__1);
l_Lean_Array_hasQuote___rarg___closed__2 = _init_l_Lean_Array_hasQuote___rarg___closed__2();
lean_mark_persistent(l_Lean_Array_hasQuote___rarg___closed__2);
l___private_Lean_Syntax_9__quoteOption___rarg___closed__1 = _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Syntax_9__quoteOption___rarg___closed__1);
l___private_Lean_Syntax_9__quoteOption___rarg___closed__2 = _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Syntax_9__quoteOption___rarg___closed__2);
l___private_Lean_Syntax_9__quoteOption___rarg___closed__3 = _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Syntax_9__quoteOption___rarg___closed__3);
l___private_Lean_Syntax_9__quoteOption___rarg___closed__4 = _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Syntax_9__quoteOption___rarg___closed__4);
l___private_Lean_Syntax_9__quoteOption___rarg___closed__5 = _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Syntax_9__quoteOption___rarg___closed__5);
l___private_Lean_Syntax_9__quoteOption___rarg___closed__6 = _init_l___private_Lean_Syntax_9__quoteOption___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Syntax_9__quoteOption___rarg___closed__6);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

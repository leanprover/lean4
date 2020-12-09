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
extern lean_object* l_instReprOption___rarg___closed__2;
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Syntax_isAntiquot_match__1(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__1(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__5(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object*);
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_SyntaxNode_modifyArgs_match__1(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__3;
extern lean_object* l_String_instInhabitedString;
lean_object* l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
lean_object* l_Lean_Syntax_mkAntiquotNode_match__3___rarg(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotScope(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__12;
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1(lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_reprint___closed__1;
lean_object* l_Lean_Syntax_rewriteBottomUpM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_modifyArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__7;
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg(lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUpM___at_Lean_Syntax_rewriteBottomUp___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs_match__1(lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUpM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNode_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__2;
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object*);
lean_object* l_Lean_Syntax_getAntiquotScopeSuffix(lean_object*);
lean_object* l_Lean_Syntax_isAntiquot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs(lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___closed__7;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isQuot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___boxed(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__16;
lean_object* l_Lean_Syntax_setAtomVal_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__1;
lean_object* l_Lean_Syntax_formatStxAux___closed__8;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_9203____closed__9;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setAtomVal(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM_match__1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__10;
lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___closed__2;
lean_object* l_Lean_Syntax_updateTrailing_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1;
lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
extern lean_object* l_term___x24_______closed__5;
lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object*);
lean_object* l_Array_back_x3f___rarg(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_modifyArgs_match__1(lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos_match__1(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux_match__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_SyntaxNode_getKind(lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs(lean_object*);
lean_object* l_Lean_Syntax_modifyArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotScopeContents___boxed(lean_object*);
lean_object* l_Lean_Syntax_ifNode(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__2(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___closed__3;
lean_object* l_Lean_Syntax_rewriteBottomUpM_match__1(lean_object*);
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_antiquotKind_x3f___closed__1;
lean_object* l_Lean_Syntax_mkAntiquotNode_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__4;
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object*);
lean_object* l_Lean_Syntax_instBEqSyntax;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___at_Lean_Syntax_structEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___closed__5;
lean_object* l_Lean_Syntax_updateTrailing(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_List_beq___at_Lean_Syntax_structEq___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM_match__2(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_structEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getKind_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instToFormatSyntax(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2(size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeMissing(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM(lean_object*);
lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_modifyArg_match__1(lean_object*);
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_structEq_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__14;
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprintLeaf___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux_match__1(lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__7(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSourceInfo___closed__1;
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Syntax_replaceM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__15;
lean_object* l_Lean_Syntax_instBEqSyntax___closed__1;
lean_object* l_Lean_Syntax_isAntiquotSplicePat___boxed(lean_object*);
extern lean_object* l_Lean_formatDataValue___closed__4;
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprintLeaf(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21_match__1(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__5;
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_Lean_Syntax_isMissing___boxed(lean_object*);
lean_object* l_Lean_Syntax_setAtomVal_match__1(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1;
lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object*);
lean_object* l_Lean_Syntax_isMissing_match__1(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Syntax_isAntiquotSplicePat___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isQuot_match__1(lean_object*);
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1___boxed(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Syntax_modifyArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_isAntiquotScope___boxed(lean_object*);
extern lean_object* l_instReprIterator___closed__2;
lean_object* l_Lean_Syntax_formatStxAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_reprint_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Syntax_ifNode___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__17;
lean_object* l_Lean_Syntax_instToStringSyntax;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2___boxed(lean_object*);
lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object*);
lean_object* l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_Syntax_replaceM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_unreachIsNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isMissing_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__1;
lean_object* l_Lean_Syntax_antiquotKind_x3f_match__1(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Syntax_isAntiquotSplicePat___spec__1(lean_object*, size_t, size_t);
lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object*);
lean_object* l_Lean_Syntax_instToStringSyntax___closed__1;
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11225____closed__9;
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__8;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateTrailing_match__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___at_Lean_Syntax_structEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUpM___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Syntax_asNode_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instToStringSyntax___lambda__1(lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__4;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___closed__9;
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs___rarg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSplicePat(lean_object*);
lean_object* l_Lean_Syntax_instToStringSyntax___closed__2;
lean_object* l_Lean_SyntaxNode_modifyArgs_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1;
lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__2(lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_38____closed__4;
lean_object* l_List_beq___at_Lean_Syntax_structEq___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instReprFormat___closed__1;
lean_object* l_Lean_mkSimpleAtom(lean_object*);
lean_object* l_Lean_Syntax_getAntiquotScopeSuffix___boxed(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__3(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_List_beq___at_Lean_Syntax_structEq___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__13;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg___lambda__1(lean_object*);
lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_9203____closed__21;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_ifNode_match__1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object*, lean_object*);
lean_object* l_Lean_mkListNode(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__6;
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg___lambda__1(lean_object*, lean_object*);
uint8_t l_List_beq___at_Lean_Syntax_structEq___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotScopeContents(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1;
lean_object* l_Lean_Syntax_formatStxAux___closed__4;
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Lean_Syntax_antiquotKind_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___closed__6;
extern lean_object* l_stx___x2a___closed__3;
lean_object* l_Lean_Syntax_getAtomVal_x21(lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_SyntaxNode_getKind_match__1(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__3(lean_object*);
lean_object* l_Lean_Syntax_isQuot___boxed(lean_object*);
lean_object* l_Lean_Syntax_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_structEq_match__1(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__11;
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind_match__1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object*);
lean_object* l_Lean_Syntax_reprint_match__1(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f_match__1(lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__6(lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_isMissing_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isMissing_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isMissing_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_SyntaxNode_getKind_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_apply_1(x_3, lean_box(0));
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_2, x_7, x_8, lean_box(0));
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_3(x_4, x_10, x_11, lean_box(0));
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_5(x_5, x_13, x_14, x_15, x_16, lean_box(0));
return x_17;
}
}
}
}
lean_object* l_Lean_SyntaxNode_getKind_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SyntaxNode_getKind_match__1___rarg), 5, 0);
return x_2;
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
lean_object* l_Lean_SyntaxNode_withArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_apply_1(x_3, lean_box(0));
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_2, x_7, x_8, lean_box(0));
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_3(x_4, x_10, x_11, lean_box(0));
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_5(x_5, x_13, x_14, x_15, x_16, lean_box(0));
return x_17;
}
}
}
}
lean_object* l_Lean_SyntaxNode_withArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SyntaxNode_withArgs_match__1___rarg), 5, 0);
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
x_4 = l_Lean_instInhabitedSyntax;
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
lean_object* l_Lean_SyntaxNode_modifyArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_apply_1(x_3, lean_box(0));
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_2, x_7, x_8, lean_box(0));
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_3(x_4, x_10, x_11, lean_box(0));
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_5(x_5, x_13, x_14, x_15, x_16, lean_box(0));
return x_17;
}
}
}
}
lean_object* l_Lean_SyntaxNode_modifyArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SyntaxNode_modifyArgs_match__1___rarg), 5, 0);
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
lean_object* l_Lean_Syntax_getAtomVal_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_getAtomVal_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getAtomVal_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_getAtomVal_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_getAtomVal_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Syntax.getAtomVal!");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_getAtomVal_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getAtomVal!: not an atom");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_getAtomVal_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Syntax_getAtomVal_x21___closed__1;
x_2 = l_Lean_Syntax_getAtomVal_x21___closed__2;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Syntax_getAtomVal_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
x_3 = l_String_instInhabitedString;
x_4 = l_Lean_Syntax_getAtomVal_x21___closed__4;
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
lean_object* l_Lean_Syntax_setAtomVal_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_3, x_5, x_6, x_2);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_2(x_4, x_1, x_2);
return x_8;
}
}
}
lean_object* l_Lean_Syntax_setAtomVal_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setAtomVal_match__1___rarg), 4, 0);
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
lean_object* l_Lean_Syntax_ifNode_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_ifNode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_ifNode_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_ifNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
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
lean_object* l_Lean_Syntax_ifNodeKind_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_ifNodeKind_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_ifNodeKind_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_ifNodeKind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_name_eq(x_6, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_name_eq(x_12, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_apply_1(x_3, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_1(x_4, x_19);
return x_20;
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
lean_object* l_Lean_Syntax_asNode_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_asNode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_asNode_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_asNode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
else
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_mkOptionalNode___closed__1;
return x_6;
}
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
lean_object* l_Lean_Syntax_modifyArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_modifyArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_modifyArgs_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Syntax_modifyArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_modifyArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_modifyArg_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Syntax_replaceM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_replaceM_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_replaceM_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_replaceM_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___rarg), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_array_get_size(x_3);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = x_3;
lean_inc(x_1);
x_12 = l_Array_mapMUnsafe_map___rarg(x_1, x_7, x_9, x_10, x_11);
x_13 = x_12;
x_14 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___rarg___lambda__2), 3, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_16);
return x_19;
}
}
}
lean_object* l_Lean_Syntax_replaceM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
x_7 = lean_apply_1(x_2, x_3);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___rarg___lambda__3), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_3);
x_11 = lean_apply_1(x_2, x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___rarg___lambda__1), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Syntax_replaceM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_rewriteBottomUpM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_rewriteBottomUpM_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_rewriteBottomUpM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Syntax_rewriteBottomUpM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___rarg), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_array_get_size(x_5);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = x_5;
x_12 = l_Array_mapMUnsafe_map___rarg(x_1, x_7, x_9, x_10, x_11);
x_13 = x_12;
x_14 = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___rarg___lambda__1), 3, 2);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_2);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_apply_1(x_2, x_3);
return x_16;
}
}
}
lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Syntax_rewriteBottomUpM___at_Lean_Syntax_rewriteBottomUp___spec__1(x_1, x_10);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_rewriteBottomUpM___at_Lean_Syntax_rewriteBottomUp___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = x_4;
lean_inc(x_1);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2(x_1, x_6, x_7, x_8);
x_10 = x_9;
lean_ctor_set(x_2, 1, x_10);
x_11 = lean_apply_1(x_1, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = x_13;
lean_inc(x_1);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2(x_1, x_15, x_16, x_17);
x_19 = x_18;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_apply_1(x_1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = lean_apply_1(x_1, x_2);
return x_22;
}
}
}
lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_rewriteBottomUpM___at_Lean_Syntax_rewriteBottomUp___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_apply_5(x_4, x_12, x_13, x_14, x_2, x_3);
return x_15;
}
}
}
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_0__Lean_Syntax_updateInfo_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_6, 0, x_14);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 2);
lean_dec(x_19);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set(x_1, 2, x_4);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_4, 0, x_22);
lean_ctor_set(x_1, 2, x_4);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_29 = x_23;
} else {
 lean_dec_ref(x_23);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 3, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_4, 0, x_30);
lean_ctor_set(x_1, 2, x_4);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 3, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_36, 2, x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 3, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_3);
lean_ctor_set(x_4, 0, x_41);
lean_ctor_set(x_1, 2, x_4);
lean_ctor_set(x_1, 0, x_37);
return x_1;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_ctor_get(x_6, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_45 = x_6;
} else {
 lean_dec_ref(x_6);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 2);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 3, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_47);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_43);
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_54 = x_44;
} else {
 lean_dec_ref(x_44);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 3, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_3);
lean_ctor_set(x_4, 0, x_55);
lean_ctor_set(x_1, 2, x_4);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_50);
return x_1;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_56 = lean_ctor_get(x_4, 0);
lean_inc(x_56);
lean_dec(x_4);
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_58 = x_5;
} else {
 lean_dec_ref(x_5);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_6, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_60 = x_6;
} else {
 lean_dec_ref(x_6);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 2);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 3, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_2);
lean_ctor_set(x_64, 2, x_62);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_60;
}
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_58)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_58;
}
lean_ctor_set(x_66, 0, x_57);
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_69 = x_59;
} else {
 lean_dec_ref(x_59);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_3);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_1, 2, x_71);
lean_ctor_set(x_1, 1, x_66);
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_4, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_73 = x_4;
} else {
 lean_dec_ref(x_4);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_5, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_75 = x_5;
} else {
 lean_dec_ref(x_5);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_6, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_77 = x_6;
} else {
 lean_dec_ref(x_6);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 2);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 3, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_79);
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_74);
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 x_86 = x_76;
} else {
 lean_dec_ref(x_76);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 3, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_3);
if (lean_is_scalar(x_73)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_73;
}
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set(x_89, 1, x_83);
lean_ctor_set(x_89, 2, x_88);
return x_89;
}
}
}
}
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = 10;
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_5);
x_7 = l_String_posOfAux(x_4, x_3, x_6, x_5);
lean_dec(x_6);
lean_dec(x_4);
x_8 = lean_nat_sub(x_7, x_5);
lean_dec(x_5);
lean_dec(x_7);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_apply_1(x_4, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_apply_5(x_2, x_5, x_11, x_8, x_9, x_10);
return x_12;
}
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_3);
x_15 = lean_apply_1(x_4, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_apply_7(x_3, x_13, x_21, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
default: 
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_apply_1(x_4, x_1);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* x_1, lean_object* x_2) {
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
x_11 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_10);
lean_inc(x_11);
x_12 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_3, x_2, x_11);
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
x_15 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_14);
lean_inc(x_15);
x_16 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_3, x_2, x_15);
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
x_22 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_20);
lean_inc(x_22);
x_23 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_3, x_2, x_22);
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
x_35 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_34);
lean_inc(x_35);
x_36 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_27, x_2, x_35);
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
x_39 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_38);
lean_inc(x_39);
x_40 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_27, x_2, x_39);
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
x_48 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_46);
lean_inc(x_48);
x_49 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_27, x_2, x_48);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 < x_1;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = x_3;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_11 = x_8;
x_12 = l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1(x_11, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = x_2 + x_15;
x_17 = x_13;
x_18 = lean_array_uset(x_10, x_2, x_17);
x_2 = x_16;
x_3 = x_18;
x_4 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_3 = x_17;
goto block_15;
}
case 1:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_array_get_size(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = x_19;
x_23 = lean_box_usize(x_21);
x_24 = l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1;
x_25 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2___boxed), 4, 3);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_22);
x_26 = x_25;
x_27 = lean_apply_1(x_26, x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_1, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_1);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = x_34;
x_38 = lean_box_usize(x_36);
x_39 = l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1;
x_40 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2___boxed), 4, 3);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
lean_closure_set(x_40, 2, x_37);
x_41 = x_40;
x_42 = lean_apply_1(x_41, x_2);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
case 2:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_2);
x_3 = x_51;
goto block_15;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_54);
lean_inc(x_55);
x_56 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_48, x_2, x_55);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_49, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_55);
x_3 = x_58;
goto block_15;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_59);
lean_inc(x_60);
x_61 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_48, x_2, x_60);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
x_3 = x_64;
goto block_15;
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 2);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_2);
x_3 = x_68;
goto block_15;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 3);
lean_inc(x_71);
x_72 = !lean_is_exclusive(x_66);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_66, 0);
x_74 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_73);
lean_inc(x_74);
x_75 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_65, x_2, x_74);
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_70);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_66, 0, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_74);
x_3 = x_77;
goto block_15;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
lean_dec(x_66);
x_79 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_78);
lean_inc(x_79);
x_80 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_65, x_2, x_79);
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_69);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_71);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
x_3 = x_83;
goto block_15;
}
}
}
}
block_15:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
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
x_3 = l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Syntax_updateTrailing_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_3(x_4, x_1, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_4(x_3, x_13, x_14, x_15, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Syntax_updateTrailing_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_updateTrailing_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_updateTrailing(lean_object* x_1, lean_object* x_2) {
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
x_13 = l_Lean_instInhabitedSyntax;
x_14 = lean_array_get(x_13, x_4, x_12);
x_15 = l_Lean_Syntax_updateTrailing(x_1, x_14);
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
x_19 = l_Lean_instInhabitedSyntax;
x_20 = lean_array_get(x_19, x_4, x_18);
x_21 = l_Lean_Syntax_updateTrailing(x_1, x_20);
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
lean_object* l_Lean_Syntax_getTailWithPos_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_2);
x_12 = lean_apply_1(x_5, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_apply_5(x_2, x_1, x_16, x_13, x_14, x_15);
return x_17;
}
}
default: 
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_3);
x_20 = lean_apply_1(x_5, x_1);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_apply_7(x_3, x_1, x_26, x_21, x_22, x_23, x_24, x_25);
return x_27;
}
}
}
}
}
lean_object* l_Lean_Syntax_getTailWithPos_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getTailWithPos_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Lean_Syntax_getTailWithPos(x_8);
if (lean_obj_tag(x_9) == 0)
{
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_7);
return x_9;
}
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
lean_object* l_Lean_Syntax_getTailWithPos(lean_object* x_1) {
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
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1(x_3, x_4, lean_box(0));
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
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprintLeaf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_instReprIterator___closed__2;
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
x_21 = l_instReprIterator___closed__2;
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
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprintLeaf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Syntax_0__Lean_Syntax_reprintLeaf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_reprint_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_4(x_3, x_13, x_14, x_15, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Syntax_reprint_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_reprint_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Syntax_reprint(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_string_append(x_4, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_2 = x_12;
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Syntax_reprint(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_string_dec_eq(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_box(0);
return x_11;
}
else
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = x_2 + x_12;
x_2 = x_13;
goto _start;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Syntax_reprint___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_reprint(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_choiceKind;
x_6 = lean_name_eq(x_3, x_5);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
x_10 = l_Lean_Syntax_reprint___closed__1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_4);
x_12 = l_Lean_Syntax_reprint___closed__1;
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Lean_instInhabitedParserDescr___closed__1;
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__1(x_4, x_13, x_14, x_15);
lean_dec(x_4);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_array_get_size(x_4);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_instInhabitedSyntax;
x_21 = lean_array_get(x_20, x_4, x_18);
x_22 = l_Lean_Syntax_reprint(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_array_get_size(x_4);
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Array_toSubarray___rarg(x_4, x_27, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_22;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_get_size(x_29);
x_34 = lean_nat_dec_le(x_31, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_22;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
lean_free_object(x_22);
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_37 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__2(x_29, x_35, x_36, x_25);
lean_dec(x_29);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_22, 0);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_array_get_size(x_4);
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Array_toSubarray___rarg(x_4, x_40, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_38);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_array_get_size(x_42);
x_48 = lean_nat_dec_le(x_44, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_38);
return x_49;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_51 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_52 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__2(x_42, x_50, x_51, x_38);
lean_dec(x_42);
return x_52;
}
}
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_4);
x_53 = lean_box(0);
return x_53;
}
}
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_56 = l___private_Lean_Syntax_0__Lean_Syntax_reprintLeaf(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
default: 
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_string_utf8_extract(x_60, x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_64 = l___private_Lean_Syntax_0__Lean_Syntax_reprintLeaf(x_59, x_63);
lean_dec(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_reprint___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Syntax_0__Lean_Syntax_formatInfo_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_46; 
x_46 = l_Lean_instInhabitedParserDescr___closed__1;
x_7 = x_46;
goto block_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_4, 0);
lean_inc(x_47);
lean_dec(x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 2);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_string_utf8_extract(x_48, x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_52 = l_String_quote(x_51);
lean_dec(x_51);
x_53 = l_myMacro____x40_Init_Notation___hyg_11225____closed__9;
x_54 = lean_string_append(x_52, x_53);
x_7 = x_54;
goto block_45;
}
block_45:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Format_join___closed__1;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_string_utf8_extract(x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_18 = l_String_quote(x_17);
lean_dec(x_17);
x_19 = l_myMacro____x40_Init_Notation___hyg_11225____closed__9;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = l_Nat_repr(x_23);
x_25 = l_addParenHeuristic(x_24);
lean_dec(x_24);
x_26 = l_instReprOption___rarg___closed__2;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_myMacro____x40_Init_Notation___hyg_9203____closed__21;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_myMacro____x40_Init_Notation___hyg_11225____closed__9;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_32);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Format_join___closed__1;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 2);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_string_utf8_extract(x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_41 = l_String_quote(x_40);
lean_dec(x_40);
x_42 = lean_string_append(x_30, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_formatInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Syntax_0__Lean_Syntax_formatInfo(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_formatStxAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_apply_1(x_5, x_1);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_3(x_6, x_1, x_8, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_3(x_3, x_1, x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_5(x_4, x_1, x_14, x_15, x_16, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Syntax_formatStxAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_formatStxAux_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
x_11 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___at_Lean_Syntax_formatStxAux___spec__1(x_1, x_2, x_3, x_8);
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
x_17 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___at_Lean_Syntax_formatStxAux___spec__1(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_4, x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
x_11 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___at_Lean_Syntax_formatStxAux___spec__3(x_1, x_2, x_3, x_8);
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
x_17 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___at_Lean_Syntax_formatStxAux___spec__3(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
x_11 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___at_Lean_Syntax_formatStxAux___spec__4(x_1, x_2, x_3, x_8);
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
x_17 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___at_Lean_Syntax_formatStxAux___spec__4(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
x_11 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___at_Lean_Syntax_formatStxAux___spec__5(x_1, x_2, x_3, x_8);
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
x_17 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___at_Lean_Syntax_formatStxAux___spec__5(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
x_11 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___at_Lean_Syntax_formatStxAux___spec__6(x_1, x_2, x_3, x_8);
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
x_17 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___at_Lean_Syntax_formatStxAux___spec__6(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
x_11 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_10, x_7);
lean_dec(x_10);
x_12 = l_List_map___at_Lean_Syntax_formatStxAux___spec__7(x_1, x_2, x_3, x_8);
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
x_17 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_16, x_13);
lean_dec(x_16);
x_18 = l_List_map___at_Lean_Syntax_formatStxAux___spec__7(x_1, x_2, x_3, x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<missing>");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("..");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_formatStxAux___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_sbracket___closed__3;
x_2 = l_Lean_Syntax_formatStxAux___closed__4;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_formatStxAux___closed__6;
x_2 = l_Lean_Format_sbracket___closed__4;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_sbracket___closed__2;
x_2 = l_Lean_Syntax_formatStxAux___closed__7;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__9() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_formatStxAux___closed__8;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_formatStxAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_formatStxAux___closed__2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = l_myMacro____x40_Init_Notation___hyg_38____closed__4;
x_13 = lean_box(0);
x_14 = l_Lean_Name_replacePrefix(x_6, x_12, x_13);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_14);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_array_get_size(x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_9);
x_21 = lean_array_to_list(lean_box(0), x_7);
x_22 = l_List_map___at_Lean_Syntax_formatStxAux___spec__1(x_1, x_2, x_3, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(1);
x_25 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_23, x_24);
lean_dec(x_23);
x_26 = l_Lean_Format_paren___closed__3;
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Format_paren___closed__4;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Format_paren___closed__2;
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = 0;
x_33 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
return x_33;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_34; 
x_34 = lean_nat_dec_lt(x_9, x_9);
lean_dec(x_9);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_35 = lean_array_to_list(lean_box(0), x_7);
x_36 = l_List_map___at_Lean_Syntax_formatStxAux___spec__3(x_1, x_2, x_3, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(1);
x_39 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_37, x_38);
lean_dec(x_37);
x_40 = l_Lean_Format_paren___closed__3;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Format_paren___closed__4;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Format_paren___closed__2;
x_45 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = 0;
x_47 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
lean_dec(x_7);
x_48 = l_Lean_Syntax_formatStxAux___closed__5;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_box(1);
x_51 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_49, x_50);
lean_dec(x_49);
x_52 = l_Lean_Format_paren___closed__3;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Format_paren___closed__4;
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Format_paren___closed__2;
x_57 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = 0;
x_59 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_nat_dec_lt(x_60, x_9);
lean_dec(x_9);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_62 = lean_array_to_list(lean_box(0), x_7);
x_63 = l_List_map___at_Lean_Syntax_formatStxAux___spec__4(x_1, x_2, x_3, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_17);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_box(1);
x_66 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_64, x_65);
lean_dec(x_64);
x_67 = l_Lean_Format_paren___closed__3;
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Format_paren___closed__4;
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Format_paren___closed__2;
x_72 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = 0;
x_74 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
lean_dec(x_7);
x_75 = l_Lean_Syntax_formatStxAux___closed__5;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_17);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_box(1);
x_78 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_76, x_77);
lean_dec(x_76);
x_79 = l_Lean_Format_paren___closed__3;
x_80 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Format_paren___closed__4;
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Format_paren___closed__2;
x_84 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = 0;
x_86 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_6);
x_87 = lean_array_get_size(x_7);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_nat_dec_lt(x_88, x_87);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
lean_dec(x_9);
x_90 = lean_array_to_list(lean_box(0), x_7);
x_91 = l_List_map___at_Lean_Syntax_formatStxAux___spec__5(x_1, x_2, x_3, x_90);
x_92 = lean_box(1);
x_93 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_91, x_92);
lean_dec(x_91);
x_94 = l_Lean_Format_sbracket___closed__3;
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Format_sbracket___closed__4;
x_97 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Format_sbracket___closed__2;
x_99 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = 0;
x_101 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
return x_101;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_102; 
x_102 = lean_nat_dec_lt(x_9, x_9);
lean_dec(x_9);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_103 = lean_array_to_list(lean_box(0), x_7);
x_104 = l_List_map___at_Lean_Syntax_formatStxAux___spec__6(x_1, x_2, x_3, x_103);
x_105 = lean_box(1);
x_106 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_104, x_105);
lean_dec(x_104);
x_107 = l_Lean_Format_sbracket___closed__3;
x_108 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Format_sbracket___closed__4;
x_110 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Format_sbracket___closed__2;
x_112 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = 0;
x_114 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_7);
x_115 = l_Lean_Syntax_formatStxAux___closed__9;
return x_115;
}
}
else
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_1, 0);
x_117 = lean_nat_dec_lt(x_116, x_9);
lean_dec(x_9);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_118 = lean_array_to_list(lean_box(0), x_7);
x_119 = l_List_map___at_Lean_Syntax_formatStxAux___spec__7(x_1, x_2, x_3, x_118);
x_120 = lean_box(1);
x_121 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_119, x_120);
lean_dec(x_119);
x_122 = l_Lean_Format_sbracket___closed__3;
x_123 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Format_sbracket___closed__4;
x_125 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Format_sbracket___closed__2;
x_127 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = 0;
x_129 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_128);
return x_129;
}
else
{
lean_object* x_130; 
lean_dec(x_7);
x_130 = l_Lean_Syntax_formatStxAux___closed__9;
return x_130;
}
}
}
}
}
case 2:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_4, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_4, 1);
lean_inc(x_132);
lean_dec(x_4);
x_133 = l_String_quote(x_132);
lean_dec(x_132);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = l___private_Lean_Syntax_0__Lean_Syntax_formatInfo(x_2, x_131, x_134);
return x_135;
}
default: 
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_4, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_4, 2);
lean_inc(x_137);
lean_dec(x_4);
x_138 = l_Lean_Name_toString___closed__1;
x_139 = l_Lean_Name_toStringWithSep(x_138, x_137);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Lean_formatDataValue___closed__4;
x_142 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l___private_Lean_Syntax_0__Lean_Syntax_formatInfo(x_2, x_136, x_142);
return x_143;
}
}
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___at_Lean_Syntax_formatStxAux___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___at_Lean_Syntax_formatStxAux___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___at_Lean_Syntax_formatStxAux___spec__3(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___at_Lean_Syntax_formatStxAux___spec__4(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___at_Lean_Syntax_formatStxAux___spec__5(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___at_Lean_Syntax_formatStxAux___spec__6(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_map___at_Lean_Syntax_formatStxAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___at_Lean_Syntax_formatStxAux___spec__7(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
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
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Syntax_formatStx(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux(x_2, x_3, x_4, x_1);
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
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Syntax_instToFormatSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_instToStringSyntax___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Syntax_instToStringSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instToStringSyntax___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instToStringSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instReprFormat___closed__1;
x_2 = l_Lean_Syntax_instToStringSyntax___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instToStringSyntax() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_instToStringSyntax___closed__2;
return x_1;
}
}
lean_object* l_Lean_Syntax_structEq_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_7, x_1, x_2);
return x_10;
}
}
case 1:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_4(x_4, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_apply_2(x_7, x_1, x_2);
return x_16;
}
}
case 2:
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_4(x_5, x_17, x_18, x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_5);
x_22 = lean_apply_2(x_7, x_1, x_2);
return x_22;
}
}
default: 
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_apply_8(x_6, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_6);
x_32 = lean_apply_2(x_7, x_1, x_2);
return x_32;
}
}
}
}
}
lean_object* l_Lean_Syntax_structEq_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_structEq_match__1___rarg), 7, 0);
return x_2;
}
}
uint8_t l_Array_isEqvAux___at_Lean_Syntax_structEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_Syntax_structEq(x_10, x_11);
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
uint8_t l_List_beq___at_Lean_Syntax_structEq___spec__3(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_List_beq___at_Lean_Syntax_structEq___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_16 = l_List_beq___at_Lean_Syntax_structEq___spec__3(x_11, x_13);
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
uint8_t l_Lean_Syntax_structEq(lean_object* x_1, lean_object* x_2) {
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
x_16 = l_Array_isEqvAux___at_Lean_Syntax_structEq___spec__1(x_6, x_8, lean_box(0), x_6, x_8, x_15);
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
x_32 = l_List_beq___at_Lean_Syntax_structEq___spec__2(x_24, x_27);
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
lean_object* l_Array_isEqvAux___at_Lean_Syntax_structEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_Syntax_structEq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_List_beq___at_Lean_Syntax_structEq___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at_Lean_Syntax_structEq___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_beq___at_Lean_Syntax_structEq___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at_Lean_Syntax_structEq___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
static lean_object* _init_l_Lean_Syntax_instBEqSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_structEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instBEqSyntax() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_instBEqSyntax___closed__1;
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
x_5 = l_instInhabitedNat;
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
x_5 = l_Lean_instInhabitedSyntax;
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
static lean_object* _init_l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1() {
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
lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___rarg), 2, 0);
return x_2;
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
lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___rarg), 2, 0);
return x_2;
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
static lean_object* _init_l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1() {
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
lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___rarg), 1, 0);
return x_2;
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
static lean_object* _init_l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1() {
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
lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___rarg), 1, 0);
return x_2;
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
static lean_object* _init_l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1() {
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
lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goRight___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Array_back_x3f___rarg(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_2(x_4, lean_box(0), x_9);
return x_10;
}
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
x_4 = l_Lean_instInhabitedSyntax;
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
lean_object* l_Lean_mkSimpleAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedSourceInfo___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_mkListNode(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Syntax_isQuot_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quot");
return x_1;
}
}
lean_object* l_Lean_Syntax_isQuot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_usize(x_4, 2);
lean_dec(x_4);
x_9 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_10 = lean_string_dec_eq(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box_usize(x_8);
x_13 = lean_apply_3(x_2, x_6, x_12, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_apply_1(x_3, x_1);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_isQuot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isQuot_match__1___rarg), 3, 0);
return x_2;
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
x_4 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
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
static lean_object* _init_l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot");
return x_1;
}
}
lean_object* l_Lean_Syntax_isAntiquot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_usize(x_4, 2);
lean_dec(x_4);
x_9 = l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1;
x_10 = lean_string_dec_eq(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box_usize(x_8);
x_13 = lean_apply_3(x_2, x_6, x_12, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_apply_1(x_3, x_1);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_isAntiquot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isAntiquot_match__1___rarg), 3, 0);
return x_2;
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
x_4 = l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1;
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
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isAntiquot(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
}
lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAntiquotSplice(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mkAntiquotNode_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Syntax_mkAntiquotNode_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mkAntiquotNode_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__3___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mkAntiquotNode_match__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode_match__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Syntax_mkAntiquotNode_match__3___rarg(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term___x24_______closed__5;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkAntiquotNode___closed__3;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_stx___x2a___closed__3;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquotName");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_11225____closed__9;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkApp___closed__1;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquotNestedExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_9203____closed__9;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_9203____closed__21;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkAntiquotNode___closed__16;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = l_Lean_Syntax_mkAntiquotNode___closed__1;
x_7 = lean_mk_array(x_2, x_6);
x_8 = l_Lean_nullKind;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Syntax_isIdent(x_1);
x_11 = l_Lean_Syntax_mkAntiquotNode___closed__2;
x_12 = l_Lean_Name_append(x_4, x_11);
x_13 = l_Lean_Syntax_mkAntiquotNode___closed__4;
x_14 = lean_array_push(x_13, x_9);
if (x_10 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = l_Lean_Syntax_mkAntiquotNode___closed__17;
x_39 = lean_array_push(x_38, x_1);
x_40 = l_Lean_Syntax_mkAntiquotNode___closed__15;
x_41 = lean_array_push(x_39, x_40);
x_42 = l_Lean_Syntax_mkAntiquotNode___closed__13;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_15 = x_43;
goto block_37;
}
else
{
x_15 = x_1;
goto block_37;
}
block_37:
{
lean_object* x_16; 
x_16 = lean_array_push(x_14, x_15);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_mkOptionalNode___closed__1;
x_18 = lean_array_push(x_16, x_17);
if (x_5 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Syntax_mkAntiquotNode___closed__7;
x_22 = lean_array_push(x_18, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = l_Lean_mkAtom(x_24);
x_26 = l_Lean_Syntax_mkAntiquotNode___closed__11;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_Syntax_mkAntiquotNode___closed__9;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_16, x_29);
if (x_5 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_mkOptionalNode___closed__1;
x_32 = lean_array_push(x_30, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_Syntax_mkAntiquotNode___closed__7;
x_35 = lean_array_push(x_30, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Syntax_mkAntiquotNode(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = l_Array_isEmpty___rarg(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isEscapedAntiquot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isAntiquot(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = lean_array_pop(x_5);
x_7 = l_Lean_nullKind;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Syntax_setArg(x_1, x_3, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isIdent(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_3, x_5);
lean_dec(x_3);
return x_6;
}
else
{
return x_3;
}
}
}
lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getAntiquotTerm(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_antiquotKind_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_usize(x_4, 2);
lean_dec(x_4);
x_9 = l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1;
x_10 = lean_string_dec_eq(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box_usize(x_8);
x_13 = lean_apply_3(x_2, x_6, x_12, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_apply_1(x_3, x_1);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_antiquotKind_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_antiquotKind_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_antiquotKind_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_instInhabitedSyntax;
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_array_get(x_9, x_3, x_10);
x_12 = l_Lean_Syntax_mkAntiquotNode___closed__9;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Syntax_antiquotKind_x3f___closed__1;
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
}
}
lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_antiquotKind_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot_scope");
return x_1;
}
}
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_usize(x_4, 2);
lean_dec(x_4);
x_9 = l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg___closed__1;
x_10 = lean_string_dec_eq(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box_usize(x_8);
x_13 = lean_apply_3(x_2, x_6, x_12, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_apply_1(x_3, x_1);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
}
}
lean_object* l_Lean_Syntax_antiquotScopeKind_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_antiquotScopeKind_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Syntax_isAntiquotScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_antiquotScopeKind_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 1;
return x_4;
}
}
}
lean_object* l_Lean_Syntax_isAntiquotScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAntiquotScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getAntiquotScopeContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getAntiquotScopeContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getAntiquotScopeContents(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getAntiquotScopeSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getAntiquotScopeSuffix___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getAntiquotScopeSuffix(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Syntax_isAntiquotSplicePat___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Syntax_isAntiquotSplice(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
lean_dec(x_5);
x_7 = 1;
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_Syntax_isEscapedAntiquot(x_5);
lean_dec(x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = x_2 + x_12;
x_2 = x_13;
goto _start;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
uint8_t l_Lean_Syntax_isAntiquotSplicePat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_nullKind;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Syntax_isAntiquotSplicePat___spec__1(x_5, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Syntax_isAntiquotSplicePat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Syntax_isAntiquotSplicePat___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Syntax_isAntiquotSplicePat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAntiquotSplicePat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
lean_object* initialize_Lean_Data_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Syntax(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Lean_Syntax_getAtomVal_x21___closed__1 = _init_l_Lean_Syntax_getAtomVal_x21___closed__1();
lean_mark_persistent(l_Lean_Syntax_getAtomVal_x21___closed__1);
l_Lean_Syntax_getAtomVal_x21___closed__2 = _init_l_Lean_Syntax_getAtomVal_x21___closed__2();
lean_mark_persistent(l_Lean_Syntax_getAtomVal_x21___closed__2);
l_Lean_Syntax_getAtomVal_x21___closed__3 = _init_l_Lean_Syntax_getAtomVal_x21___closed__3();
lean_mark_persistent(l_Lean_Syntax_getAtomVal_x21___closed__3);
l_Lean_Syntax_getAtomVal_x21___closed__4 = _init_l_Lean_Syntax_getAtomVal_x21___closed__4();
lean_mark_persistent(l_Lean_Syntax_getAtomVal_x21___closed__4);
l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1 = _init_l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1();
lean_mark_persistent(l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1);
l_Lean_Syntax_reprint___closed__1 = _init_l_Lean_Syntax_reprint___closed__1();
lean_mark_persistent(l_Lean_Syntax_reprint___closed__1);
l_Lean_Syntax_formatStxAux___closed__1 = _init_l_Lean_Syntax_formatStxAux___closed__1();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__1);
l_Lean_Syntax_formatStxAux___closed__2 = _init_l_Lean_Syntax_formatStxAux___closed__2();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__2);
l_Lean_Syntax_formatStxAux___closed__3 = _init_l_Lean_Syntax_formatStxAux___closed__3();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__3);
l_Lean_Syntax_formatStxAux___closed__4 = _init_l_Lean_Syntax_formatStxAux___closed__4();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__4);
l_Lean_Syntax_formatStxAux___closed__5 = _init_l_Lean_Syntax_formatStxAux___closed__5();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__5);
l_Lean_Syntax_formatStxAux___closed__6 = _init_l_Lean_Syntax_formatStxAux___closed__6();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__6);
l_Lean_Syntax_formatStxAux___closed__7 = _init_l_Lean_Syntax_formatStxAux___closed__7();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__7);
l_Lean_Syntax_formatStxAux___closed__8 = _init_l_Lean_Syntax_formatStxAux___closed__8();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__8);
l_Lean_Syntax_formatStxAux___closed__9 = _init_l_Lean_Syntax_formatStxAux___closed__9();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___closed__9);
l_Lean_Syntax_instToStringSyntax___closed__1 = _init_l_Lean_Syntax_instToStringSyntax___closed__1();
lean_mark_persistent(l_Lean_Syntax_instToStringSyntax___closed__1);
l_Lean_Syntax_instToStringSyntax___closed__2 = _init_l_Lean_Syntax_instToStringSyntax___closed__2();
lean_mark_persistent(l_Lean_Syntax_instToStringSyntax___closed__2);
l_Lean_Syntax_instToStringSyntax = _init_l_Lean_Syntax_instToStringSyntax();
lean_mark_persistent(l_Lean_Syntax_instToStringSyntax);
l_Lean_Syntax_instBEqSyntax___closed__1 = _init_l_Lean_Syntax_instBEqSyntax___closed__1();
lean_mark_persistent(l_Lean_Syntax_instBEqSyntax___closed__1);
l_Lean_Syntax_instBEqSyntax = _init_l_Lean_Syntax_instBEqSyntax();
lean_mark_persistent(l_Lean_Syntax_instBEqSyntax);
l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1);
l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1);
l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1);
l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1 = _init_l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1);
l_Lean_Syntax_isQuot_match__1___rarg___closed__1 = _init_l_Lean_Syntax_isQuot_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_isQuot_match__1___rarg___closed__1);
l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1 = _init_l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1);
l_Lean_Syntax_mkAntiquotNode___closed__1 = _init_l_Lean_Syntax_mkAntiquotNode___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__1);
l_Lean_Syntax_mkAntiquotNode___closed__2 = _init_l_Lean_Syntax_mkAntiquotNode___closed__2();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__2);
l_Lean_Syntax_mkAntiquotNode___closed__3 = _init_l_Lean_Syntax_mkAntiquotNode___closed__3();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__3);
l_Lean_Syntax_mkAntiquotNode___closed__4 = _init_l_Lean_Syntax_mkAntiquotNode___closed__4();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__4);
l_Lean_Syntax_mkAntiquotNode___closed__5 = _init_l_Lean_Syntax_mkAntiquotNode___closed__5();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__5);
l_Lean_Syntax_mkAntiquotNode___closed__6 = _init_l_Lean_Syntax_mkAntiquotNode___closed__6();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__6);
l_Lean_Syntax_mkAntiquotNode___closed__7 = _init_l_Lean_Syntax_mkAntiquotNode___closed__7();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__7);
l_Lean_Syntax_mkAntiquotNode___closed__8 = _init_l_Lean_Syntax_mkAntiquotNode___closed__8();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__8);
l_Lean_Syntax_mkAntiquotNode___closed__9 = _init_l_Lean_Syntax_mkAntiquotNode___closed__9();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__9);
l_Lean_Syntax_mkAntiquotNode___closed__10 = _init_l_Lean_Syntax_mkAntiquotNode___closed__10();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__10);
l_Lean_Syntax_mkAntiquotNode___closed__11 = _init_l_Lean_Syntax_mkAntiquotNode___closed__11();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__11);
l_Lean_Syntax_mkAntiquotNode___closed__12 = _init_l_Lean_Syntax_mkAntiquotNode___closed__12();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__12);
l_Lean_Syntax_mkAntiquotNode___closed__13 = _init_l_Lean_Syntax_mkAntiquotNode___closed__13();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__13);
l_Lean_Syntax_mkAntiquotNode___closed__14 = _init_l_Lean_Syntax_mkAntiquotNode___closed__14();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__14);
l_Lean_Syntax_mkAntiquotNode___closed__15 = _init_l_Lean_Syntax_mkAntiquotNode___closed__15();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__15);
l_Lean_Syntax_mkAntiquotNode___closed__16 = _init_l_Lean_Syntax_mkAntiquotNode___closed__16();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__16);
l_Lean_Syntax_mkAntiquotNode___closed__17 = _init_l_Lean_Syntax_mkAntiquotNode___closed__17();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotNode___closed__17);
l_Lean_Syntax_antiquotKind_x3f___closed__1 = _init_l_Lean_Syntax_antiquotKind_x3f___closed__1();
lean_mark_persistent(l_Lean_Syntax_antiquotKind_x3f___closed__1);
l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg___closed__1 = _init_l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_antiquotScopeKind_x3f_match__1___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

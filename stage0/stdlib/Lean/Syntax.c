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
lean_object* l_Lean_Syntax_getQuotContent___closed__1;
lean_object* l_Lean_Syntax_isAntiquot_match__1(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__4;
lean_object* l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__3;
extern lean_object* l_String_instInhabitedString;
lean_object* l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__12;
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object*);
extern lean_object* l_term_x5b___x5d___closed__9;
lean_object* l_Lean_Syntax_rewriteBottomUpM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_modifyArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__1;
lean_object* l_Lean_Syntax_ifNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1;
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__7;
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__5(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg(lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUpM___at_Lean_Syntax_rewriteBottomUp___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs_match__1(lean_object*);
lean_object* l_Lean_Syntax_ifNode_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__2;
lean_object* l_Lean_Syntax_isAntiquot_match__1___rarg___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object*);
lean_object* l_Lean_Syntax_isAntiquot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isQuot_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___boxed(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setAtomVal_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__1;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setAtomVal(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM_match__1(lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing_match__1(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__10;
lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object*);
lean_object* l_Lean_Syntax_updateTrailing_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___closed__1;
lean_object* l_Std_RBMap_instForInRBMapProd___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__2;
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
extern lean_object* l_term___x24_______closed__5;
lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object*);
lean_object* l_Lean_Syntax_reprint_reprintLeaf___boxed(lean_object*, lean_object*);
lean_object* l_Array_back_x3f___rarg(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos_match__1(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux_match__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1;
lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getKind(lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs(lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNode(lean_object*);
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_antiquotKind_x3f___closed__1;
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__4;
lean_object* l_Lean_Syntax_getAtomVal_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__2(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateTrailing(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM_match__2(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__3;
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getKind_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_updateLeading___spec__2(size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeMissing(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM(lean_object*);
lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__14;
lean_object* l_Lean_Syntax_reprint_reprintLeaf(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Syntax_replaceM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21_match__1(lean_object*);
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__5;
lean_object* l_Lean_Syntax_isMissing___boxed(lean_object*);
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_setAtomVal_match__1(lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg___closed__1;
lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object*);
lean_object* l_Lean_Syntax_isMissing_match__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isQuot_match__1(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1___boxed(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Syntax_instForInTopDownSyntax_match__1(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__6;
lean_object* l_Lean_Syntax_getAtomVal_x21___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_reprint_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Syntax_ifNode___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__5;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2___boxed(lean_object*);
lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_unreachIsNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceM_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isMissing_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__1;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object*);
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__8;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
lean_object* l_Lean_SyntaxNode_withArgs_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateTrailing_match__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUpM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object*);
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs___rarg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_topDown(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg___closed__1;
lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object*);
lean_object* l_Lean_Syntax_isTokenAntiquot___closed__1;
lean_object* l_Lean_Syntax_topDown___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isTokenAntiquot___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_goDown___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__13;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg___lambda__1(lean_object*);
lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object*);
lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object*);
lean_object* l_Lean_Syntax_ifNode_match__1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object*, lean_object*);
lean_object* l_Lean_mkListNode(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___rarg(lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1;
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__6;
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailWithPos___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___rarg___lambda__1(lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object*);
lean_object* l_Lean_Syntax_replaceM___at_Lean_Syntax_updateLeading___spec__1___boxed__const__1;
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal_x21(lean_object*);
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_SyntaxNode_getKind_match__1(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object*);
lean_object* l_Lean_Syntax_isQuot___boxed(lean_object*);
lean_object* l_Lean_Syntax_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_rewriteBottomUp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode___closed__11;
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___rarg___lambda__1___boxed(lean_object*);
extern lean_object* l_term_x5b___x5d___closed__3;
extern lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object*);
lean_object* l_Lean_Syntax_reprint_match__1(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_SourceInfo_updateTrailing_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SourceInfo_updateTrailing_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 2);
lean_dec(x_4);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_1);
return x_7;
}
}
else
{
lean_dec(x_1);
return x_2;
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
lean_internal_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_internal_panic_unreachable();
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
lean_internal_panic_unreachable();
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
x_3 = lean_unsigned_to_nat(68u);
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
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_5(x_4, x_6, x_7, x_8, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_10;
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
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 2);
lean_dec(x_10);
lean_ctor_set(x_7, 2, x_3);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_1, 2, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_20 = x_14;
} else {
 lean_dec_ref(x_14);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 3, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_27 = x_22;
} else {
 lean_dec_ref(x_22);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 3, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 3, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_3);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
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
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_apply_5(x_2, x_5, x_7, x_8, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_4, x_1);
return x_11;
}
}
case 3:
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
x_19 = lean_apply_7(x_3, x_12, x_16, x_17, x_18, x_13, x_14, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_3);
x_20 = lean_apply_1(x_4, x_1);
return x_20;
}
}
default: 
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_apply_1(x_4, x_1);
return x_21;
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_6);
lean_inc(x_7);
x_8 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_3, x_2, x_7);
lean_ctor_set(x_1, 0, x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_12);
lean_inc(x_13);
x_14 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_3, x_2, x_13);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
}
case 3:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
x_24 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_23);
lean_inc(x_24);
x_25 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_20, x_2, x_24);
lean_ctor_set(x_1, 0, x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_1, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_31 = lean_ctor_get(x_20, 2);
lean_inc(x_31);
x_32 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_31);
lean_inc(x_32);
x_33 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_20, x_2, x_32);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_20);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
return x_38;
}
}
default: 
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_2);
return x_40;
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
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_50);
lean_inc(x_51);
x_52 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_48, x_2, x_51);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_3 = x_55;
goto block_15;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_48);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_2);
x_3 = x_57;
goto block_15;
}
}
default: 
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(x_62);
lean_inc(x_63);
x_64 = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(x_58, x_2, x_63);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
x_3 = x_67;
goto block_15;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_58);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_2);
x_3 = x_69;
goto block_15;
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
x_26 = l_Lean_SourceInfo_updateTrailing(x_1, x_25);
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
x_29 = l_Lean_SourceInfo_updateTrailing(x_1, x_27);
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
x_33 = l_Lean_SourceInfo_updateTrailing(x_1, x_32);
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
x_38 = l_Lean_SourceInfo_updateTrailing(x_1, x_34);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_apply_3(x_2, x_1, x_10, x_11);
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
x_17 = lean_apply_5(x_3, x_1, x_13, x_14, x_15, x_16);
return x_17;
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = 0;
x_8 = l_Lean_SourceInfo_getPos_x3f(x_6, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
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
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
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
lean_object* l_Lean_Syntax_topDown(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_topDown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Syntax_topDown(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop_match__2___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(x_3);
x_6 = lean_apply_2(x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_apply_2(x_8, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_apply_2(x_15, lean_box(0), x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
lean_inc(x_23);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_21);
lean_closure_set(x_26, 2, x_23);
x_27 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_25, x_26);
return x_27;
}
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_instForInTopDownSyntax_loop___rarg(x_1, x_2, x_3, x_7, x_9, x_4);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__2), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_1(x_2, x_6);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_13);
return x_16;
}
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_20, 0, x_1);
if (x_5 == 0)
{
lean_object* x_33; 
lean_dec(x_18);
x_33 = lean_box(0);
x_21 = x_33;
goto block_32;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_choiceKind;
x_35 = lean_name_eq(x_18, x_34);
lean_dec(x_18);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_21 = x_36;
goto block_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_37 = l_Lean_instInhabitedSyntax;
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_get(x_37, x_19, x_38);
lean_dec(x_19);
lean_inc(x_1);
x_40 = l_Lean_Syntax_instForInTopDownSyntax_loop___rarg(x_1, x_4, x_5, x_39, x_17, x_6);
x_41 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__5), 2, 1);
lean_closure_set(x_41, 0, x_1);
x_42 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_40, x_41);
return x_42;
}
}
block_32:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_box(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__3___boxed), 8, 6);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_4);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_6);
lean_closure_set(x_25, 4, x_22);
lean_closure_set(x_25, 5, x_3);
x_26 = lean_array_get_size(x_19);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
lean_inc(x_1);
x_29 = l_Array_forInUnsafe_loop___rarg(x_1, x_19, x_25, x_27, x_28, x_23);
lean_inc(x_3);
x_30 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__4), 4, 3);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_20);
lean_closure_set(x_30, 2, x_3);
x_31 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
lean_dec(x_7);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_apply_2(x_45, lean_box(0), x_46);
x_48 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_48, 0, x_1);
lean_closure_set(x_48, 1, x_43);
x_49 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_47, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_8 = lean_apply_2(x_2, x_4, x_5);
x_9 = lean_box(x_3);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__6___boxed), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_2);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_6);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__3(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__6(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Syntax_instForInTopDownSyntax_loop___rarg(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_9 < x_8;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg(x_1, x_2, x_3, x_4, x_15, x_17);
lean_inc(x_5);
lean_inc(x_6);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__2), 4, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_5);
lean_inc(x_5);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_box_usize(x_9);
x_22 = lean_box(x_4);
x_23 = lean_box_usize(x_8);
x_24 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_21);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_6);
lean_closure_set(x_24, 7, x_7);
lean_closure_set(x_24, 8, x_23);
x_25 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_20, x_24);
return x_25;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___boxed), 10, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_20, 0, x_1);
if (x_6 == 0)
{
lean_object* x_31; 
lean_dec(x_18);
x_31 = lean_box(0);
x_21 = x_31;
goto block_30;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_choiceKind;
x_33 = lean_name_eq(x_18, x_32);
lean_dec(x_18);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_21 = x_34;
goto block_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_20);
x_35 = l_Lean_instInhabitedSyntax;
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get(x_35, x_19, x_36);
lean_dec(x_19);
lean_inc(x_1);
x_38 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg(x_1, x_4, x_5, x_6, x_37, x_17);
x_39 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__5), 2, 1);
lean_closure_set(x_39, 0, x_1);
x_40 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
}
}
block_30:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_array_get_size(x_19);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg(x_1, x_4, x_5, x_6, x_3, x_22, x_19, x_25, x_26, x_23);
lean_inc(x_3);
x_28 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__4), 4, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_20);
lean_closure_set(x_28, 2, x_3);
x_29 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_27, x_28);
return x_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
lean_dec(x_7);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
x_46 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_41);
x_47 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_45, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_5);
x_8 = lean_apply_2(x_3, x_5, x_6);
x_9 = lean_box(x_4);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_2);
lean_closure_set(x_10, 4, x_3);
lean_closure_set(x_10, 5, x_9);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_3);
x_9 = lean_alloc_closure((void*)(l_Std_RBMap_instForInRBMapProd___rarg___lambda__1), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; uint8_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___lambda__1(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_13, x_10);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__2___rarg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_12, x_13, x_10);
return x_14;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_instForInTopDownSyntax___spec__1___rarg(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
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
lean_object* l_Lean_Syntax_reprint_reprintLeaf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
x_9 = l_Lean_instInhabitedParserDescr___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = lean_string_append(x_11, x_2);
x_13 = lean_string_append(x_12, x_9);
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_string_utf8_extract(x_14, x_15, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_20);
return x_22;
}
}
}
lean_object* l_Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_reprint_reprintLeaf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lean_Syntax_reprint(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_string_dec_eq(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = x_5 + x_14;
x_16 = lean_box(0);
x_5 = x_15;
x_6 = x_16;
goto _start;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_3, x_5);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2(x_1, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_free_object(x_11);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = x_5 + x_25;
x_5 = x_26;
x_6 = x_24;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
lean_inc(x_29);
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
lean_inc(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
x_37 = 1;
x_38 = x_5 + x_37;
x_5 = x_38;
x_6 = x_36;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_3);
x_4 = x_41;
goto block_40;
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
x_44 = l_Lean_choiceKind;
x_45 = lean_name_eq(x_42, x_44);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_3);
x_4 = x_46;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lean_instInhabitedSyntax;
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_array_get(x_47, x_43, x_48);
x_50 = l_Lean_Syntax_reprint(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_box(0);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; lean_object* x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_array_get_size(x_43);
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Array_toSubarray___rarg(x_43, x_54, x_53);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
x_57 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = lean_box(0);
lean_inc(x_2);
x_61 = l_Subarray_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__1(x_2, x_52, x_55, x_57, x_59, x_60);
lean_dec(x_55);
lean_dec(x_52);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(0);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
x_63 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___lambda__1(x_3, x_60);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_4 = x_64;
goto block_40;
}
}
}
}
case 2:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_67 = l_Lean_Syntax_reprint_reprintLeaf(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
x_68 = lean_string_append(x_3, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_4 = x_69;
goto block_40;
}
default: 
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_string_utf8_extract(x_72, x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
x_76 = l_Lean_Syntax_reprint_reprintLeaf(x_71, x_75);
lean_dec(x_75);
lean_dec(x_71);
x_77 = lean_string_append(x_3, x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_4 = x_78;
goto block_40;
}
}
block_40:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___closed__1;
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
if (x_1 == 0)
{
lean_object* x_26; 
lean_dec(x_7);
x_26 = lean_box(0);
x_9 = x_26;
goto block_25;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_choiceKind;
x_28 = lean_name_eq(x_7, x_27);
lean_dec(x_7);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_9 = x_29;
goto block_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_instInhabitedSyntax;
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get(x_30, x_8, x_31);
lean_dec(x_8);
x_33 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2(x_1, x_32, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
block_25:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_array_get_size(x_8);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__3(x_1, x_10, x_8, x_13, x_14, x_11);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_6, x_19, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_apply_2(x_6, x_5, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Syntax_reprint(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
x_4 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2(x_2, x_1, x_3);
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Subarray_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Syntax_reprint___spec__3(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2(x_4, x_2, x_3);
return x_5;
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
static lean_object* _init_l_Lean_Syntax_isQuot_match__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dynamicQuot");
return x_1;
}
}
lean_object* l_Lean_Syntax_isQuot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get_usize(x_5, 2);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get_usize(x_8, 2);
x_24 = lean_ctor_get(x_18, 1);
x_25 = lean_ctor_get_usize(x_18, 2);
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get_usize(x_19, 2);
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_32 = lean_string_dec_eq(x_28, x_31);
lean_dec(x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_19);
lean_free_object(x_18);
lean_dec(x_24);
lean_dec(x_21);
lean_free_object(x_5);
lean_dec(x_3);
x_33 = lean_box(0);
x_11 = x_33;
goto block_17;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_1, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_8, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 0);
lean_dec(x_39);
x_40 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_41 = lean_string_dec_eq(x_24, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_3);
x_42 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_43 = lean_string_dec_eq(x_9, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_2);
lean_ctor_set(x_19, 1, x_31);
x_44 = lean_apply_1(x_4, x_1);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_1);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_ctor_set(x_19, 1, x_31);
x_45 = lean_box_usize(x_10);
x_46 = lean_apply_3(x_2, x_8, x_45, x_6);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_24);
x_47 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_48 = lean_string_dec_eq(x_21, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_3);
x_49 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_50 = lean_string_dec_eq(x_9, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_2);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_40);
x_51 = lean_apply_1(x_4, x_1);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_1);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_40);
x_52 = lean_box_usize(x_10);
x_53 = lean_apply_3(x_2, x_8, x_52, x_6);
return x_53;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_21);
x_54 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_55 = lean_string_dec_eq(x_9, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_2);
x_56 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_57 = lean_string_dec_eq(x_9, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_3);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_40);
lean_ctor_set(x_8, 1, x_47);
x_58 = lean_apply_1(x_4, x_1);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_8);
lean_free_object(x_1);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
x_59 = lean_box_usize(x_29);
x_60 = lean_box_usize(x_25);
x_61 = lean_box_usize(x_23);
x_62 = lean_box_usize(x_10);
x_63 = lean_apply_5(x_3, x_6, x_59, x_60, x_61, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_free_object(x_1);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_40);
lean_ctor_set(x_8, 1, x_47);
x_64 = lean_box_usize(x_10);
x_65 = lean_apply_3(x_2, x_8, x_64, x_6);
return x_65;
}
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_8);
x_66 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_67 = lean_string_dec_eq(x_24, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_3);
x_68 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_69 = lean_string_dec_eq(x_9, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_2);
lean_ctor_set(x_19, 1, x_31);
x_70 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_21);
lean_ctor_set_usize(x_70, 2, x_23);
lean_ctor_set(x_5, 0, x_70);
x_71 = lean_apply_1(x_4, x_1);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_1);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_ctor_set(x_19, 1, x_31);
x_72 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_21);
lean_ctor_set_usize(x_72, 2, x_23);
x_73 = lean_box_usize(x_10);
x_74 = lean_apply_3(x_2, x_72, x_73, x_6);
return x_74;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_24);
x_75 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_76 = lean_string_dec_eq(x_21, x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_3);
x_77 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_78 = lean_string_dec_eq(x_9, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_66);
x_79 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_79, 0, x_18);
lean_ctor_set(x_79, 1, x_21);
lean_ctor_set_usize(x_79, 2, x_23);
lean_ctor_set(x_5, 0, x_79);
x_80 = lean_apply_1(x_4, x_1);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_free_object(x_1);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_66);
x_81 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_81, 0, x_18);
lean_ctor_set(x_81, 1, x_21);
lean_ctor_set_usize(x_81, 2, x_23);
x_82 = lean_box_usize(x_10);
x_83 = lean_apply_3(x_2, x_81, x_82, x_6);
return x_83;
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_21);
x_84 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_85 = lean_string_dec_eq(x_9, x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
lean_dec(x_2);
x_86 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_87 = lean_string_dec_eq(x_9, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_66);
x_88 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_88, 0, x_18);
lean_ctor_set(x_88, 1, x_75);
lean_ctor_set_usize(x_88, 2, x_23);
lean_ctor_set(x_5, 0, x_88);
x_89 = lean_apply_1(x_4, x_1);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_1);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
x_90 = lean_box_usize(x_29);
x_91 = lean_box_usize(x_25);
x_92 = lean_box_usize(x_23);
x_93 = lean_box_usize(x_10);
x_94 = lean_apply_5(x_3, x_6, x_90, x_91, x_92, x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_1);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_66);
x_95 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_95, 0, x_18);
lean_ctor_set(x_95, 1, x_75);
lean_ctor_set_usize(x_95, 2, x_23);
x_96 = lean_box_usize(x_10);
x_97 = lean_apply_3(x_2, x_95, x_96, x_6);
return x_97;
}
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_98 = x_8;
} else {
 lean_dec_ref(x_8);
 x_98 = lean_box(0);
}
x_99 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_100 = lean_string_dec_eq(x_24, x_99);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_3);
x_101 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_102 = lean_string_dec_eq(x_9, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
lean_ctor_set(x_19, 1, x_31);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_18);
lean_ctor_set(x_103, 1, x_21);
lean_ctor_set_usize(x_103, 2, x_23);
lean_ctor_set(x_5, 0, x_103);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_5);
lean_ctor_set(x_104, 1, x_6);
x_105 = lean_apply_1(x_4, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_ctor_set(x_19, 1, x_31);
if (lean_is_scalar(x_98)) {
 x_106 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_106 = x_98;
}
lean_ctor_set(x_106, 0, x_18);
lean_ctor_set(x_106, 1, x_21);
lean_ctor_set_usize(x_106, 2, x_23);
x_107 = lean_box_usize(x_10);
x_108 = lean_apply_3(x_2, x_106, x_107, x_6);
return x_108;
}
}
else
{
lean_object* x_109; uint8_t x_110; 
lean_dec(x_24);
x_109 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_110 = lean_string_dec_eq(x_21, x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_3);
x_111 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_112 = lean_string_dec_eq(x_9, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_99);
if (lean_is_scalar(x_98)) {
 x_113 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_113 = x_98;
}
lean_ctor_set(x_113, 0, x_18);
lean_ctor_set(x_113, 1, x_21);
lean_ctor_set_usize(x_113, 2, x_23);
lean_ctor_set(x_5, 0, x_113);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_5);
lean_ctor_set(x_114, 1, x_6);
x_115 = lean_apply_1(x_4, x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_99);
if (lean_is_scalar(x_98)) {
 x_116 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_116 = x_98;
}
lean_ctor_set(x_116, 0, x_18);
lean_ctor_set(x_116, 1, x_21);
lean_ctor_set_usize(x_116, 2, x_23);
x_117 = lean_box_usize(x_10);
x_118 = lean_apply_3(x_2, x_116, x_117, x_6);
return x_118;
}
}
else
{
lean_object* x_119; uint8_t x_120; 
lean_dec(x_21);
x_119 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_120 = lean_string_dec_eq(x_9, x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_2);
x_121 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_122 = lean_string_dec_eq(x_9, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_99);
if (lean_is_scalar(x_98)) {
 x_123 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_123 = x_98;
}
lean_ctor_set(x_123, 0, x_18);
lean_ctor_set(x_123, 1, x_109);
lean_ctor_set_usize(x_123, 2, x_23);
lean_ctor_set(x_5, 0, x_123);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_5);
lean_ctor_set(x_124, 1, x_6);
x_125 = lean_apply_1(x_4, x_124);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_98);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
x_126 = lean_box_usize(x_29);
x_127 = lean_box_usize(x_25);
x_128 = lean_box_usize(x_23);
x_129 = lean_box_usize(x_10);
x_130 = lean_apply_5(x_3, x_6, x_126, x_127, x_128, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_19, 1, x_31);
lean_ctor_set(x_18, 1, x_99);
if (lean_is_scalar(x_98)) {
 x_131 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_131 = x_98;
}
lean_ctor_set(x_131, 0, x_18);
lean_ctor_set(x_131, 1, x_109);
lean_ctor_set_usize(x_131, 2, x_23);
x_132 = lean_box_usize(x_10);
x_133 = lean_apply_3(x_2, x_131, x_132, x_6);
return x_133;
}
}
}
}
}
}
else
{
lean_object* x_134; size_t x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_19, 1);
x_135 = lean_ctor_get_usize(x_19, 2);
lean_inc(x_134);
lean_dec(x_19);
x_136 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_137 = lean_string_dec_eq(x_134, x_136);
lean_dec(x_134);
if (x_137 == 0)
{
lean_object* x_138; 
lean_free_object(x_18);
lean_dec(x_24);
lean_dec(x_21);
lean_free_object(x_5);
lean_dec(x_3);
x_138 = lean_box(0);
x_11 = x_138;
goto block_17;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_139 = x_1;
} else {
 lean_dec_ref(x_1);
 x_139 = lean_box(0);
}
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_140 = x_8;
} else {
 lean_dec_ref(x_8);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_142 = lean_string_dec_eq(x_24, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
lean_dec(x_3);
x_143 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_144 = lean_string_dec_eq(x_9, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_2);
x_145 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_145, 0, x_20);
lean_ctor_set(x_145, 1, x_136);
lean_ctor_set_usize(x_145, 2, x_135);
lean_ctor_set(x_18, 0, x_145);
if (lean_is_scalar(x_140)) {
 x_146 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_146 = x_140;
}
lean_ctor_set(x_146, 0, x_18);
lean_ctor_set(x_146, 1, x_21);
lean_ctor_set_usize(x_146, 2, x_23);
lean_ctor_set(x_5, 0, x_146);
if (lean_is_scalar(x_139)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_139;
}
lean_ctor_set(x_147, 0, x_5);
lean_ctor_set(x_147, 1, x_6);
x_148 = lean_apply_1(x_4, x_147);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_139);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
x_149 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_149, 0, x_20);
lean_ctor_set(x_149, 1, x_136);
lean_ctor_set_usize(x_149, 2, x_135);
lean_ctor_set(x_18, 0, x_149);
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_18);
lean_ctor_set(x_150, 1, x_21);
lean_ctor_set_usize(x_150, 2, x_23);
x_151 = lean_box_usize(x_10);
x_152 = lean_apply_3(x_2, x_150, x_151, x_6);
return x_152;
}
}
else
{
lean_object* x_153; uint8_t x_154; 
lean_dec(x_24);
x_153 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_154 = lean_string_dec_eq(x_21, x_153);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_3);
x_155 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_156 = lean_string_dec_eq(x_9, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
x_157 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_157, 0, x_20);
lean_ctor_set(x_157, 1, x_136);
lean_ctor_set_usize(x_157, 2, x_135);
lean_ctor_set(x_18, 1, x_141);
lean_ctor_set(x_18, 0, x_157);
if (lean_is_scalar(x_140)) {
 x_158 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_158 = x_140;
}
lean_ctor_set(x_158, 0, x_18);
lean_ctor_set(x_158, 1, x_21);
lean_ctor_set_usize(x_158, 2, x_23);
lean_ctor_set(x_5, 0, x_158);
if (lean_is_scalar(x_139)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_139;
}
lean_ctor_set(x_159, 0, x_5);
lean_ctor_set(x_159, 1, x_6);
x_160 = lean_apply_1(x_4, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_139);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
x_161 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_161, 0, x_20);
lean_ctor_set(x_161, 1, x_136);
lean_ctor_set_usize(x_161, 2, x_135);
lean_ctor_set(x_18, 1, x_141);
lean_ctor_set(x_18, 0, x_161);
if (lean_is_scalar(x_140)) {
 x_162 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_162 = x_140;
}
lean_ctor_set(x_162, 0, x_18);
lean_ctor_set(x_162, 1, x_21);
lean_ctor_set_usize(x_162, 2, x_23);
x_163 = lean_box_usize(x_10);
x_164 = lean_apply_3(x_2, x_162, x_163, x_6);
return x_164;
}
}
else
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_21);
x_165 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_166 = lean_string_dec_eq(x_9, x_165);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
lean_dec(x_2);
x_167 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_168 = lean_string_dec_eq(x_9, x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_3);
x_169 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_169, 0, x_20);
lean_ctor_set(x_169, 1, x_136);
lean_ctor_set_usize(x_169, 2, x_135);
lean_ctor_set(x_18, 1, x_141);
lean_ctor_set(x_18, 0, x_169);
if (lean_is_scalar(x_140)) {
 x_170 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_170 = x_140;
}
lean_ctor_set(x_170, 0, x_18);
lean_ctor_set(x_170, 1, x_153);
lean_ctor_set_usize(x_170, 2, x_23);
lean_ctor_set(x_5, 0, x_170);
if (lean_is_scalar(x_139)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_139;
}
lean_ctor_set(x_171, 0, x_5);
lean_ctor_set(x_171, 1, x_6);
x_172 = lean_apply_1(x_4, x_171);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_140);
lean_dec(x_139);
lean_free_object(x_18);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
x_173 = lean_box_usize(x_135);
x_174 = lean_box_usize(x_25);
x_175 = lean_box_usize(x_23);
x_176 = lean_box_usize(x_10);
x_177 = lean_apply_5(x_3, x_6, x_173, x_174, x_175, x_176);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_139);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_178, 0, x_20);
lean_ctor_set(x_178, 1, x_136);
lean_ctor_set_usize(x_178, 2, x_135);
lean_ctor_set(x_18, 1, x_141);
lean_ctor_set(x_18, 0, x_178);
if (lean_is_scalar(x_140)) {
 x_179 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_179 = x_140;
}
lean_ctor_set(x_179, 0, x_18);
lean_ctor_set(x_179, 1, x_153);
lean_ctor_set_usize(x_179, 2, x_23);
x_180 = lean_box_usize(x_10);
x_181 = lean_apply_3(x_2, x_179, x_180, x_6);
return x_181;
}
}
}
}
}
}
else
{
size_t x_182; lean_object* x_183; size_t x_184; lean_object* x_185; size_t x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_182 = lean_ctor_get_usize(x_8, 2);
x_183 = lean_ctor_get(x_18, 1);
x_184 = lean_ctor_get_usize(x_18, 2);
lean_inc(x_183);
lean_dec(x_18);
x_185 = lean_ctor_get(x_19, 1);
lean_inc(x_185);
x_186 = lean_ctor_get_usize(x_19, 2);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_187 = x_19;
} else {
 lean_dec_ref(x_19);
 x_187 = lean_box(0);
}
x_188 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_189 = lean_string_dec_eq(x_185, x_188);
lean_dec(x_185);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_187);
lean_dec(x_183);
lean_dec(x_21);
lean_free_object(x_5);
lean_dec(x_3);
x_190 = lean_box(0);
x_11 = x_190;
goto block_17;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_191 = x_1;
} else {
 lean_dec_ref(x_1);
 x_191 = lean_box(0);
}
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_192 = x_8;
} else {
 lean_dec_ref(x_8);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_194 = lean_string_dec_eq(x_183, x_193);
if (x_194 == 0)
{
lean_object* x_195; uint8_t x_196; 
lean_dec(x_3);
x_195 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_196 = lean_string_dec_eq(x_9, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_2);
if (lean_is_scalar(x_187)) {
 x_197 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_197 = x_187;
}
lean_ctor_set(x_197, 0, x_20);
lean_ctor_set(x_197, 1, x_188);
lean_ctor_set_usize(x_197, 2, x_186);
x_198 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_183);
lean_ctor_set_usize(x_198, 2, x_184);
if (lean_is_scalar(x_192)) {
 x_199 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_199 = x_192;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_21);
lean_ctor_set_usize(x_199, 2, x_182);
lean_ctor_set(x_5, 0, x_199);
if (lean_is_scalar(x_191)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_191;
}
lean_ctor_set(x_200, 0, x_5);
lean_ctor_set(x_200, 1, x_6);
x_201 = lean_apply_1(x_4, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_191);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
if (lean_is_scalar(x_187)) {
 x_202 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_202 = x_187;
}
lean_ctor_set(x_202, 0, x_20);
lean_ctor_set(x_202, 1, x_188);
lean_ctor_set_usize(x_202, 2, x_186);
x_203 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_183);
lean_ctor_set_usize(x_203, 2, x_184);
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_21);
lean_ctor_set_usize(x_204, 2, x_182);
x_205 = lean_box_usize(x_10);
x_206 = lean_apply_3(x_2, x_204, x_205, x_6);
return x_206;
}
}
else
{
lean_object* x_207; uint8_t x_208; 
lean_dec(x_183);
x_207 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_208 = lean_string_dec_eq(x_21, x_207);
if (x_208 == 0)
{
lean_object* x_209; uint8_t x_210; 
lean_dec(x_3);
x_209 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_210 = lean_string_dec_eq(x_9, x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_2);
if (lean_is_scalar(x_187)) {
 x_211 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_211 = x_187;
}
lean_ctor_set(x_211, 0, x_20);
lean_ctor_set(x_211, 1, x_188);
lean_ctor_set_usize(x_211, 2, x_186);
x_212 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_193);
lean_ctor_set_usize(x_212, 2, x_184);
if (lean_is_scalar(x_192)) {
 x_213 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_213 = x_192;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_21);
lean_ctor_set_usize(x_213, 2, x_182);
lean_ctor_set(x_5, 0, x_213);
if (lean_is_scalar(x_191)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_191;
}
lean_ctor_set(x_214, 0, x_5);
lean_ctor_set(x_214, 1, x_6);
x_215 = lean_apply_1(x_4, x_214);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_191);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
if (lean_is_scalar(x_187)) {
 x_216 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_216 = x_187;
}
lean_ctor_set(x_216, 0, x_20);
lean_ctor_set(x_216, 1, x_188);
lean_ctor_set_usize(x_216, 2, x_186);
x_217 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_193);
lean_ctor_set_usize(x_217, 2, x_184);
if (lean_is_scalar(x_192)) {
 x_218 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_218 = x_192;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_21);
lean_ctor_set_usize(x_218, 2, x_182);
x_219 = lean_box_usize(x_10);
x_220 = lean_apply_3(x_2, x_218, x_219, x_6);
return x_220;
}
}
else
{
lean_object* x_221; uint8_t x_222; 
lean_dec(x_21);
x_221 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_222 = lean_string_dec_eq(x_9, x_221);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
lean_dec(x_2);
x_223 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_224 = lean_string_dec_eq(x_9, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_3);
if (lean_is_scalar(x_187)) {
 x_225 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_225 = x_187;
}
lean_ctor_set(x_225, 0, x_20);
lean_ctor_set(x_225, 1, x_188);
lean_ctor_set_usize(x_225, 2, x_186);
x_226 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_193);
lean_ctor_set_usize(x_226, 2, x_184);
if (lean_is_scalar(x_192)) {
 x_227 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_227 = x_192;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_207);
lean_ctor_set_usize(x_227, 2, x_182);
lean_ctor_set(x_5, 0, x_227);
if (lean_is_scalar(x_191)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_191;
}
lean_ctor_set(x_228, 0, x_5);
lean_ctor_set(x_228, 1, x_6);
x_229 = lean_apply_1(x_4, x_228);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_187);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
x_230 = lean_box_usize(x_186);
x_231 = lean_box_usize(x_184);
x_232 = lean_box_usize(x_182);
x_233 = lean_box_usize(x_10);
x_234 = lean_apply_5(x_3, x_6, x_230, x_231, x_232, x_233);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_191);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_187)) {
 x_235 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_235 = x_187;
}
lean_ctor_set(x_235, 0, x_20);
lean_ctor_set(x_235, 1, x_188);
lean_ctor_set_usize(x_235, 2, x_186);
x_236 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_193);
lean_ctor_set_usize(x_236, 2, x_184);
if (lean_is_scalar(x_192)) {
 x_237 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_237 = x_192;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_207);
lean_ctor_set_usize(x_237, 2, x_182);
x_238 = lean_box_usize(x_10);
x_239 = lean_apply_3(x_2, x_237, x_238, x_6);
return x_239;
}
}
}
}
}
}
else
{
lean_object* x_240; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_3);
x_240 = lean_box(0);
x_11 = x_240;
goto block_17;
}
}
else
{
lean_object* x_241; 
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_3);
x_241 = lean_box(0);
x_11 = x_241;
goto block_17;
}
}
else
{
lean_object* x_242; 
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_3);
x_242 = lean_box(0);
x_11 = x_242;
goto block_17;
}
}
else
{
lean_object* x_243; 
lean_free_object(x_5);
lean_dec(x_3);
x_243 = lean_box(0);
x_11 = x_243;
goto block_17;
}
block_17:
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_11);
x_12 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_13 = lean_string_dec_eq(x_9, x_12);
lean_dec(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_box_usize(x_10);
x_16 = lean_apply_3(x_2, x_8, x_15, x_6);
return x_16;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; size_t x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_5, 0);
x_245 = lean_ctor_get(x_5, 1);
x_246 = lean_ctor_get_usize(x_5, 2);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_5);
if (lean_obj_tag(x_244) == 1)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_244, 0);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 1)
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_obj_tag(x_255) == 1)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; size_t x_258; lean_object* x_259; size_t x_260; lean_object* x_261; lean_object* x_262; size_t x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_257 = lean_ctor_get(x_244, 1);
lean_inc(x_257);
x_258 = lean_ctor_get_usize(x_244, 2);
x_259 = lean_ctor_get(x_254, 1);
lean_inc(x_259);
x_260 = lean_ctor_get_usize(x_254, 2);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_261 = x_254;
} else {
 lean_dec_ref(x_254);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_255, 1);
lean_inc(x_262);
x_263 = lean_ctor_get_usize(x_255, 2);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_264 = x_255;
} else {
 lean_dec_ref(x_255);
 x_264 = lean_box(0);
}
x_265 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_266 = lean_string_dec_eq(x_262, x_265);
lean_dec(x_262);
if (x_266 == 0)
{
lean_object* x_267; 
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_259);
lean_dec(x_257);
lean_dec(x_3);
x_267 = lean_box(0);
x_247 = x_267;
goto block_253;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_268 = x_1;
} else {
 lean_dec_ref(x_1);
 x_268 = lean_box(0);
}
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_269 = x_244;
} else {
 lean_dec_ref(x_244);
 x_269 = lean_box(0);
}
x_270 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_271 = lean_string_dec_eq(x_259, x_270);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
lean_dec(x_3);
x_272 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_273 = lean_string_dec_eq(x_245, x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_2);
if (lean_is_scalar(x_264)) {
 x_274 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_274 = x_264;
}
lean_ctor_set(x_274, 0, x_256);
lean_ctor_set(x_274, 1, x_265);
lean_ctor_set_usize(x_274, 2, x_263);
if (lean_is_scalar(x_261)) {
 x_275 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_275 = x_261;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_259);
lean_ctor_set_usize(x_275, 2, x_260);
if (lean_is_scalar(x_269)) {
 x_276 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_276 = x_269;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_257);
lean_ctor_set_usize(x_276, 2, x_258);
x_277 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_245);
lean_ctor_set_usize(x_277, 2, x_246);
if (lean_is_scalar(x_268)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_268;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_6);
x_279 = lean_apply_1(x_4, x_278);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_268);
lean_dec(x_245);
lean_dec(x_4);
if (lean_is_scalar(x_264)) {
 x_280 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_280 = x_264;
}
lean_ctor_set(x_280, 0, x_256);
lean_ctor_set(x_280, 1, x_265);
lean_ctor_set_usize(x_280, 2, x_263);
if (lean_is_scalar(x_261)) {
 x_281 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_281 = x_261;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_259);
lean_ctor_set_usize(x_281, 2, x_260);
if (lean_is_scalar(x_269)) {
 x_282 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_282 = x_269;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_257);
lean_ctor_set_usize(x_282, 2, x_258);
x_283 = lean_box_usize(x_246);
x_284 = lean_apply_3(x_2, x_282, x_283, x_6);
return x_284;
}
}
else
{
lean_object* x_285; uint8_t x_286; 
lean_dec(x_259);
x_285 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_286 = lean_string_dec_eq(x_257, x_285);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
lean_dec(x_3);
x_287 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_288 = lean_string_dec_eq(x_245, x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_2);
if (lean_is_scalar(x_264)) {
 x_289 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_289 = x_264;
}
lean_ctor_set(x_289, 0, x_256);
lean_ctor_set(x_289, 1, x_265);
lean_ctor_set_usize(x_289, 2, x_263);
if (lean_is_scalar(x_261)) {
 x_290 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_290 = x_261;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_270);
lean_ctor_set_usize(x_290, 2, x_260);
if (lean_is_scalar(x_269)) {
 x_291 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_291 = x_269;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_257);
lean_ctor_set_usize(x_291, 2, x_258);
x_292 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_245);
lean_ctor_set_usize(x_292, 2, x_246);
if (lean_is_scalar(x_268)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_268;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_6);
x_294 = lean_apply_1(x_4, x_293);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_268);
lean_dec(x_245);
lean_dec(x_4);
if (lean_is_scalar(x_264)) {
 x_295 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_295 = x_264;
}
lean_ctor_set(x_295, 0, x_256);
lean_ctor_set(x_295, 1, x_265);
lean_ctor_set_usize(x_295, 2, x_263);
if (lean_is_scalar(x_261)) {
 x_296 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_296 = x_261;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_270);
lean_ctor_set_usize(x_296, 2, x_260);
if (lean_is_scalar(x_269)) {
 x_297 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_297 = x_269;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_257);
lean_ctor_set_usize(x_297, 2, x_258);
x_298 = lean_box_usize(x_246);
x_299 = lean_apply_3(x_2, x_297, x_298, x_6);
return x_299;
}
}
else
{
lean_object* x_300; uint8_t x_301; 
lean_dec(x_257);
x_300 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_301 = lean_string_dec_eq(x_245, x_300);
if (x_301 == 0)
{
lean_object* x_302; uint8_t x_303; 
lean_dec(x_2);
x_302 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_303 = lean_string_dec_eq(x_245, x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_3);
if (lean_is_scalar(x_264)) {
 x_304 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_304 = x_264;
}
lean_ctor_set(x_304, 0, x_256);
lean_ctor_set(x_304, 1, x_265);
lean_ctor_set_usize(x_304, 2, x_263);
if (lean_is_scalar(x_261)) {
 x_305 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_305 = x_261;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_270);
lean_ctor_set_usize(x_305, 2, x_260);
if (lean_is_scalar(x_269)) {
 x_306 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_306 = x_269;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_285);
lean_ctor_set_usize(x_306, 2, x_258);
x_307 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_245);
lean_ctor_set_usize(x_307, 2, x_246);
if (lean_is_scalar(x_268)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_268;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_6);
x_309 = lean_apply_1(x_4, x_308);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_245);
lean_dec(x_4);
x_310 = lean_box_usize(x_263);
x_311 = lean_box_usize(x_260);
x_312 = lean_box_usize(x_258);
x_313 = lean_box_usize(x_246);
x_314 = lean_apply_5(x_3, x_6, x_310, x_311, x_312, x_313);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_268);
lean_dec(x_245);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_264)) {
 x_315 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_315 = x_264;
}
lean_ctor_set(x_315, 0, x_256);
lean_ctor_set(x_315, 1, x_265);
lean_ctor_set_usize(x_315, 2, x_263);
if (lean_is_scalar(x_261)) {
 x_316 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_316 = x_261;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_270);
lean_ctor_set_usize(x_316, 2, x_260);
if (lean_is_scalar(x_269)) {
 x_317 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_317 = x_269;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_285);
lean_ctor_set_usize(x_317, 2, x_258);
x_318 = lean_box_usize(x_246);
x_319 = lean_apply_3(x_2, x_317, x_318, x_6);
return x_319;
}
}
}
}
}
else
{
lean_object* x_320; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_3);
x_320 = lean_box(0);
x_247 = x_320;
goto block_253;
}
}
else
{
lean_object* x_321; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_3);
x_321 = lean_box(0);
x_247 = x_321;
goto block_253;
}
}
else
{
lean_object* x_322; 
lean_dec(x_254);
lean_dec(x_3);
x_322 = lean_box(0);
x_247 = x_322;
goto block_253;
}
}
else
{
lean_object* x_323; 
lean_dec(x_3);
x_323 = lean_box(0);
x_247 = x_323;
goto block_253;
}
block_253:
{
lean_object* x_248; uint8_t x_249; 
lean_dec(x_247);
x_248 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_249 = lean_string_dec_eq(x_245, x_248);
lean_dec(x_245);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec(x_244);
lean_dec(x_6);
lean_dec(x_2);
x_250 = lean_apply_1(x_4, x_1);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_4);
lean_dec(x_1);
x_251 = lean_box_usize(x_246);
x_252 = lean_apply_3(x_2, x_244, x_251, x_6);
return x_252;
}
}
}
}
else
{
lean_object* x_324; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_324 = lean_apply_1(x_4, x_1);
return x_324;
}
}
else
{
lean_object* x_325; 
lean_dec(x_3);
lean_dec(x_2);
x_325 = lean_apply_1(x_4, x_1);
return x_325;
}
}
}
lean_object* l_Lean_Syntax_isQuot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isQuot_match__1___rarg), 4, 0);
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_5, 1);
x_11 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_14 = lean_string_dec_eq(x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_18 = lean_string_dec_eq(x_7, x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_myMacro____x40_Init_Notation___hyg_2204____closed__1;
x_20 = lean_string_dec_eq(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_22 = lean_string_dec_eq(x_7, x_21);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_24 = lean_string_dec_eq(x_7, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_26 = lean_string_dec_eq(x_7, x_25);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_30 = lean_string_dec_eq(x_28, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_2, 1);
x_32 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_33 = lean_string_dec_eq(x_31, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_2, 1);
x_35 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_36 = lean_string_dec_eq(x_34, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_2, 1);
x_38 = l_Lean_Syntax_isQuot_match__1___rarg___closed__1;
x_39 = lean_string_dec_eq(x_37, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = 0;
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = 0;
return x_41;
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
static lean_object* _init_l_Lean_Syntax_getQuotContent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_2 = l_Lean_Syntax_isQuot_match__1___rarg___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getQuotContent(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Syntax_getQuotContent___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
return x_7;
}
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
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_term___x24_______closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_1 = lean_unsigned_to_nat(4u);
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
lean_object* x_1; 
x_1 = lean_mk_string("antiquotNestedExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_prec_x28___x29___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_prec_x28___x29___closed__7;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkAntiquotNode___closed__9;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquotName");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkApp___closed__1;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Syntax_mkAntiquotNode___closed__1;
x_6 = lean_mk_array(x_2, x_5);
x_7 = l_Lean_nullKind;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Syntax_isIdent(x_1);
x_10 = l_Lean_Syntax_mkAntiquotNode___closed__2;
x_11 = l_Lean_Name_append(x_4, x_10);
x_12 = l_Lean_Syntax_mkAntiquotNode___closed__4;
x_13 = lean_array_push(x_12, x_8);
if (x_9 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_Syntax_mkAntiquotNode___closed__10;
x_15 = lean_array_push(x_14, x_1);
x_16 = l_Lean_Syntax_mkAntiquotNode___closed__8;
x_17 = lean_array_push(x_15, x_16);
x_18 = l_Lean_Syntax_mkAntiquotNode___closed__6;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_push(x_13, x_19);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_mkOptionalNode___closed__1;
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_box(2);
lean_inc(x_24);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Syntax_mkAntiquotNode___closed__14;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_Syntax_mkAntiquotNode___closed__12;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_20, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = lean_array_push(x_13, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_mkOptionalNode___closed__1;
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_box(2);
lean_inc(x_37);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Syntax_mkAntiquotNode___closed__14;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Lean_Syntax_mkAntiquotNode___closed__12;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_push(x_33, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mkAntiquotNode(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
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
uint8_t x_2; 
x_2 = l_Lean_Syntax_isAntiquot(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_isIdent(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_4, x_6);
lean_dec(x_4);
return x_7;
}
else
{
return x_4;
}
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isIdent(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_9, x_11);
lean_dec(x_9);
return x_12;
}
else
{
return x_9;
}
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
x_12 = l_Lean_Syntax_mkAntiquotNode___closed__12;
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
static lean_object* _init_l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot_scope");
return x_1;
}
}
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1;
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
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* x_1) {
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
x_5 = l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1;
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
lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_antiquotSpliceKind_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_antiquotSpliceKind_x3f(x_1);
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
lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* x_1) {
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
lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getAntiquotSpliceContents(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isAntiquotSplice(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(5u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getAntiquotSpliceSuffix(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot_splice");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_mkAntiquotSpliceNode___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_term_x5b___x5d___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_term_x5b___x5d___closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkAntiquotSpliceNode___closed__5;
x_2 = l_Lean_Syntax_mkAntiquotNode___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = l_Lean_Syntax_mkAntiquotNode___closed__1;
x_6 = lean_mk_array(x_4, x_5);
x_7 = l_Lean_nullKind;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Syntax_mkAntiquotSpliceNode___closed__2;
x_10 = l_Lean_Name_append(x_1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_box(2);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = l_Lean_Syntax_mkAntiquotSpliceNode___closed__6;
x_15 = lean_array_push(x_14, x_8);
x_16 = l_Lean_Syntax_mkAntiquotSpliceNode___closed__3;
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_array_push(x_17, x_11);
x_19 = l_Lean_Syntax_mkAntiquotSpliceNode___closed__4;
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mkAntiquotSpliceNode(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot_suffix_splice");
return x_1;
}
}
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1;
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
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* x_1) {
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
x_5 = l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1;
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
lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_antiquotSuffixSplice_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_antiquotSuffixSplice_x3f(x_1);
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
lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAntiquotSuffixSplice(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getAntiquotSuffixSpliceInner(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1;
x_5 = l_Lean_Name_append(x_1, x_4);
x_6 = lean_box(2);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_array_push(x_9, x_7);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mkAntiquotSuffixSpliceNode(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_isTokenAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("token_antiquot");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_isTokenAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_isTokenAntiquot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Syntax_isTokenAntiquot___closed__2;
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isTokenAntiquot(x_1);
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
l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___closed__1 = _init_l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___closed__1();
lean_mark_persistent(l_Lean_Syntax_instForInTopDownSyntax_loop___at_Lean_Syntax_reprint___spec__2___closed__1);
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
l_Lean_Syntax_isQuot_match__1___rarg___closed__2 = _init_l_Lean_Syntax_isQuot_match__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Syntax_isQuot_match__1___rarg___closed__2);
l_Lean_Syntax_getQuotContent___closed__1 = _init_l_Lean_Syntax_getQuotContent___closed__1();
lean_mark_persistent(l_Lean_Syntax_getQuotContent___closed__1);
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
l_Lean_Syntax_antiquotKind_x3f___closed__1 = _init_l_Lean_Syntax_antiquotKind_x3f___closed__1();
lean_mark_persistent(l_Lean_Syntax_antiquotKind_x3f___closed__1);
l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1 = _init_l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1);
l_Lean_Syntax_mkAntiquotSpliceNode___closed__1 = _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1);
l_Lean_Syntax_mkAntiquotSpliceNode___closed__2 = _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__2();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2);
l_Lean_Syntax_mkAntiquotSpliceNode___closed__3 = _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
l_Lean_Syntax_mkAntiquotSpliceNode___closed__4 = _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__4();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4);
l_Lean_Syntax_mkAntiquotSpliceNode___closed__5 = _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
l_Lean_Syntax_mkAntiquotSpliceNode___closed__6 = _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1 = _init_l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Syntax_antiquotSuffixSplice_x3f_match__1___rarg___closed__1);
l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1 = _init_l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1);
l_Lean_Syntax_isTokenAntiquot___closed__1 = _init_l_Lean_Syntax_isTokenAntiquot___closed__1();
lean_mark_persistent(l_Lean_Syntax_isTokenAntiquot___closed__1);
l_Lean_Syntax_isTokenAntiquot___closed__2 = _init_l_Lean_Syntax_isTokenAntiquot___closed__2();
lean_mark_persistent(l_Lean_Syntax_isTokenAntiquot___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

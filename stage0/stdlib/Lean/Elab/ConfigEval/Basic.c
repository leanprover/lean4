// Lean compiler output
// Module: Lean.Elab.ConfigEval.Basic
// Imports: public import Lean.Elab.ConfigEval.Types public import Lean.Elab.SyntheticMVars import Lean.Elab.ConfigEval.Util
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
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_identComponents(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_hasMissing(lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Lean_Linter_mkReplacementHint___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Could not evaluate the expression:"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Option is not boolean-valued, so `("};
static const lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " := ...)` syntax must be used"};
static const lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Invalid configuration option"};
static const lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " for `"};
static const lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Cannot set option"};
static const lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " using configuration syntax."};
static const lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__2_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value;
static const lean_string_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8_value;
static const lean_string_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10_value;
static const lean_string_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11_value;
static const lean_string_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12_value;
static const lean_string_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_cfg_dummy"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(46, 239, 32, 15, 23, 237, 128, 232)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigEval"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(102, 213, 240, 228, 24, 48, 9, 246)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value;
static const lean_array_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__12;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__13;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(lean_object* v_inst_1_, lean_object* v_stx_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_evalTerm_10_; lean_object* v_toCold_11_; lean_object* v_currRecDepth_12_; lean_object* v_ref_13_; uint16_t v_optionFlags_14_; uint8_t v_suppressElabErrors_15_; uint8_t v_checkDeprecated_16_; uint8_t v_isRecordingDeps_17_; lean_object* v_ref_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_evalTerm_10_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_evalTerm_10_);
lean_dec_ref(v_inst_1_);
v_toCold_11_ = lean_ctor_get(v_a_7_, 0);
v_currRecDepth_12_ = lean_ctor_get(v_a_7_, 1);
v_ref_13_ = lean_ctor_get(v_a_7_, 2);
v_optionFlags_14_ = lean_ctor_get_uint16(v_a_7_, sizeof(void*)*3);
v_suppressElabErrors_15_ = lean_ctor_get_uint8(v_a_7_, sizeof(void*)*3 + 2);
v_checkDeprecated_16_ = lean_ctor_get_uint8(v_a_7_, sizeof(void*)*3 + 3);
v_isRecordingDeps_17_ = lean_ctor_get_uint8(v_a_7_, sizeof(void*)*3 + 4);
v_ref_18_ = l_Lean_replaceRef(v_stx_2_, v_ref_13_);
lean_inc(v_currRecDepth_12_);
lean_inc_ref(v_toCold_11_);
v___x_19_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_19_, 0, v_toCold_11_);
lean_ctor_set(v___x_19_, 1, v_currRecDepth_12_);
lean_ctor_set(v___x_19_, 2, v_ref_18_);
lean_ctor_set_uint16(v___x_19_, sizeof(void*)*3, v_optionFlags_14_);
lean_ctor_set_uint8(v___x_19_, sizeof(void*)*3 + 2, v_suppressElabErrors_15_);
lean_ctor_set_uint8(v___x_19_, sizeof(void*)*3 + 3, v_checkDeprecated_16_);
lean_ctor_set_uint8(v___x_19_, sizeof(void*)*3 + 4, v_isRecordingDeps_17_);
lean_inc(v_a_8_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_20_ = lean_apply_8(v_evalTerm_10_, v_stx_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v___x_19_, v_a_8_, lean_box(0));
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_29_ == 0)
{
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_fst_25_; lean_object* v___x_27_; 
v_fst_25_ = lean_ctor_get(v_a_21_, 0);
lean_inc(v_fst_25_);
lean_dec(v_a_21_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v_fst_25_);
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_fst_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_20_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_20_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___redArg___boxed(lean_object* v_inst_38_, lean_object* v_stx_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_38_, v_stx_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_, lean_object* v_stx_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_49_, v_stx_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___boxed(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_stx_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Elab_ConfigEval_evalTermWithRef(v_00_u03b1_59_, v_inst_60_, v_stx_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
return v_res_69_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_instMonadEIO___redArg();
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0);
v___x_72_ = l_StateRefT_x27_instMonad___redArg(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_81_; lean_object* v___f_82_; 
v___x_81_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_82_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_82_, 0, v___x_81_);
return v___f_82_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_83_; lean_object* v___f_84_; 
v___x_83_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_84_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_84_, 0, v___x_83_);
return v___f_84_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12(void){
_start:
{
lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___x_87_; 
v___f_85_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11);
v___f_86_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___f_86_);
lean_ctor_set(v___x_87_, 1, v___f_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13(void){
_start:
{
lean_object* v___x_88_; lean_object* v___f_89_; 
v___x_88_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_89_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_89_, 0, v___x_88_);
return v___f_89_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14(void){
_start:
{
lean_object* v___x_90_; lean_object* v___f_91_; 
v___x_90_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_91_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_91_, 0, v___x_90_);
return v___f_91_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15(void){
_start:
{
lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; 
v___f_92_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14);
v___f_93_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___f_93_);
lean_ctor_set(v___x_94_, 1, v___f_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16(void){
_start:
{
lean_object* v___x_95_; lean_object* v___f_96_; 
v___x_95_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_96_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_96_, 0, v___x_95_);
return v___f_96_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17(void){
_start:
{
lean_object* v___x_97_; lean_object* v___f_98_; 
v___x_97_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_98_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_98_, 0, v___x_97_);
return v___f_98_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18(void){
_start:
{
lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_101_; 
v___f_99_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17);
v___f_100_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___f_100_);
lean_ctor_set(v___x_101_, 1, v___f_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19(void){
_start:
{
lean_object* v___x_102_; lean_object* v___f_103_; 
v___x_102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_103_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_103_, 0, v___x_102_);
return v___f_103_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20(void){
_start:
{
lean_object* v___x_104_; lean_object* v___f_105_; 
v___x_104_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_105_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_105_, 0, v___x_104_);
return v___f_105_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21(void){
_start:
{
lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v___f_106_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20);
v___f_107_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___f_107_);
lean_ctor_set(v___x_108_, 1, v___f_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_110_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23));
v___x_113_ = l_Lean_stringToMessageData(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25));
v___x_116_ = l_Lean_stringToMessageData(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27));
v___x_119_ = l_Lean_stringToMessageData(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
v___x_122_ = l_Lean_stringToMessageData(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(lean_object* v_inst_126_, lean_object* v_stx_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; lean_object* v_toApplicative_136_; lean_object* v_toFunctor_137_; lean_object* v_toSeq_138_; lean_object* v_toSeqLeft_139_; lean_object* v_toSeqRight_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_toApplicative_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_382_; 
v___x_135_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1);
v_toApplicative_136_ = lean_ctor_get(v___x_135_, 0);
v_toFunctor_137_ = lean_ctor_get(v_toApplicative_136_, 0);
v_toSeq_138_ = lean_ctor_get(v_toApplicative_136_, 2);
v_toSeqLeft_139_ = lean_ctor_get(v_toApplicative_136_, 3);
v_toSeqRight_140_ = lean_ctor_get(v_toApplicative_136_, 4);
v___f_141_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2));
v___f_142_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_137_, 2);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_143_, 0, v_toFunctor_137_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_144_, 0, v_toFunctor_137_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___f_143_);
lean_ctor_set(v___x_145_, 1, v___f_144_);
lean_inc(v_toSeqRight_140_);
v___f_146_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_146_, 0, v_toSeqRight_140_);
lean_inc(v_toSeqLeft_139_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeqLeft_139_);
lean_inc(v_toSeq_138_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_148_, 0, v_toSeq_138_);
v___x_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_149_, 0, v___x_145_);
lean_ctor_set(v___x_149_, 1, v___f_141_);
lean_ctor_set(v___x_149_, 2, v___f_148_);
lean_ctor_set(v___x_149_, 3, v___f_147_);
lean_ctor_set(v___x_149_, 4, v___f_146_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___f_142_);
v___x_151_ = l_StateRefT_x27_instMonad___redArg(v___x_150_);
v_toApplicative_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v___x_151_, 1);
lean_dec(v_unused_383_);
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_382_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_toApplicative_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_382_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v_toFunctor_156_; lean_object* v_toSeq_157_; lean_object* v_toSeqLeft_158_; lean_object* v_toSeqRight_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_380_; 
v_toFunctor_156_ = lean_ctor_get(v_toApplicative_152_, 0);
v_toSeq_157_ = lean_ctor_get(v_toApplicative_152_, 2);
v_toSeqLeft_158_ = lean_ctor_get(v_toApplicative_152_, 3);
v_toSeqRight_159_ = lean_ctor_get(v_toApplicative_152_, 4);
v_isSharedCheck_380_ = !lean_is_exclusive(v_toApplicative_152_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_toApplicative_152_, 1);
lean_dec(v_unused_381_);
v___x_161_ = v_toApplicative_152_;
v_isShared_162_ = v_isSharedCheck_380_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_toSeqRight_159_);
lean_inc(v_toSeqLeft_158_);
lean_inc(v_toSeq_157_);
lean_inc(v_toFunctor_156_);
lean_dec(v_toApplicative_152_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_380_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___x_172_; 
v___f_163_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4));
v___f_164_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5));
lean_inc_ref(v_toFunctor_156_);
v___f_165_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_165_, 0, v_toFunctor_156_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_166_, 0, v_toFunctor_156_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___f_165_);
lean_ctor_set(v___x_167_, 1, v___f_166_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_168_, 0, v_toSeqRight_159_);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_169_, 0, v_toSeqLeft_158_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_170_, 0, v_toSeq_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 4, v___f_168_);
lean_ctor_set(v___x_161_, 3, v___f_169_);
lean_ctor_set(v___x_161_, 2, v___f_170_);
lean_ctor_set(v___x_161_, 1, v___f_163_);
lean_ctor_set(v___x_161_, 0, v___x_167_);
v___x_172_ = v___x_161_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___f_163_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v___f_170_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v___f_169_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v___f_168_);
v___x_172_ = v_reuseFailAlloc_379_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___f_164_);
lean_ctor_set(v___x_154_, 0, v___x_172_);
v___x_174_ = v___x_154_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___f_164_);
v___x_174_ = v_reuseFailAlloc_378_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v_toApplicative_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_376_; 
v___x_175_ = l_StateRefT_x27_instMonad___redArg(v___x_174_);
v_toApplicative_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v___x_175_, 1);
lean_dec(v_unused_377_);
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_376_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toApplicative_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_376_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_toFunctor_180_; lean_object* v_toSeq_181_; lean_object* v_toSeqLeft_182_; lean_object* v_toSeqRight_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_374_; 
v_toFunctor_180_ = lean_ctor_get(v_toApplicative_176_, 0);
v_toSeq_181_ = lean_ctor_get(v_toApplicative_176_, 2);
v_toSeqLeft_182_ = lean_ctor_get(v_toApplicative_176_, 3);
v_toSeqRight_183_ = lean_ctor_get(v_toApplicative_176_, 4);
v_isSharedCheck_374_ = !lean_is_exclusive(v_toApplicative_176_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_toApplicative_176_, 1);
lean_dec(v_unused_375_);
v___x_185_ = v_toApplicative_176_;
v_isShared_186_ = v_isSharedCheck_374_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_toSeqRight_183_);
lean_inc(v_toSeqLeft_182_);
lean_inc(v_toSeq_181_);
lean_inc(v_toFunctor_180_);
lean_dec(v_toApplicative_176_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_374_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_196_; 
v___f_187_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6));
v___f_188_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7));
lean_inc_ref(v_toFunctor_180_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_189_, 0, v_toFunctor_180_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_190_, 0, v_toFunctor_180_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___f_189_);
lean_ctor_set(v___x_191_, 1, v___f_190_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_192_, 0, v_toSeqRight_183_);
v___f_193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_193_, 0, v_toSeqLeft_182_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_194_, 0, v_toSeq_181_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 4, v___f_192_);
lean_ctor_set(v___x_185_, 3, v___f_193_);
lean_ctor_set(v___x_185_, 2, v___f_194_);
lean_ctor_set(v___x_185_, 1, v___f_187_);
lean_ctor_set(v___x_185_, 0, v___x_191_);
v___x_196_ = v___x_185_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___f_187_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___f_194_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v___f_193_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___f_192_);
v___x_196_ = v_reuseFailAlloc_373_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___f_188_);
lean_ctor_set(v___x_178_, 0, v___x_196_);
v___x_198_ = v___x_178_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___f_188_);
v___x_198_ = v_reuseFailAlloc_372_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v_toMonadQuotation_200_; lean_object* v_toMonadRef_201_; lean_object* v___x_202_; lean_object* v_getMCtx_203_; lean_object* v_modifyMCtx_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_evalExpr_216_; lean_object* v_expectedType_x3f_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_371_; 
v___x_199_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_200_ = lean_ctor_get(v___x_199_, 0);
v_toMonadRef_201_ = lean_ctor_get(v_toMonadQuotation_200_, 0);
v___x_202_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_203_ = lean_ctor_get(v___x_202_, 0);
v_modifyMCtx_204_ = lean_ctor_get(v___x_202_, 1);
v___f_205_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8));
v___x_206_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9));
lean_inc(v_modifyMCtx_204_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_207_, 0, v_modifyMCtx_204_);
lean_closure_set(v___f_207_, 1, v___x_206_);
lean_inc(v_getMCtx_203_);
v___x_208_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_208_, 0, lean_box(0));
lean_closure_set(v___x_208_, 1, lean_box(0));
lean_closure_set(v___x_208_, 2, lean_box(0));
lean_closure_set(v___x_208_, 3, lean_box(0));
lean_closure_set(v___x_208_, 4, v_getMCtx_203_);
v___f_209_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_209_, 0, v___f_207_);
lean_closure_set(v___f_209_, 1, v___f_205_);
v___x_210_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_210_, 0, lean_box(0));
lean_closure_set(v___x_210_, 1, v___x_208_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___f_209_);
v___x_212_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_213_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_201_);
v___x_214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v_toMonadRef_201_);
lean_ctor_set(v___x_214_, 2, v___x_213_);
v___x_215_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22);
v_evalExpr_216_ = lean_ctor_get(v_inst_126_, 0);
v_expectedType_x3f_217_ = lean_ctor_get(v_inst_126_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_inst_126_);
if (v_isSharedCheck_371_ == 0)
{
v___x_219_ = v_inst_126_;
v_isShared_220_ = v_isSharedCheck_371_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_expectedType_x3f_217_);
lean_inc(v_evalExpr_216_);
lean_dec(v_inst_126_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_371_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_toCold_226_; lean_object* v_currRecDepth_227_; lean_object* v_ref_228_; uint16_t v_optionFlags_229_; uint8_t v_suppressElabErrors_230_; uint8_t v_checkDeprecated_231_; uint8_t v_isRecordingDeps_232_; uint8_t v___x_233_; lean_object* v_ref_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_221_ = 1;
v___x_222_ = lean_box(0);
v___x_223_ = lean_box(v___x_221_);
v___x_224_ = lean_box(v___x_221_);
lean_inc(v_expectedType_x3f_217_);
lean_inc(v_stx_127_);
v___x_225_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_225_, 0, v_stx_127_);
lean_closure_set(v___x_225_, 1, v_expectedType_x3f_217_);
lean_closure_set(v___x_225_, 2, v___x_223_);
lean_closure_set(v___x_225_, 3, v___x_224_);
lean_closure_set(v___x_225_, 4, v___x_222_);
v_toCold_226_ = lean_ctor_get(v_a_132_, 0);
v_currRecDepth_227_ = lean_ctor_get(v_a_132_, 1);
v_ref_228_ = lean_ctor_get(v_a_132_, 2);
v_optionFlags_229_ = lean_ctor_get_uint16(v_a_132_, sizeof(void*)*3);
v_suppressElabErrors_230_ = lean_ctor_get_uint8(v_a_132_, sizeof(void*)*3 + 2);
v_checkDeprecated_231_ = lean_ctor_get_uint8(v_a_132_, sizeof(void*)*3 + 3);
v_isRecordingDeps_232_ = lean_ctor_get_uint8(v_a_132_, sizeof(void*)*3 + 4);
v___x_233_ = 1;
v_ref_234_ = l_Lean_replaceRef(v_stx_127_, v_ref_228_);
lean_dec(v_stx_127_);
lean_inc(v_currRecDepth_227_);
lean_inc_ref(v_toCold_226_);
v___x_235_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_235_, 0, v_toCold_226_);
lean_ctor_set(v___x_235_, 1, v_currRecDepth_227_);
lean_ctor_set(v___x_235_, 2, v_ref_234_);
lean_ctor_set_uint16(v___x_235_, sizeof(void*)*3, v_optionFlags_229_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 2, v_suppressElabErrors_230_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 3, v_checkDeprecated_231_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 4, v_isRecordingDeps_232_);
v___x_236_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_225_, v___x_233_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v___x_235_, v_a_133_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_3564__overap_238_; lean_object* v___x_239_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
lean_inc_ref(v___x_198_);
v___x_3564__overap_238_ = l_Lean_instantiateMVars___redArg(v___x_198_, v___x_211_, v_a_237_);
lean_inc(v_a_133_);
lean_inc_ref(v___x_235_);
lean_inc(v_a_131_);
lean_inc_ref(v_a_130_);
lean_inc(v_a_129_);
lean_inc_ref(v_a_128_);
v___x_239_ = lean_apply_7(v___x_3564__overap_238_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v___x_235_, v_a_133_, lean_box(0));
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; uint8_t v___x_343_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v___x_343_ = l_Lean_Expr_hasSorry(v_a_240_);
if (v___x_343_ == 0)
{
v___y_286_ = v_a_128_;
v___y_287_ = v_a_129_;
v___y_288_ = v_a_130_;
v___y_289_ = v_a_131_;
v___y_290_ = v___x_235_;
v___y_291_ = v_a_133_;
goto v___jp_285_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_Expr_hasSyntheticSorry(v_a_240_);
if (v___x_344_ == 0)
{
v___y_324_ = v_a_128_;
v___y_325_ = v_a_129_;
v___y_326_ = v_a_130_;
v___y_327_ = v_a_131_;
v___y_328_ = v___x_235_;
v___y_329_ = v_a_133_;
goto v___jp_323_;
}
else
{
lean_object* v___x_3572__overap_345_; lean_object* v___x_346_; 
v___x_3572__overap_345_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_215_);
lean_inc(v_a_133_);
lean_inc_ref(v___x_235_);
lean_inc(v_a_131_);
lean_inc_ref(v_a_130_);
lean_inc(v_a_129_);
lean_inc_ref(v_a_128_);
v___x_346_ = lean_apply_7(v___x_3572__overap_345_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v___x_235_, v_a_133_, lean_box(0));
if (lean_obj_tag(v___x_346_) == 0)
{
lean_dec_ref_known(v___x_346_, 1);
v___y_324_ = v_a_128_;
v___y_325_ = v_a_129_;
v___y_326_ = v_a_130_;
v___y_327_ = v_a_131_;
v___y_328_ = v___x_235_;
v___y_329_ = v_a_133_;
goto v___jp_323_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_240_);
lean_dec_ref_known(v___x_235_, 3);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref(v_evalExpr_216_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
v___jp_241_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24);
v___x_250_ = l_Lean_indentExpr(v_a_240_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 7);
lean_ctor_set(v___x_219_, 1, v___x_250_);
lean_ctor_set(v___x_219_, 0, v___x_249_);
v___x_252_ = v___x_219_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_3566__overap_254_; lean_object* v___x_255_; 
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___y_248_);
v___x_3566__overap_254_ = l_Lean_throwError___redArg(v___x_198_, v___x_214_, v___x_253_);
lean_inc(v___y_242_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_244_);
v___x_255_ = lean_apply_7(v___x_3566__overap_254_, v___y_244_, v___y_247_, v___y_246_, v___y_243_, v___y_245_, v___y_242_, lean_box(0));
return v___x_255_;
}
}
v___jp_257_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
lean_inc(v_a_240_);
v___x_265_ = lean_apply_6(v_evalExpr_216_, v_a_240_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, lean_box(0));
if (lean_obj_tag(v___x_265_) == 0)
{
lean_dec_ref(v___y_262_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
return v___x_265_;
}
else
{
lean_object* v_a_266_; uint8_t v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
v___x_267_ = l_Lean_Exception_isInterrupt(v_a_266_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
lean_inc(v_a_266_);
v___x_268_ = l_Lean_Exception_isRuntime(v_a_266_);
if (v___x_268_ == 0)
{
if (lean_obj_tag(v_a_266_) == 0)
{
lean_dec_ref_known(v_a_266_, 2);
lean_dec_ref(v___y_262_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
return v___x_265_;
}
else
{
lean_object* v_id_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_283_; 
v_id_269_ = lean_ctor_get(v_a_266_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_a_266_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_a_266_, 1);
lean_dec(v_unused_284_);
v___x_271_ = v_a_266_;
v_isShared_272_ = v_isSharedCheck_283_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_id_269_);
lean_dec(v_a_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_283_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint8_t v___x_273_; 
v___x_273_ = l_Lean_instBEqInternalExceptionId_beq(v___x_264_, v_id_269_);
lean_dec(v_id_269_);
if (v___x_273_ == 0)
{
lean_del_object(v___x_271_);
lean_dec_ref(v___y_262_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
return v___x_265_;
}
else
{
lean_dec_ref_known(v___x_265_, 1);
if (lean_obj_tag(v_expectedType_x3f_217_) == 1)
{
lean_object* v_val_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_val_274_ = lean_ctor_get(v_expectedType_x3f_217_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v_expectedType_x3f_217_, 1);
v___x_275_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26);
v___x_276_ = l_Lean_MessageData_ofExpr(v_val_274_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 7);
lean_ctor_set(v___x_271_, 1, v___x_276_);
lean_ctor_set(v___x_271_, 0, v___x_275_);
v___x_278_ = v___x_271_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_276_);
v___x_278_ = v_reuseFailAlloc_281_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___y_242_ = v___y_263_;
v___y_243_ = v___y_261_;
v___y_244_ = v___y_258_;
v___y_245_ = v___y_262_;
v___y_246_ = v___y_260_;
v___y_247_ = v___y_259_;
v___y_248_ = v___x_280_;
goto v___jp_241_;
}
}
else
{
lean_object* v___x_282_; 
lean_del_object(v___x_271_);
lean_dec(v_expectedType_x3f_217_);
v___x_282_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_242_ = v___y_263_;
v___y_243_ = v___y_261_;
v___y_244_ = v___y_258_;
v___y_245_ = v___y_262_;
v___y_246_ = v___y_260_;
v___y_247_ = v___y_259_;
v___y_248_ = v___x_282_;
goto v___jp_241_;
}
}
}
}
}
else
{
lean_dec(v_a_266_);
lean_dec_ref(v___y_262_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
return v___x_265_;
}
}
else
{
lean_dec(v_a_266_);
lean_dec_ref(v___y_262_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
return v___x_265_;
}
}
}
v___jp_285_:
{
lean_object* v___x_292_; 
lean_inc(v_a_240_);
v___x_292_ = l_Lean_Meta_getMVars(v_a_240_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_293_, v___x_222_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v_a_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; uint8_t v___x_296_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = lean_unbox(v_a_295_);
lean_dec(v_a_295_);
if (v___x_296_ == 0)
{
v___y_258_ = v___y_286_;
v___y_259_ = v___y_287_;
v___y_260_ = v___y_288_;
v___y_261_ = v___y_289_;
v___y_262_ = v___y_290_;
v___y_263_ = v___y_291_;
goto v___jp_257_;
}
else
{
lean_object* v___x_3568__overap_297_; lean_object* v___x_298_; 
v___x_3568__overap_297_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_215_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
lean_inc(v___y_289_);
lean_inc_ref(v___y_288_);
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
v___x_298_ = lean_apply_7(v___x_3568__overap_297_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, lean_box(0));
if (lean_obj_tag(v___x_298_) == 0)
{
lean_dec_ref_known(v___x_298_, 1);
v___y_258_ = v___y_286_;
v___y_259_ = v___y_287_;
v___y_260_ = v___y_288_;
v___y_261_ = v___y_289_;
v___y_262_ = v___y_290_;
v___y_263_ = v___y_291_;
goto v___jp_257_;
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v___y_290_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref(v_evalExpr_216_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v___y_290_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref(v_evalExpr_216_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
v_a_307_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_294_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_294_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec_ref(v___y_290_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref(v_evalExpr_216_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
v_a_315_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_292_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_292_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
v___jp_323_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_3570__overap_333_; lean_object* v___x_334_; 
v___x_330_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32);
lean_inc(v_a_240_);
v___x_331_ = l_Lean_indentExpr(v_a_240_);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_inc_ref(v___x_214_);
lean_inc_ref(v___x_198_);
v___x_3570__overap_333_ = l_Lean_throwError___redArg(v___x_198_, v___x_214_, v___x_332_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
v___x_334_ = lean_apply_7(v___x_3570__overap_333_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, lean_box(0));
if (lean_obj_tag(v___x_334_) == 0)
{
lean_dec_ref_known(v___x_334_, 1);
v___y_286_ = v___y_324_;
v___y_287_ = v___y_325_;
v___y_288_ = v___y_326_;
v___y_289_ = v___y_327_;
v___y_290_ = v___y_328_;
v___y_291_ = v___y_329_;
goto v___jp_285_;
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec_ref(v___y_328_);
lean_dec(v_a_240_);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref(v_evalExpr_216_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref_known(v___x_235_, 3);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref(v_evalExpr_216_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref(v___x_198_);
v_a_355_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_239_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_239_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref_known(v___x_235_, 3);
lean_del_object(v___x_219_);
lean_dec(v_expectedType_x3f_217_);
lean_dec_ref(v_evalExpr_216_);
lean_dec_ref_known(v___x_214_, 3);
lean_dec_ref_known(v___x_211_, 2);
lean_dec_ref(v___x_198_);
v_a_363_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_236_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_236_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___boxed(lean_object* v_inst_384_, lean_object* v_stx_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_384_, v_stx_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab(lean_object* v_00_u03b1_394_, lean_object* v_inst_395_, lean_object* v_stx_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_395_, v_stx_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___boxed(lean_object* v_00_u03b1_405_, lean_object* v_inst_406_, lean_object* v_stx_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_ConfigEval_evalExprWithElab(v_00_u03b1_405_, v_inst_406_, v_stx_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_stx_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_evalTerm_426_; lean_object* v_toCold_427_; lean_object* v_currRecDepth_428_; lean_object* v_ref_429_; uint16_t v_optionFlags_430_; uint8_t v_suppressElabErrors_431_; uint8_t v_checkDeprecated_432_; uint8_t v_isRecordingDeps_433_; lean_object* v___x_434_; lean_object* v_ref_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_evalTerm_426_ = lean_ctor_get(v_inst_416_, 0);
lean_inc_ref(v_evalTerm_426_);
lean_dec_ref(v_inst_416_);
v_toCold_427_ = lean_ctor_get(v_a_423_, 0);
v_currRecDepth_428_ = lean_ctor_get(v_a_423_, 1);
v_ref_429_ = lean_ctor_get(v_a_423_, 2);
v_optionFlags_430_ = lean_ctor_get_uint16(v_a_423_, sizeof(void*)*3);
v_suppressElabErrors_431_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*3 + 2);
v_checkDeprecated_432_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*3 + 3);
v_isRecordingDeps_433_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*3 + 4);
v___x_434_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_435_ = l_Lean_replaceRef(v_stx_418_, v_ref_429_);
lean_inc(v_currRecDepth_428_);
lean_inc_ref(v_toCold_427_);
v___x_436_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_436_, 0, v_toCold_427_);
lean_ctor_set(v___x_436_, 1, v_currRecDepth_428_);
lean_ctor_set(v___x_436_, 2, v_ref_435_);
lean_ctor_set_uint16(v___x_436_, sizeof(void*)*3, v_optionFlags_430_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*3 + 2, v_suppressElabErrors_431_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*3 + 3, v_checkDeprecated_432_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*3 + 4, v_isRecordingDeps_433_);
lean_inc(v_a_424_);
lean_inc_ref(v___x_436_);
lean_inc(v_a_422_);
lean_inc_ref(v_a_421_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_stx_418_);
v___x_437_ = lean_apply_8(v_evalTerm_426_, v_stx_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v___x_436_, v_a_424_, lean_box(0));
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref_known(v___x_436_, 3);
lean_dec(v_stx_418_);
lean_dec_ref(v_inst_417_);
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_fst_442_; lean_object* v___x_444_; 
v_fst_442_ = lean_ctor_get(v_a_438_, 0);
lean_inc(v_fst_442_);
lean_dec(v_a_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_fst_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fst_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_459_; 
v_a_447_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_459_ == 0)
{
v___x_449_ = v___x_437_;
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_437_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
lean_inc(v_a_447_);
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_458_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
uint8_t v___x_453_; 
v___x_453_ = l_Lean_Exception_isInterrupt(v_a_447_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
lean_inc(v_a_447_);
v___x_454_ = l_Lean_Exception_isRuntime(v_a_447_);
if (v___x_454_ == 0)
{
if (lean_obj_tag(v_a_447_) == 0)
{
lean_dec_ref_known(v_a_447_, 2);
lean_dec_ref_known(v___x_436_, 3);
lean_dec(v_stx_418_);
lean_dec_ref(v_inst_417_);
return v___x_452_;
}
else
{
lean_object* v_id_455_; uint8_t v___x_456_; 
v_id_455_ = lean_ctor_get(v_a_447_, 0);
lean_inc(v_id_455_);
lean_dec_ref_known(v_a_447_, 2);
v___x_456_ = l_Lean_instBEqInternalExceptionId_beq(v___x_434_, v_id_455_);
lean_dec(v_id_455_);
if (v___x_456_ == 0)
{
lean_dec_ref_known(v___x_436_, 3);
lean_dec(v_stx_418_);
lean_dec_ref(v_inst_417_);
return v___x_452_;
}
else
{
lean_object* v___x_457_; 
lean_dec_ref(v___x_452_);
v___x_457_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_417_, v_stx_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v___x_436_, v_a_424_);
lean_dec_ref_known(v___x_436_, 3);
return v___x_457_;
}
}
}
else
{
lean_dec(v_a_447_);
lean_dec_ref_known(v___x_436_, 3);
lean_dec(v_stx_418_);
lean_dec_ref(v_inst_417_);
return v___x_452_;
}
}
else
{
lean_dec(v_a_447_);
lean_dec_ref_known(v___x_436_, 3);
lean_dec(v_stx_418_);
lean_dec_ref(v_inst_417_);
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_stx_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_460_, v_inst_461_, v_stx_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(lean_object* v_00_u03b1_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_stx_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_472_, v_inst_473_, v_stx_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___boxed(lean_object* v_00_u03b1_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_stx_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(v_00_u03b1_483_, v_inst_484_, v_inst_485_, v_stx_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4));
lean_inc(v_x_513_);
v___x_515_ = l_Lean_Syntax_isOfKind(v_x_513_, v___x_514_);
if (v___x_515_ == 0)
{
return v_x_513_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Lean_Syntax_getArg(v_x_513_, v___x_516_);
v___x_518_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6));
lean_inc(v___x_517_);
v___x_519_ = l_Lean_Syntax_isOfKind(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v___x_517_);
return v_x_513_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = l_Lean_Syntax_getArg(v___x_517_, v___x_520_);
lean_dec(v___x_517_);
v___x_522_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8));
lean_inc(v___x_521_);
v___x_523_ = l_Lean_Syntax_isOfKind(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_dec(v___x_521_);
return v_x_513_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = l_Lean_Syntax_getArg(v___x_521_, v___x_516_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v___x_526_ = l_Lean_Syntax_matchesIdent(v___x_524_, v___x_525_);
lean_dec(v___x_524_);
if (v___x_526_ == 0)
{
return v_x_513_;
}
else
{
lean_object* v_t_527_; 
v_t_527_ = l_Lean_Syntax_getArg(v_x_513_, v___x_520_);
lean_dec(v_x_513_);
v_x_513_ = v_t_527_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(lean_object* v_expectedType_x3f_529_, lean_object* v_f_530_, lean_object* v_stx_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_toCold_539_; lean_object* v_currRecDepth_540_; lean_object* v_ref_541_; uint16_t v_optionFlags_542_; uint8_t v_suppressElabErrors_543_; uint8_t v_checkDeprecated_544_; uint8_t v_isRecordingDeps_545_; lean_object* v___x_546_; lean_object* v_ref_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_toCold_539_ = lean_ctor_get(v_a_536_, 0);
v_currRecDepth_540_ = lean_ctor_get(v_a_536_, 1);
v_ref_541_ = lean_ctor_get(v_a_536_, 2);
v_optionFlags_542_ = lean_ctor_get_uint16(v_a_536_, sizeof(void*)*3);
v_suppressElabErrors_543_ = lean_ctor_get_uint8(v_a_536_, sizeof(void*)*3 + 2);
v_checkDeprecated_544_ = lean_ctor_get_uint8(v_a_536_, sizeof(void*)*3 + 3);
v_isRecordingDeps_545_ = lean_ctor_get_uint8(v_a_536_, sizeof(void*)*3 + 4);
lean_inc(v_stx_531_);
v___x_546_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_531_);
v_ref_547_ = l_Lean_replaceRef(v_stx_531_, v_ref_541_);
lean_inc(v_currRecDepth_540_);
lean_inc_ref(v_toCold_539_);
v___x_548_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_548_, 0, v_toCold_539_);
lean_ctor_set(v___x_548_, 1, v_currRecDepth_540_);
lean_ctor_set(v___x_548_, 2, v_ref_547_);
lean_ctor_set_uint16(v___x_548_, sizeof(void*)*3, v_optionFlags_542_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 2, v_suppressElabErrors_543_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 3, v_checkDeprecated_544_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*3 + 4, v_isRecordingDeps_545_);
lean_inc(v_a_537_);
lean_inc(v_a_535_);
lean_inc_ref(v_a_534_);
lean_inc(v_a_533_);
lean_inc_ref(v_a_532_);
v___x_549_ = lean_apply_8(v_f_530_, v___x_546_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v___x_548_, v_a_537_, lean_box(0));
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_581_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_581_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_581_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_581_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_snd_554_; lean_object* v___x_555_; lean_object* v_infoState_556_; uint8_t v_enabled_557_; 
v_snd_554_ = lean_ctor_get(v_a_550_, 1);
v___x_555_ = lean_st_ref_get(v_a_537_);
v_infoState_556_ = lean_ctor_get(v___x_555_, 8);
lean_inc_ref(v_infoState_556_);
lean_dec(v___x_555_);
v_enabled_557_ = lean_ctor_get_uint8(v_infoState_556_, sizeof(void*)*3);
lean_dec_ref(v_infoState_556_);
if (v_enabled_557_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v_stx_531_);
lean_dec(v_expectedType_x3f_529_);
if (v_isShared_553_ == 0)
{
v___x_559_ = v___x_552_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_550_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; 
lean_del_object(v___x_552_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_box(0);
v___x_563_ = 0;
lean_inc(v_snd_554_);
v___x_564_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_531_, v_snd_554_, v_expectedType_x3f_529_, v___x_561_, v___x_562_, v___x_563_, v___x_563_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_564_, 0);
lean_dec(v_unused_572_);
v___x_566_ = v___x_564_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_dec(v___x_564_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_a_550_);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_550_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_a_550_);
v_a_573_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_564_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_564_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_531_);
lean_dec(v_expectedType_x3f_529_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg___boxed(lean_object* v_expectedType_x3f_582_, lean_object* v_f_583_, lean_object* v_stx_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(v_expectedType_x3f_582_, v_f_583_, v_stx_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(lean_object* v_00_u03b1_593_, lean_object* v_expectedType_x3f_594_, lean_object* v_f_595_, lean_object* v_stx_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_toCold_604_; lean_object* v_currRecDepth_605_; lean_object* v_ref_606_; uint16_t v_optionFlags_607_; uint8_t v_suppressElabErrors_608_; uint8_t v_checkDeprecated_609_; uint8_t v_isRecordingDeps_610_; lean_object* v___x_611_; lean_object* v_ref_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_toCold_604_ = lean_ctor_get(v_a_601_, 0);
v_currRecDepth_605_ = lean_ctor_get(v_a_601_, 1);
v_ref_606_ = lean_ctor_get(v_a_601_, 2);
v_optionFlags_607_ = lean_ctor_get_uint16(v_a_601_, sizeof(void*)*3);
v_suppressElabErrors_608_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 2);
v_checkDeprecated_609_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 3);
v_isRecordingDeps_610_ = lean_ctor_get_uint8(v_a_601_, sizeof(void*)*3 + 4);
lean_inc(v_stx_596_);
v___x_611_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_596_);
v_ref_612_ = l_Lean_replaceRef(v_stx_596_, v_ref_606_);
lean_inc(v_currRecDepth_605_);
lean_inc_ref(v_toCold_604_);
v___x_613_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_613_, 0, v_toCold_604_);
lean_ctor_set(v___x_613_, 1, v_currRecDepth_605_);
lean_ctor_set(v___x_613_, 2, v_ref_612_);
lean_ctor_set_uint16(v___x_613_, sizeof(void*)*3, v_optionFlags_607_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 2, v_suppressElabErrors_608_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 3, v_checkDeprecated_609_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 4, v_isRecordingDeps_610_);
lean_inc(v_a_602_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
v___x_614_ = lean_apply_8(v_f_595_, v___x_611_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v___x_613_, v_a_602_, lean_box(0));
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_646_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_646_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_646_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_646_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_snd_619_; lean_object* v___x_620_; lean_object* v_infoState_621_; uint8_t v_enabled_622_; 
v_snd_619_ = lean_ctor_get(v_a_615_, 1);
v___x_620_ = lean_st_ref_get(v_a_602_);
v_infoState_621_ = lean_ctor_get(v___x_620_, 8);
lean_inc_ref(v_infoState_621_);
lean_dec(v___x_620_);
v_enabled_622_ = lean_ctor_get_uint8(v_infoState_621_, sizeof(void*)*3);
lean_dec_ref(v_infoState_621_);
if (v_enabled_622_ == 0)
{
lean_object* v___x_624_; 
lean_dec(v_stx_596_);
lean_dec(v_expectedType_x3f_594_);
if (v_isShared_618_ == 0)
{
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_615_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_617_);
v___x_626_ = lean_box(0);
v___x_627_ = lean_box(0);
v___x_628_ = 0;
lean_inc(v_snd_619_);
v___x_629_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_596_, v_snd_619_, v_expectedType_x3f_594_, v___x_626_, v___x_627_, v___x_628_, v___x_628_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v___x_629_, 0);
lean_dec(v_unused_637_);
v___x_631_ = v___x_629_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_dec(v___x_629_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_a_615_);
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_615_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_a_615_);
v_a_638_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_629_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_596_);
lean_dec(v_expectedType_x3f_594_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___boxed(lean_object* v_00_u03b1_647_, lean_object* v_expectedType_x3f_648_, lean_object* v_f_649_, lean_object* v_stx_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(v_00_u03b1_647_, v_expectedType_x3f_648_, v_f_649_, v_stx_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(lean_object* v_inst_659_, lean_object* v_f_660_, lean_object* v_stx_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_toExpr_669_; lean_object* v_toTypeExpr_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_729_; 
v_toExpr_669_ = lean_ctor_get(v_inst_659_, 0);
v_toTypeExpr_670_ = lean_ctor_get(v_inst_659_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_inst_659_);
if (v_isSharedCheck_729_ == 0)
{
v___x_672_ = v_inst_659_;
v_isShared_673_ = v_isSharedCheck_729_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_toTypeExpr_670_);
lean_inc(v_toExpr_669_);
lean_dec(v_inst_659_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_729_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_toCold_674_; lean_object* v_currRecDepth_675_; lean_object* v_ref_676_; uint16_t v_optionFlags_677_; uint8_t v_suppressElabErrors_678_; uint8_t v_checkDeprecated_679_; uint8_t v_isRecordingDeps_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_ref_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_toCold_674_ = lean_ctor_get(v_a_666_, 0);
v_currRecDepth_675_ = lean_ctor_get(v_a_666_, 1);
v_ref_676_ = lean_ctor_get(v_a_666_, 2);
v_optionFlags_677_ = lean_ctor_get_uint16(v_a_666_, sizeof(void*)*3);
v_suppressElabErrors_678_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*3 + 2);
v_checkDeprecated_679_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*3 + 3);
v_isRecordingDeps_680_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*3 + 4);
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_toTypeExpr_670_);
lean_inc(v_stx_661_);
v___x_682_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_661_);
v_ref_683_ = l_Lean_replaceRef(v_stx_661_, v_ref_676_);
lean_inc(v_currRecDepth_675_);
lean_inc_ref(v_toCold_674_);
v___x_684_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_684_, 0, v_toCold_674_);
lean_ctor_set(v___x_684_, 1, v_currRecDepth_675_);
lean_ctor_set(v___x_684_, 2, v_ref_683_);
lean_ctor_set_uint16(v___x_684_, sizeof(void*)*3, v_optionFlags_677_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*3 + 2, v_suppressElabErrors_678_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*3 + 3, v_checkDeprecated_679_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*3 + 4, v_isRecordingDeps_680_);
lean_inc(v_a_667_);
lean_inc(v_a_665_);
lean_inc_ref(v_a_664_);
lean_inc(v_a_663_);
lean_inc_ref(v_a_662_);
v___x_685_ = lean_apply_8(v_f_660_, v___x_682_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v___x_684_, v_a_667_, lean_box(0));
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_720_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_720_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_720_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_720_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
lean_inc(v_a_686_);
v___x_690_ = lean_apply_1(v_toExpr_669_, v_a_686_);
lean_inc_ref(v___x_690_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v___x_690_);
lean_ctor_set(v___x_672_, 0, v_a_686_);
v___x_692_ = v___x_672_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_686_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_719_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v_infoState_694_; uint8_t v_enabled_695_; 
v___x_693_ = lean_st_ref_get(v_a_667_);
v_infoState_694_ = lean_ctor_get(v___x_693_, 8);
lean_inc_ref(v_infoState_694_);
lean_dec(v___x_693_);
v_enabled_695_ = lean_ctor_get_uint8(v_infoState_694_, sizeof(void*)*3);
lean_dec_ref(v_infoState_694_);
if (v_enabled_695_ == 0)
{
lean_object* v___x_697_; 
lean_dec_ref(v___x_690_);
lean_dec_ref_known(v___x_681_, 1);
lean_dec(v_stx_661_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_692_);
v___x_697_ = v___x_688_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; 
lean_del_object(v___x_688_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_box(0);
v___x_701_ = 0;
v___x_702_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_661_, v___x_690_, v___x_681_, v___x_699_, v___x_700_, v___x_701_, v___x_701_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_702_, 0);
lean_dec(v_unused_710_);
v___x_704_ = v___x_702_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_dec(v___x_702_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_692_);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_692_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___x_692_);
v_a_711_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_702_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_702_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref_known(v___x_681_, 1);
lean_del_object(v___x_672_);
lean_dec_ref(v_toExpr_669_);
lean_dec(v_stx_661_);
v_a_721_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_685_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_685_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg___boxed(lean_object* v_inst_730_, lean_object* v_f_731_, lean_object* v_stx_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(v_inst_730_, v_f_731_, v_stx_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(lean_object* v_00_u03b1_741_, lean_object* v_inst_742_, lean_object* v_f_743_, lean_object* v_stx_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_toExpr_752_; lean_object* v_toTypeExpr_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_812_; 
v_toExpr_752_ = lean_ctor_get(v_inst_742_, 0);
v_toTypeExpr_753_ = lean_ctor_get(v_inst_742_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_inst_742_);
if (v_isSharedCheck_812_ == 0)
{
v___x_755_ = v_inst_742_;
v_isShared_756_ = v_isSharedCheck_812_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_toTypeExpr_753_);
lean_inc(v_toExpr_752_);
lean_dec(v_inst_742_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_812_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_toCold_757_; lean_object* v_currRecDepth_758_; lean_object* v_ref_759_; uint16_t v_optionFlags_760_; uint8_t v_suppressElabErrors_761_; uint8_t v_checkDeprecated_762_; uint8_t v_isRecordingDeps_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_ref_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_toCold_757_ = lean_ctor_get(v_a_749_, 0);
v_currRecDepth_758_ = lean_ctor_get(v_a_749_, 1);
v_ref_759_ = lean_ctor_get(v_a_749_, 2);
v_optionFlags_760_ = lean_ctor_get_uint16(v_a_749_, sizeof(void*)*3);
v_suppressElabErrors_761_ = lean_ctor_get_uint8(v_a_749_, sizeof(void*)*3 + 2);
v_checkDeprecated_762_ = lean_ctor_get_uint8(v_a_749_, sizeof(void*)*3 + 3);
v_isRecordingDeps_763_ = lean_ctor_get_uint8(v_a_749_, sizeof(void*)*3 + 4);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v_toTypeExpr_753_);
lean_inc(v_stx_744_);
v___x_765_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_744_);
v_ref_766_ = l_Lean_replaceRef(v_stx_744_, v_ref_759_);
lean_inc(v_currRecDepth_758_);
lean_inc_ref(v_toCold_757_);
v___x_767_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_767_, 0, v_toCold_757_);
lean_ctor_set(v___x_767_, 1, v_currRecDepth_758_);
lean_ctor_set(v___x_767_, 2, v_ref_766_);
lean_ctor_set_uint16(v___x_767_, sizeof(void*)*3, v_optionFlags_760_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*3 + 2, v_suppressElabErrors_761_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*3 + 3, v_checkDeprecated_762_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*3 + 4, v_isRecordingDeps_763_);
lean_inc(v_a_750_);
lean_inc(v_a_748_);
lean_inc_ref(v_a_747_);
lean_inc(v_a_746_);
lean_inc_ref(v_a_745_);
v___x_768_ = lean_apply_8(v_f_743_, v___x_765_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v___x_767_, v_a_750_, lean_box(0));
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_803_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_803_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_803_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_803_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_inc(v_a_769_);
v___x_773_ = lean_apply_1(v_toExpr_752_, v_a_769_);
lean_inc_ref(v___x_773_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_773_);
lean_ctor_set(v___x_755_, 0, v_a_769_);
v___x_775_ = v___x_755_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_769_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_802_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v_infoState_777_; uint8_t v_enabled_778_; 
v___x_776_ = lean_st_ref_get(v_a_750_);
v_infoState_777_ = lean_ctor_get(v___x_776_, 8);
lean_inc_ref(v_infoState_777_);
lean_dec(v___x_776_);
v_enabled_778_ = lean_ctor_get_uint8(v_infoState_777_, sizeof(void*)*3);
lean_dec_ref(v_infoState_777_);
if (v_enabled_778_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v___x_773_);
lean_dec_ref_known(v___x_764_, 1);
lean_dec(v_stx_744_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_780_ = v___x_771_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; 
lean_del_object(v___x_771_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_box(0);
v___x_784_ = 0;
v___x_785_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_744_, v___x_773_, v___x_764_, v___x_782_, v___x_783_, v___x_784_, v___x_784_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_785_, 0);
lean_dec(v_unused_793_);
v___x_787_ = v___x_785_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_dec(v___x_785_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_775_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_775_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v___x_775_);
v_a_794_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_785_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_785_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref_known(v___x_764_, 1);
lean_del_object(v___x_755_);
lean_dec_ref(v_toExpr_752_);
lean_dec(v_stx_744_);
v_a_804_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_768_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_768_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___boxed(lean_object* v_00_u03b1_813_, lean_object* v_inst_814_, lean_object* v_f_815_, lean_object* v_stx_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(v_00_u03b1_813_, v_inst_814_, v_f_815_, v_stx_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(lean_object* v_msgData_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_env_832_; uint8_t v___x_833_; lean_object* v_env_834_; lean_object* v___x_835_; lean_object* v_toCold_836_; lean_object* v_mctx_837_; lean_object* v_lctx_838_; lean_object* v_options_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_831_ = lean_st_ref_get(v___y_829_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
v___x_833_ = 0;
v_env_834_ = l_Lean_Environment_setRecordingDeps(v_env_832_, v___x_833_);
v___x_835_ = lean_st_ref_get(v___y_827_);
v_toCold_836_ = lean_ctor_get(v___y_828_, 0);
v_mctx_837_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_mctx_837_);
lean_dec(v___x_835_);
v_lctx_838_ = lean_ctor_get(v___y_826_, 2);
v_options_839_ = lean_ctor_get(v_toCold_836_, 2);
lean_inc_ref(v_options_839_);
lean_inc_ref(v_lctx_838_);
v___x_840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_840_, 0, v_env_834_);
lean_ctor_set(v___x_840_, 1, v_mctx_837_);
lean_ctor_set(v___x_840_, 2, v_lctx_838_);
lean_ctor_set(v___x_840_, 3, v_options_839_);
v___x_841_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_msgData_825_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(lean_object* v_msgData_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(lean_object* v_msg_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_ref_856_; lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_866_; 
v_ref_856_ = lean_ctor_get(v___y_853_, 2);
v___x_857_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_866_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_inc(v_ref_856_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_ref_856_);
lean_ctor_set(v___x_862_, 1, v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 1);
lean_ctor_set(v___x_860_, 0, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg___boxed(lean_object* v_msg_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(lean_object* v_f_877_, lean_object* v_e_878_, lean_object* v_errMsg_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___y_887_; lean_object* v_a_888_; lean_object* v___x_905_; 
v___x_885_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_inc_ref(v_f_877_);
lean_inc(v_a_883_);
lean_inc_ref(v_a_882_);
lean_inc(v_a_881_);
lean_inc_ref(v_a_880_);
lean_inc_ref(v_e_878_);
v___x_905_ = lean_apply_6(v_f_877_, v_e_878_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, lean_box(0));
if (lean_obj_tag(v___x_905_) == 0)
{
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
lean_dec_ref(v_f_877_);
return v___x_905_;
}
else
{
lean_object* v_a_906_; uint8_t v___x_907_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
v___x_907_ = l_Lean_Exception_isInterrupt(v_a_906_);
if (v___x_907_ == 0)
{
uint8_t v___x_908_; 
lean_inc(v_a_906_);
v___x_908_ = l_Lean_Exception_isRuntime(v_a_906_);
if (v___x_908_ == 0)
{
if (lean_obj_tag(v_a_906_) == 0)
{
lean_dec_ref_known(v_a_906_, 2);
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
lean_dec_ref(v_f_877_);
return v___x_905_;
}
else
{
lean_object* v_id_909_; uint8_t v___x_910_; 
v_id_909_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_id_909_);
lean_dec_ref_known(v_a_906_, 2);
v___x_910_ = l_Lean_instBEqInternalExceptionId_beq(v___x_885_, v_id_909_);
lean_dec(v_id_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
lean_dec_ref(v_f_877_);
return v___x_905_;
}
else
{
lean_object* v___x_911_; 
lean_dec_ref_known(v___x_905_, 1);
lean_inc(v_a_883_);
lean_inc_ref(v_a_882_);
lean_inc(v_a_881_);
lean_inc_ref(v_a_880_);
lean_inc_ref(v_e_878_);
v___x_911_ = lean_whnf(v_e_878_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
lean_inc(v_a_883_);
lean_inc_ref(v_a_882_);
lean_inc(v_a_881_);
lean_inc_ref(v_a_880_);
v___x_913_ = lean_apply_6(v_f_877_, v_a_912_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, lean_box(0));
if (lean_obj_tag(v___x_913_) == 0)
{
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
return v___x_913_;
}
else
{
lean_object* v_a_914_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
v___y_887_ = v___x_913_;
v_a_888_ = v_a_914_;
goto v___jp_886_;
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v_f_877_);
v_a_915_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_911_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_911_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
lean_inc(v_a_915_);
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
v___y_887_ = v___x_920_;
v_a_888_ = v_a_915_;
goto v___jp_886_;
}
}
}
}
}
}
else
{
lean_dec(v_a_906_);
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
lean_dec_ref(v_f_877_);
return v___x_905_;
}
}
else
{
lean_dec(v_a_906_);
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
lean_dec_ref(v_f_877_);
return v___x_905_;
}
}
v___jp_886_:
{
uint8_t v___x_889_; 
v___x_889_ = l_Lean_Exception_isInterrupt(v_a_888_);
if (v___x_889_ == 0)
{
uint8_t v___x_890_; 
lean_inc_ref(v_a_888_);
v___x_890_ = l_Lean_Exception_isRuntime(v_a_888_);
if (v___x_890_ == 0)
{
if (lean_obj_tag(v_a_888_) == 0)
{
lean_dec_ref_known(v_a_888_, 2);
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
return v___y_887_;
}
else
{
lean_object* v_id_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_903_; 
v_id_891_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_a_888_, 1);
lean_dec(v_unused_904_);
v___x_893_ = v_a_888_;
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_id_891_);
lean_dec(v_a_888_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_instBEqInternalExceptionId_beq(v___x_885_, v_id_891_);
lean_dec(v_id_891_);
if (v___x_895_ == 0)
{
lean_del_object(v___x_893_);
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
return v___y_887_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec_ref(v___y_887_);
v___x_896_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1);
v___x_897_ = l_Lean_indentExpr(v_e_878_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 7);
lean_ctor_set(v___x_893_, 1, v___x_897_);
lean_ctor_set(v___x_893_, 0, v___x_896_);
v___x_899_ = v___x_893_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_902_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_errMsg_879_);
v___x_901_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v___x_900_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
return v___x_901_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_888_);
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
return v___y_887_;
}
}
else
{
lean_dec_ref(v_a_888_);
lean_dec_ref(v_errMsg_879_);
lean_dec_ref(v_e_878_);
return v___y_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___boxed(lean_object* v_f_923_, lean_object* v_e_924_, lean_object* v_errMsg_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_923_, v_e_924_, v_errMsg_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(lean_object* v_00_u03b1_932_, lean_object* v_f_933_, lean_object* v_e_934_, lean_object* v_errMsg_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_933_, v_e_934_, v_errMsg_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___boxed(lean_object* v_00_u03b1_942_, lean_object* v_f_943_, lean_object* v_e_944_, lean_object* v_errMsg_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(v_00_u03b1_942_, v_f_943_, v_e_944_, v_errMsg_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(lean_object* v_00_u03b1_952_, lean_object* v_msg_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___boxed(lean_object* v_00_u03b1_960_, lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(v_00_u03b1_960_, v_msg_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_967_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object* v_item_968_){
_start:
{
lean_object* v_optionComps_969_; uint8_t v___x_970_; 
v_optionComps_969_ = lean_ctor_get(v_item_968_, 5);
v___x_970_ = l_List_isEmpty___redArg(v_optionComps_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(lean_object* v_item_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_971_);
lean_dec_ref(v_item_971_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root(lean_object* v_item_974_){
_start:
{
lean_object* v_optionComps_975_; 
v_optionComps_975_ = lean_ctor_get(v_item_974_, 5);
if (lean_obj_tag(v_optionComps_975_) == 1)
{
lean_object* v_head_976_; 
v_head_976_ = lean_ctor_get(v_optionComps_975_, 0);
lean_inc(v_head_976_);
return v_head_976_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = lean_box(0);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(lean_object* v_item_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_978_);
lean_dec_ref(v_item_978_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object* v_item_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_980_);
v___x_982_ = l_Lean_Syntax_getId(v___x_981_);
lean_dec(v___x_981_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_str_983_; 
v_str_983_ = lean_ctor_get(v___x_982_, 1);
lean_inc_ref(v_str_983_);
lean_dec_ref_known(v___x_982_, 2);
return v_str_983_;
}
else
{
lean_object* v___x_984_; 
lean_dec(v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(lean_object* v_item_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_985_);
lean_dec_ref(v_item_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(lean_object* v_item_987_){
_start:
{
lean_object* v_prevOptionComps_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_prevOptionComps_988_ = lean_ctor_get(v_item_987_, 6);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = l_List_get_x3fInternal___redArg(v_prevOptionComps_988_, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(lean_object* v_item_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(v_item_991_);
lean_dec_ref(v_item_991_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(lean_object* v_item_993_){
_start:
{
lean_object* v_prevOptionComps_994_; 
v_prevOptionComps_994_ = lean_ctor_get(v_item_993_, 6);
if (lean_obj_tag(v_prevOptionComps_994_) == 1)
{
lean_object* v_head_995_; 
v_head_995_ = lean_ctor_get(v_prevOptionComps_994_, 0);
lean_inc(v_head_995_);
return v_head_995_;
}
else
{
lean_object* v___x_996_; 
v___x_996_ = lean_box(0);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(lean_object* v_item_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_997_);
lean_dec_ref(v_item_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
return v_x_999_;
}
else
{
lean_object* v_head_1001_; lean_object* v_tail_1002_; lean_object* v___x_1003_; 
v_head_1001_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_head_1001_);
v_tail_1002_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_tail_1002_);
lean_dec_ref_known(v_x_1000_, 2);
v___x_1003_ = l_Lean_Name_appendCore(v_x_999_, v_head_1001_);
lean_dec(v_x_999_);
v_x_999_ = v___x_1003_;
v_x_1000_ = v_tail_1002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
if (lean_obj_tag(v_a_1005_) == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = l_List_reverse___redArg(v_a_1006_);
return v___x_1007_;
}
else
{
lean_object* v_head_1008_; lean_object* v_tail_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1018_; 
v_head_1008_ = lean_ctor_get(v_a_1005_, 0);
v_tail_1009_ = lean_ctor_get(v_a_1005_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_1005_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1011_ = v_a_1005_;
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_tail_1009_);
lean_inc(v_head_1008_);
lean_dec(v_a_1005_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = l_Lean_Syntax_getId(v_head_1008_);
lean_dec(v_head_1008_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v_a_1006_);
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_a_1006_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v_a_1005_ = v_tail_1009_;
v_a_1006_ = v___x_1015_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(lean_object* v_item_1019_){
_start:
{
lean_object* v_optionComps_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_optionComps_1020_ = lean_ctor_get(v_item_1019_, 5);
lean_inc(v_optionComps_1020_);
lean_dec_ref(v_item_1019_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_box(0);
v___x_1023_ = l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(v_optionComps_1020_, v___x_1022_);
v___x_1024_ = l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(v___x_1021_, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object* v_item_1025_){
_start:
{
lean_object* v_ref_1026_; lean_object* v_option_1027_; lean_object* v_value_1028_; lean_object* v_bool_x3f_1029_; lean_object* v_origOptionName_1030_; lean_object* v_optionComps_1031_; lean_object* v_prevOptionComps_1032_; lean_object* v___y_1034_; 
v_ref_1026_ = lean_ctor_get(v_item_1025_, 0);
lean_inc(v_ref_1026_);
v_option_1027_ = lean_ctor_get(v_item_1025_, 1);
lean_inc(v_option_1027_);
v_value_1028_ = lean_ctor_get(v_item_1025_, 2);
lean_inc(v_value_1028_);
v_bool_x3f_1029_ = lean_ctor_get(v_item_1025_, 3);
lean_inc(v_bool_x3f_1029_);
v_origOptionName_1030_ = lean_ctor_get(v_item_1025_, 4);
lean_inc(v_origOptionName_1030_);
v_optionComps_1031_ = lean_ctor_get(v_item_1025_, 5);
v_prevOptionComps_1032_ = lean_ctor_get(v_item_1025_, 6);
lean_inc(v_prevOptionComps_1032_);
if (lean_obj_tag(v_optionComps_1031_) == 0)
{
v___y_1034_ = v_optionComps_1031_;
goto v___jp_1033_;
}
else
{
lean_object* v_tail_1051_; 
v_tail_1051_ = lean_ctor_get(v_optionComps_1031_, 1);
lean_inc(v_tail_1051_);
v___y_1034_ = v_tail_1051_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v___x_1035_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1025_);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_item_1025_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; lean_object* v_unused_1045_; lean_object* v_unused_1046_; lean_object* v_unused_1047_; lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; 
v_unused_1044_ = lean_ctor_get(v_item_1025_, 6);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_item_1025_, 5);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v_item_1025_, 4);
lean_dec(v_unused_1046_);
v_unused_1047_ = lean_ctor_get(v_item_1025_, 3);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_item_1025_, 2);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_item_1025_, 1);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_item_1025_, 0);
lean_dec(v_unused_1050_);
v___x_1037_ = v_item_1025_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v_item_1025_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1035_);
lean_ctor_set(v___x_1039_, 1, v_prevOptionComps_1032_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 6, v___x_1039_);
lean_ctor_set(v___x_1037_, 5, v___y_1034_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_ref_1026_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_option_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_value_1028_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_bool_x3f_1029_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_origOptionName_1030_);
lean_ctor_set(v_reuseFailAlloc_1042_, 5, v___y_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 6, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(1);
v___x_1053_ = l_Lean_MessageData_ofFormat(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2));
v___x_1058_ = l_Lean_MessageData_ofFormat(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 0)
{
return v_x_1059_;
}
else
{
lean_object* v_head_1061_; lean_object* v_tail_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1084_; 
v_head_1061_ = lean_ctor_get(v_x_1060_, 0);
v_tail_1062_ = lean_ctor_get(v_x_1060_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_1060_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1064_ = v_x_1060_;
v_isShared_1065_ = v_isSharedCheck_1084_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_tail_1062_);
lean_inc(v_head_1061_);
lean_dec(v_x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1084_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_before_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1082_; 
v_before_1066_ = lean_ctor_get(v_head_1061_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_head_1061_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_head_1061_, 1);
lean_dec(v_unused_1083_);
v___x_1068_ = v_head_1061_;
v_isShared_1069_ = v_isSharedCheck_1082_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_before_1066_);
lean_dec(v_head_1061_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1082_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 7);
lean_ctor_set(v___x_1068_, 1, v___x_1070_);
lean_ctor_set(v___x_1068_, 0, v_x_1059_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_x_1059_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 7);
lean_ctor_set(v___x_1064_, 1, v___x_1073_);
lean_ctor_set(v___x_1064_, 0, v___x_1072_);
v___x_1075_ = v___x_1064_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = l_Lean_MessageData_ofSyntax(v_before_1066_);
v___x_1077_ = l_Lean_indentD(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1075_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v_x_1059_ = v___x_1078_;
v_x_1060_ = v_tail_1062_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(lean_object* v_opts_1085_, lean_object* v_opt_1086_){
_start:
{
lean_object* v_name_1087_; lean_object* v_defValue_1088_; lean_object* v_map_1089_; lean_object* v___x_1090_; 
v_name_1087_ = lean_ctor_get(v_opt_1086_, 0);
v_defValue_1088_ = lean_ctor_get(v_opt_1086_, 1);
v_map_1089_ = lean_ctor_get(v_opts_1085_, 0);
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1089_, v_name_1087_);
if (lean_obj_tag(v___x_1090_) == 0)
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_unbox(v_defValue_1088_);
return v___x_1091_;
}
else
{
lean_object* v_val_1092_; 
v_val_1092_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_val_1092_);
lean_dec_ref_known(v___x_1090_, 1);
if (lean_obj_tag(v_val_1092_) == 1)
{
uint8_t v_v_1093_; 
v_v_1093_ = lean_ctor_get_uint8(v_val_1092_, 0);
lean_dec_ref_known(v_val_1092_, 0);
return v_v_1093_;
}
else
{
uint8_t v___x_1094_; 
lean_dec(v_val_1092_);
v___x_1094_ = lean_unbox(v_defValue_1088_);
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_1095_, lean_object* v_opt_1096_){
_start:
{
uint8_t v_res_1097_; lean_object* v_r_1098_; 
v_res_1097_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_1095_, v_opt_1096_);
lean_dec_ref(v_opt_1096_);
lean_dec_ref(v_opts_1095_);
v_r_1098_ = lean_box(v_res_1097_);
return v_r_1098_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_1103_ = l_Lean_MessageData_ofFormat(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_1104_, lean_object* v_macroStack_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1106_);
v___x_1109_ = l_Lean_Elab_pp_macroStack;
v___x_1110_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_1108_, v___x_1109_);
lean_dec_ref(v___x_1108_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v_macroStack_1105_);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_msgData_1104_);
return v___x_1111_;
}
else
{
if (lean_obj_tag(v_macroStack_1105_) == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_msgData_1104_);
return v___x_1112_;
}
else
{
lean_object* v_head_1113_; lean_object* v_after_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1129_; 
v_head_1113_ = lean_ctor_get(v_macroStack_1105_, 0);
lean_inc(v_head_1113_);
v_after_1114_ = lean_ctor_get(v_head_1113_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_head_1113_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v_head_1113_, 0);
lean_dec(v_unused_1130_);
v___x_1116_ = v_head_1113_;
v_isShared_1117_ = v_isSharedCheck_1129_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_after_1114_);
lean_dec(v_head_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1129_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 7);
lean_ctor_set(v___x_1116_, 1, v___x_1118_);
lean_ctor_set(v___x_1116_, 0, v_msgData_1104_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_msgData_1104_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_msgData_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1121_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_MessageData_ofSyntax(v_after_1114_);
v___x_1124_ = l_Lean_indentD(v___x_1123_);
v_msgData_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1125_, 0, v___x_1122_);
lean_ctor_set(v_msgData_1125_, 1, v___x_1124_);
v___x_1126_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(v_msgData_1125_, v_macroStack_1105_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_1131_, lean_object* v_macroStack_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1131_, v_macroStack_1132_, v___y_1133_);
lean_dec_ref(v___y_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(lean_object* v_msg_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_ref_1144_; lean_object* v_macroStack_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v_ref_1144_ = lean_ctor_get(v___y_1141_, 2);
v_macroStack_1145_ = lean_ctor_get(v___y_1137_, 1);
v___x_1146_ = l_Lean_Elab_getBetterRef(v_ref_1144_, v_macroStack_1145_);
v___x_1147_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_1136_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref(v___x_1147_);
lean_inc(v_macroStack_1145_);
v___x_1149_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_1148_, v_macroStack_1145_, v___y_1141_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1146_);
lean_ctor_set(v___x_1154_, 1, v_a_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(lean_object* v_ref_1168_, lean_object* v_msg_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_toCold_1177_; lean_object* v_currRecDepth_1178_; lean_object* v_ref_1179_; uint16_t v_optionFlags_1180_; uint8_t v_suppressElabErrors_1181_; uint8_t v_checkDeprecated_1182_; uint8_t v_isRecordingDeps_1183_; lean_object* v_ref_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_toCold_1177_ = lean_ctor_get(v___y_1174_, 0);
v_currRecDepth_1178_ = lean_ctor_get(v___y_1174_, 1);
v_ref_1179_ = lean_ctor_get(v___y_1174_, 2);
v_optionFlags_1180_ = lean_ctor_get_uint16(v___y_1174_, sizeof(void*)*3);
v_suppressElabErrors_1181_ = lean_ctor_get_uint8(v___y_1174_, sizeof(void*)*3 + 2);
v_checkDeprecated_1182_ = lean_ctor_get_uint8(v___y_1174_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1183_ = lean_ctor_get_uint8(v___y_1174_, sizeof(void*)*3 + 4);
v_ref_1184_ = l_Lean_replaceRef(v_ref_1168_, v_ref_1179_);
lean_inc(v_currRecDepth_1178_);
lean_inc_ref(v_toCold_1177_);
v___x_1185_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1185_, 0, v_toCold_1177_);
lean_ctor_set(v___x_1185_, 1, v_currRecDepth_1178_);
lean_ctor_set(v___x_1185_, 2, v_ref_1184_);
lean_ctor_set_uint16(v___x_1185_, sizeof(void*)*3, v_optionFlags_1180_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*3 + 2, v_suppressElabErrors_1181_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*3 + 3, v_checkDeprecated_1182_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*3 + 4, v_isRecordingDeps_1183_);
v___x_1186_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___x_1185_, v___y_1175_);
lean_dec_ref_known(v___x_1185_, 3);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(lean_object* v_ref_1187_, lean_object* v_msg_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1187_, v_msg_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v_ref_1187_);
return v_res_1196_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2));
v___x_1202_ = l_Lean_stringToMessageData(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object* v_item_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_bool_x3f_1211_; 
v_bool_x3f_1211_ = lean_ctor_get(v_item_1203_, 3);
if (lean_obj_tag(v_bool_x3f_1211_) == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_item_1203_);
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
else
{
lean_object* v_option_1214_; lean_object* v_origOptionName_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_option_1214_ = lean_ctor_get(v_item_1203_, 1);
lean_inc(v_option_1214_);
v_origOptionName_1215_ = lean_ctor_get(v_item_1203_, 4);
lean_inc(v_origOptionName_1215_);
lean_dec_ref(v_item_1203_);
v___x_1216_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1);
v___x_1217_ = l_Lean_MessageData_ofName(v_origOptionName_1215_);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3);
v___x_1220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1214_, v___x_1220_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
lean_dec(v_option_1214_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(lean_object* v_item_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(lean_object* v_00_u03b1_1231_, lean_object* v_ref_1232_, lean_object* v_msg_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1232_, v_msg_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_ref_1243_, lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(v_00_u03b1_1242_, v_ref_1243_, v_msg_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v_ref_1243_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(lean_object* v_00_u03b1_1253_, lean_object* v_msg_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_1263_, v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(lean_object* v_msgData_1273_, lean_object* v_macroStack_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1273_, v_macroStack_1274_, v___y_1279_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1283_, lean_object* v_macroStack_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_1283_, v_macroStack_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1292_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4));
v___x_1301_ = l_Lean_stringToMessageData(v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object* v_item_1302_, lean_object* v_structName_x3f_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_option_1311_; lean_object* v_origOptionName_1312_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1321_; uint8_t v___x_1330_; 
v_option_1311_ = lean_ctor_get(v_item_1302_, 1);
lean_inc(v_option_1311_);
v_origOptionName_1312_ = lean_ctor_get(v_item_1302_, 4);
lean_inc(v_origOptionName_1312_);
lean_dec_ref(v_item_1302_);
v___x_1330_ = l_Lean_Name_isAnonymous(v_origOptionName_1312_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1331_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1332_ = l_Lean_MessageData_ofName(v_origOptionName_1312_);
v___x_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___y_1321_ = v___x_1335_;
goto v___jp_1320_;
}
else
{
lean_object* v___x_1336_; 
lean_dec(v_origOptionName_1312_);
v___x_1336_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1321_ = v___x_1336_;
goto v___jp_1320_;
}
v___jp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___y_1314_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___y_1315_);
v___x_1319_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1311_, v___x_1318_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_option_1311_);
return v___x_1319_;
}
v___jp_1320_:
{
if (lean_obj_tag(v_structName_x3f_1303_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_val_1322_ = lean_ctor_get(v_structName_x3f_1303_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v_structName_x3f_1303_, 1);
v___x_1323_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1324_ = 0;
v___x_1325_ = l_Lean_MessageData_ofConstName(v_val_1322_, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1323_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___y_1314_ = v___y_1321_;
v___y_1315_ = v___x_1328_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1329_; 
lean_dec(v_structName_x3f_1303_);
v___x_1329_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1314_ = v___y_1321_;
v___y_1315_ = v___x_1329_;
goto v___jp_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___boxed(lean_object* v_item_1337_, lean_object* v_structName_x3f_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1337_, v_structName_x3f_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(lean_object* v_00_u03b1_1347_, lean_object* v_item_1348_, lean_object* v_structName_x3f_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1348_, v_structName_x3f_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___boxed(lean_object* v_00_u03b1_1358_, lean_object* v_item_1359_, lean_object* v_structName_x3f_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(v_00_u03b1_1358_, v_item_1359_, v_structName_x3f_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
return v_res_1368_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0));
v___x_1371_ = l_Lean_stringToMessageData(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(lean_object* v_item_1375_, lean_object* v_structName_x3f_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_option_1384_; lean_object* v_origOptionName_1385_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1396_; uint8_t v___x_1405_; 
v_option_1384_ = lean_ctor_get(v_item_1375_, 1);
lean_inc(v_option_1384_);
v_origOptionName_1385_ = lean_ctor_get(v_item_1375_, 4);
lean_inc(v_origOptionName_1385_);
lean_dec_ref(v_item_1375_);
v___x_1405_ = l_Lean_Name_isAnonymous(v_origOptionName_1385_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1406_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1407_ = l_Lean_MessageData_ofName(v_origOptionName_1385_);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___y_1396_ = v___x_1410_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_origOptionName_1385_);
v___x_1411_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1396_ = v___x_1411_;
goto v___jp_1395_;
}
v___jp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1389_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___y_1387_);
v___x_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___y_1388_);
v___x_1392_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
v___x_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1384_, v___x_1393_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_option_1384_);
return v___x_1394_;
}
v___jp_1395_:
{
if (lean_obj_tag(v_structName_x3f_1376_) == 1)
{
lean_object* v_val_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_val_1397_ = lean_ctor_get(v_structName_x3f_1376_, 0);
lean_inc(v_val_1397_);
lean_dec_ref_known(v_structName_x3f_1376_, 1);
v___x_1398_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1399_ = 0;
v___x_1400_ = l_Lean_MessageData_ofConstName(v_val_1397_, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1398_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___y_1387_ = v___y_1396_;
v___y_1388_ = v___x_1403_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1404_; 
lean_dec(v_structName_x3f_1376_);
v___x_1404_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1387_ = v___y_1396_;
v___y_1388_ = v___x_1404_;
goto v___jp_1386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___boxed(lean_object* v_item_1412_, lean_object* v_structName_x3f_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1412_, v_structName_x3f_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(lean_object* v_00_u03b1_1422_, lean_object* v_item_1423_, lean_object* v_structName_x3f_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1423_, v_structName_x3f_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_item_1434_, lean_object* v_structName_x3f_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(v_00_u03b1_1433_, v_item_1434_, v_structName_x3f_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___lam__0(lean_object* v_projFn_1444_, lean_object* v___x_1445_, lean_object* v_newName_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1452_ = l_Lean_Name_getPrefix(v_newName_1446_);
v___x_1453_ = l_Lean_Name_getPrefix(v_projFn_1444_);
v___x_1454_ = lean_name_eq(v___x_1452_, v___x_1453_);
lean_dec(v___x_1453_);
lean_dec(v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v___x_1445_);
v___x_1455_ = l_Lean_MessageData_nil;
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = l_Lean_Name_getString_x21(v_newName_1446_);
v___x_1458_ = l_Lean_Linter_mkReplacementHint___redArg(v___x_1445_, v___x_1457_, v___y_1449_, v___y_1450_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___lam__0___boxed(lean_object* v_projFn_1459_, lean_object* v___x_1460_, lean_object* v_newName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___lam__0(v_projFn_1459_, v___x_1460_, v_newName_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_newName_1461_);
lean_dec(v_projFn_1459_);
return v_res_1467_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
lean_ctor_set(v___x_1473_, 2, v___x_1472_);
lean_ctor_set(v___x_1473_, 3, v___x_1472_);
lean_ctor_set(v___x_1473_, 4, v___x_1471_);
lean_ctor_set(v___x_1473_, 5, v___x_1471_);
lean_ctor_set(v___x_1473_, 6, v___x_1471_);
lean_ctor_set(v___x_1473_, 7, v___x_1471_);
lean_ctor_set(v___x_1473_, 8, v___x_1471_);
lean_ctor_set(v___x_1473_, 9, v___x_1471_);
lean_ctor_set(v___x_1473_, 10, v___x_1471_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_unsigned_to_nat(32u);
v___x_1475_ = lean_mk_empty_array_with_capacity(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1477_ = ((size_t)5ULL);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_unsigned_to_nat(32u);
v___x_1480_ = lean_mk_empty_array_with_capacity(v___x_1479_);
v___x_1481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1482_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v___x_1478_);
lean_ctor_set(v___x_1482_, 3, v___x_1478_);
lean_ctor_set_usize(v___x_1482_, 4, v___x_1477_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1483_ = lean_box(1);
v___x_1484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1485_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v___x_1484_);
lean_ctor_set(v___x_1486_, 2, v___x_1483_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1508_, lean_object* v_declHint_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_env_1514_; uint8_t v___x_1515_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_st_ref_get(v___y_1510_);
v_env_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc_ref(v_env_1514_);
lean_dec(v___x_1513_);
v___x_1515_ = l_Lean_Name_isAnonymous(v_declHint_1509_);
if (v___x_1515_ == 0)
{
uint8_t v_isExporting_1516_; 
v_isExporting_1516_ = lean_ctor_get_uint8(v_env_1514_, sizeof(void*)*13);
if (v_isExporting_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref(v_env_1514_);
lean_dec(v_declHint_1509_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_msg_1508_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
lean_inc_ref(v_env_1514_);
v___x_1518_ = l_Lean_Environment_setExporting(v_env_1514_, v___x_1515_);
lean_inc(v_declHint_1509_);
lean_inc_ref(v___x_1518_);
v___x_1519_ = l_Lean_Environment_contains(v___x_1518_, v_declHint_1509_, v_isExporting_1516_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
lean_dec_ref(v___x_1518_);
lean_dec_ref(v_env_1514_);
lean_dec(v_declHint_1509_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_msg_1508_);
return v___x_1520_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v_c_1526_; lean_object* v___x_1527_; 
v___x_1521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1522_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1523_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1518_);
v___x_1524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1518_);
lean_ctor_set(v___x_1524_, 1, v___x_1521_);
lean_ctor_set(v___x_1524_, 2, v___x_1522_);
lean_ctor_set(v___x_1524_, 3, v___x_1523_);
lean_inc(v_declHint_1509_);
v___x_1525_ = l_Lean_MessageData_ofConstName(v_declHint_1509_, v___x_1515_);
v_c_1526_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1526_, 0, v___x_1524_);
lean_ctor_set(v_c_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1518_, v_declHint_1509_);
lean_dec_ref(v___x_1518_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec_ref(v_env_1514_);
lean_dec(v_declHint_1509_);
v___x_1528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v_c_1526_);
v___x_1530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_MessageData_note(v___x_1531_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_msg_1508_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
else
{
lean_object* v_val_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1569_; 
v_val_1535_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1537_ = v___x_1527_;
v_isShared_1538_ = v_isSharedCheck_1569_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_val_1535_);
lean_dec(v___x_1527_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1569_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v_moduleNames_1540_; lean_object* v_mod_1541_; uint8_t v___x_1542_; 
v___x_1539_ = l_Lean_Environment_header(v_env_1514_);
lean_dec_ref(v_env_1514_);
v_moduleNames_1540_ = lean_ctor_get(v___x_1539_, 4);
lean_inc_ref(v_moduleNames_1540_);
lean_dec_ref(v___x_1539_);
v_mod_1541_ = lean_array_get(v___x_1512_, v_moduleNames_1540_, v_val_1535_);
lean_dec(v_val_1535_);
lean_dec_ref(v_moduleNames_1540_);
v___x_1542_ = l_Lean_isPrivateName(v_declHint_1509_);
lean_dec(v_declHint_1509_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_c_1526_);
v___x_1545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = l_Lean_MessageData_ofName(v_mod_1541_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_MessageData_note(v___x_1550_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_msg_1508_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1552_);
v___x_1554_ = v___x_1537_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v_c_1526_);
v___x_1558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_MessageData_ofName(v_mod_1541_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_MessageData_note(v___x_1563_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_msg_1508_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1565_);
v___x_1567_ = v___x_1537_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1570_; 
lean_dec_ref(v_env_1514_);
lean_dec(v_declHint_1509_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_msg_1508_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1571_, lean_object* v_declHint_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1571_, v_declHint_1572_, v___y_1573_);
lean_dec(v___y_1573_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_1576_, lean_object* v_declHint_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1595_; 
v___x_1585_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1576_, v_declHint_1577_, v___y_1583_);
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = l_Lean_unknownIdentifierMessageTag;
v___x_1591_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_a_1586_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_1596_, lean_object* v_declHint_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1596_, v_declHint_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1606_, lean_object* v_msg_1607_, lean_object* v_declHint_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1618_; 
v___x_1616_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1607_, v_declHint_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1606_, v_a_1617_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1619_, lean_object* v_msg_1620_, lean_object* v_declHint_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1619_, v_msg_1620_, v_declHint_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v_ref_1619_);
return v_res_1629_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_1633_, lean_object* v_constName_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1642_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1643_ = 0;
lean_inc(v_constName_1634_);
v___x_1644_ = l_Lean_MessageData_ofConstName(v_constName_1634_, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1642_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1633_, v___x_1647_, v_constName_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1649_, lean_object* v_constName_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1649_, v_constName_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v_ref_1649_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_ref_1667_; lean_object* v___x_1668_; 
v_ref_1667_ = lean_ctor_get(v___y_1664_, 2);
v___x_1668_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1667_, v_constName_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object* v_constName_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v_env_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1686_ = lean_st_ref_get(v___y_1684_);
v_env_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc_ref(v_env_1687_);
lean_dec(v___x_1686_);
v___x_1688_ = 0;
lean_inc(v_constName_1678_);
v___x_1689_ = l_Lean_Environment_findConstVal_x3f(v_env_1687_, v_constName_1678_, v___x_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_constName_1678_);
v_val_1691_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1689_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_val_1691_);
lean_dec(v___x_1689_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 0);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_val_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
if (lean_obj_tag(v_a_1708_) == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = l_List_reverse___redArg(v_a_1709_);
return v___x_1710_;
}
else
{
lean_object* v_head_1711_; lean_object* v_tail_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1721_; 
v_head_1711_ = lean_ctor_get(v_a_1708_, 0);
v_tail_1712_ = lean_ctor_get(v_a_1708_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_a_1708_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1714_ = v_a_1708_;
v_isShared_1715_ = v_isSharedCheck_1721_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_tail_1712_);
lean_inc(v_head_1711_);
lean_dec(v_a_1708_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1721_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = l_Lean_mkLevelParam(v_head_1711_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_a_1709_);
lean_ctor_set(v___x_1714_, 0, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_a_1709_);
v___x_1718_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v_a_1708_ = v_tail_1712_;
v_a_1709_ = v___x_1718_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object* v_constName_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
lean_inc(v_constName_1722_);
v___x_1730_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1742_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1742_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1742_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_levelParams_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v_levelParams_1735_ = lean_ctor_get(v_a_1731_, 1);
lean_inc(v_levelParams_1735_);
lean_dec(v_a_1731_);
v___x_1736_ = lean_box(0);
v___x_1737_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_1735_, v___x_1736_);
v___x_1738_ = l_Lean_mkConst(v_constName_1722_, v___x_1737_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1738_);
v___x_1740_ = v___x_1733_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v_constName_1722_);
v_a_1743_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1730_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1730_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object* v_constName_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; lean_object* v_infoState_1764_; uint8_t v_enabled_1765_; 
v___x_1763_ = lean_st_ref_get(v___y_1761_);
v_infoState_1764_ = lean_ctor_get(v___x_1763_, 8);
lean_inc_ref(v_infoState_1764_);
lean_dec(v___x_1763_);
v_enabled_1765_ = lean_ctor_get_uint8(v_infoState_1764_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1764_);
if (v_enabled_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v_t_1760_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; lean_object* v_infoState_1769_; lean_object* v_env_1770_; lean_object* v_nextMacroScope_1771_; lean_object* v_ngen_1772_; lean_object* v_auxDeclNGen_1773_; lean_object* v_traceState_1774_; lean_object* v_cache_1775_; lean_object* v_recordedDeps_1776_; lean_object* v_messages_1777_; lean_object* v_snapshotTasks_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1800_; 
v___x_1768_ = lean_st_ref_take(v___y_1761_);
v_infoState_1769_ = lean_ctor_get(v___x_1768_, 8);
v_env_1770_ = lean_ctor_get(v___x_1768_, 0);
v_nextMacroScope_1771_ = lean_ctor_get(v___x_1768_, 1);
v_ngen_1772_ = lean_ctor_get(v___x_1768_, 2);
v_auxDeclNGen_1773_ = lean_ctor_get(v___x_1768_, 3);
v_traceState_1774_ = lean_ctor_get(v___x_1768_, 4);
v_cache_1775_ = lean_ctor_get(v___x_1768_, 5);
v_recordedDeps_1776_ = lean_ctor_get(v___x_1768_, 6);
v_messages_1777_ = lean_ctor_get(v___x_1768_, 7);
v_snapshotTasks_1778_ = lean_ctor_get(v___x_1768_, 9);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1780_ = v___x_1768_;
v_isShared_1781_ = v_isSharedCheck_1800_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snapshotTasks_1778_);
lean_inc(v_infoState_1769_);
lean_inc(v_messages_1777_);
lean_inc(v_recordedDeps_1776_);
lean_inc(v_cache_1775_);
lean_inc(v_traceState_1774_);
lean_inc(v_auxDeclNGen_1773_);
lean_inc(v_ngen_1772_);
lean_inc(v_nextMacroScope_1771_);
lean_inc(v_env_1770_);
lean_dec(v___x_1768_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1800_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
uint8_t v_enabled_1782_; lean_object* v_assignment_1783_; lean_object* v_lazyAssignment_1784_; lean_object* v_trees_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1799_; 
v_enabled_1782_ = lean_ctor_get_uint8(v_infoState_1769_, sizeof(void*)*3);
v_assignment_1783_ = lean_ctor_get(v_infoState_1769_, 0);
v_lazyAssignment_1784_ = lean_ctor_get(v_infoState_1769_, 1);
v_trees_1785_ = lean_ctor_get(v_infoState_1769_, 2);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_infoState_1769_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1787_ = v_infoState_1769_;
v_isShared_1788_ = v_isSharedCheck_1799_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_trees_1785_);
lean_inc(v_lazyAssignment_1784_);
lean_inc(v_assignment_1783_);
lean_dec(v_infoState_1769_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1799_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1789_ = lean_box(0);
v___x_1790_ = l_Lean_PersistentArray_push___redArg(v_trees_1785_, v_t_1760_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 2, v___x_1790_);
v___x_1792_ = v___x_1787_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_assignment_1783_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_lazyAssignment_1784_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v___x_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*3, v_enabled_1782_);
v___x_1792_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1794_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 8, v___x_1792_);
v___x_1794_ = v___x_1780_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_env_1770_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_nextMacroScope_1771_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_ngen_1772_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_auxDeclNGen_1773_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_traceState_1774_);
lean_ctor_set(v_reuseFailAlloc_1797_, 5, v_cache_1775_);
lean_ctor_set(v_reuseFailAlloc_1797_, 6, v_recordedDeps_1776_);
lean_ctor_set(v_reuseFailAlloc_1797_, 7, v_messages_1777_);
lean_ctor_set(v_reuseFailAlloc_1797_, 8, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1797_, 9, v_snapshotTasks_1778_);
v___x_1794_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_st_ref_put(v___y_1761_, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1789_);
return v___x_1796_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1801_, v___y_1802_);
lean_dec(v___y_1802_);
return v_res_1804_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_unsigned_to_nat(32u);
v___x_1806_ = lean_mk_empty_array_with_capacity(v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1808_ = ((size_t)5ULL);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_unsigned_to_nat(32u);
v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
v___x_1813_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
lean_ctor_set(v___x_1813_, 2, v___x_1809_);
lean_ctor_set(v___x_1813_, 3, v___x_1809_);
lean_ctor_set_usize(v___x_1813_, 4, v___x_1808_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object* v_t_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; lean_object* v_infoState_1823_; uint8_t v_enabled_1824_; 
v___x_1822_ = lean_st_ref_get(v___y_1820_);
v_infoState_1823_ = lean_ctor_get(v___x_1822_, 8);
lean_inc_ref(v_infoState_1823_);
lean_dec(v___x_1822_);
v_enabled_1824_ = lean_ctor_get_uint8(v_infoState_1823_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1823_);
if (v_enabled_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec_ref(v_t_1814_);
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
v___x_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_t_1814_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_1828_, v___y_1820_);
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object* v_t_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object* v_stx_1839_, lean_object* v_n_1840_, lean_object* v_expectedType_x3f_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_1840_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = lean_box(0);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v_stx_1839_);
v___x_1853_ = l_Lean_LocalContext_empty;
v___x_1854_ = 0;
v___x_1855_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1855_, 0, v___x_1852_);
lean_ctor_set(v___x_1855_, 1, v___x_1853_);
lean_ctor_set(v___x_1855_, 2, v_expectedType_x3f_1841_);
lean_ctor_set(v___x_1855_, 3, v_a_1850_);
lean_ctor_set_uint8(v___x_1855_, sizeof(void*)*4, v___x_1854_);
lean_ctor_set_uint8(v___x_1855_, sizeof(void*)*4 + 1, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v___x_1857_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1856_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1857_;
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_expectedType_x3f_1841_);
lean_dec(v_stx_1839_);
v_a_1858_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1849_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1849_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object* v_stx_1866_, lean_object* v_n_1867_, lean_object* v_expectedType_x3f_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1866_, v_n_1867_, v_expectedType_x3f_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object* v_item_1877_, lean_object* v_projFn_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___x_1895_; lean_object* v_env_1896_; uint8_t v___x_1897_; uint8_t v___x_1898_; 
v___x_1895_ = lean_st_ref_get(v_a_1884_);
v_env_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc_ref(v_env_1896_);
lean_dec(v___x_1895_);
v___x_1897_ = 1;
lean_inc(v_projFn_1878_);
v___x_1898_ = l_Lean_Environment_contains(v_env_1896_, v_projFn_1878_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec(v_projFn_1878_);
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; lean_object* v_infoState_1902_; uint8_t v_enabled_1903_; 
v___x_1901_ = lean_st_ref_get(v_a_1884_);
v_infoState_1902_ = lean_ctor_get(v___x_1901_, 8);
lean_inc_ref(v_infoState_1902_);
lean_dec(v___x_1901_);
v_enabled_1903_ = lean_ctor_get_uint8(v_infoState_1902_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1902_);
if (v_enabled_1903_ == 0)
{
v___y_1887_ = v_a_1881_;
v___y_1888_ = v_a_1882_;
v___y_1889_ = v_a_1883_;
v___y_1890_ = v_a_1884_;
goto v___jp_1886_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1877_);
v___x_1905_ = lean_box(0);
lean_inc(v_projFn_1878_);
v___x_1906_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_1904_, v_projFn_1878_, v___x_1905_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_dec_ref_known(v___x_1906_, 1);
v___y_1887_ = v_a_1881_;
v___y_1888_ = v_a_1882_;
v___y_1889_ = v_a_1883_;
v___y_1890_ = v_a_1884_;
goto v___jp_1886_;
}
else
{
lean_dec(v_projFn_1878_);
return v___x_1906_;
}
}
}
v___jp_1886_:
{
lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1891_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1877_);
lean_inc(v___x_1891_);
lean_inc(v_projFn_1878_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1892_, 0, v_projFn_1878_);
lean_closure_set(v___f_1892_, 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___f_1892_);
v___x_1894_ = l_Lean_Linter_checkDeprecatedAt(v___x_1891_, v_projFn_1878_, v___x_1893_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___x_1891_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object* v_item_1907_, lean_object* v_projFn_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1907_, v_projFn_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec_ref(v_item_1907_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object* v_t_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1917_, v___y_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1935_, lean_object* v_constName_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1945_, lean_object* v_constName_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1945_, v_constName_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_1955_, lean_object* v_ref_1956_, lean_object* v_constName_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1956_, v_constName_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_ref_1967_, lean_object* v_constName_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_1966_, v_ref_1967_, v_constName_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_ref_1967_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1977_, lean_object* v_ref_1978_, lean_object* v_msg_1979_, lean_object* v_declHint_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1978_, v_msg_1979_, v_declHint_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1989_, lean_object* v_ref_1990_, lean_object* v_msg_1991_, lean_object* v_declHint_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1989_, v_ref_1990_, v_msg_1991_, v_declHint_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v_ref_1990_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2001_, lean_object* v_declHint_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2001_, v_declHint_2002_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2011_, lean_object* v_declHint_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2011_, v_declHint_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object* v_info_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_info_2021_);
v___x_2030_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_2029_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(lean_object* v_info_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2039_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = lean_box(1);
v___x_2043_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2044_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_2045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v___x_2043_);
lean_ctor_set(v___x_2045_, 2, v___x_2042_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object* v_item_2046_, lean_object* v_structName_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; lean_object* v_infoState_2056_; uint8_t v_enabled_2057_; 
v___x_2055_ = lean_st_ref_get(v_a_2053_);
v_infoState_2056_ = lean_ctor_get(v___x_2055_, 8);
lean_inc_ref(v_infoState_2056_);
lean_dec(v___x_2055_);
v_enabled_2057_ = lean_ctor_get_uint8(v_infoState_2056_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2056_);
if (v_enabled_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v_structName_2047_);
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
else
{
lean_object* v___x_2060_; lean_object* v_env_2061_; uint8_t v___x_2062_; 
v___x_2060_ = lean_st_ref_get(v_a_2053_);
v_env_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc_ref(v_env_2061_);
lean_dec(v___x_2060_);
lean_inc(v_structName_2047_);
v___x_2062_ = l_Lean_Environment_contains(v_env_2061_, v_structName_2047_, v_enabled_2057_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec(v_structName_2047_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2065_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_2046_);
v___x_2066_ = l_Lean_Syntax_getId(v___x_2065_);
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
v___x_2068_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2069_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2065_);
lean_ctor_set(v___x_2069_, 1, v___x_2067_);
lean_ctor_set(v___x_2069_, 2, v___x_2068_);
lean_ctor_set(v___x_2069_, 3, v_structName_2047_);
v___x_2070_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2069_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object* v_item_2071_, lean_object* v_structName_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2071_, v_structName_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec_ref(v_item_2071_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object* v_cfg_2081_, lean_object* v_withRef_2082_, lean_object* v___x_2083_, lean_object* v_oldRef_2084_){
_start:
{
lean_object* v_ref_2085_; lean_object* v___x_2086_; 
v_ref_2085_ = l_Lean_replaceRef(v_cfg_2081_, v_oldRef_2084_);
v___x_2086_ = lean_apply_3(v_withRef_2082_, lean_box(0), v_ref_2085_, v___x_2083_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object* v_cfg_2087_, lean_object* v_withRef_2088_, lean_object* v___x_2089_, lean_object* v_oldRef_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(v_cfg_2087_, v_withRef_2088_, v___x_2089_, v_oldRef_2090_);
lean_dec(v_oldRef_2090_);
lean_dec(v_cfg_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t v_x_2092_){
_start:
{
uint32_t v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = 46;
v___x_2094_ = lean_uint32_dec_eq(v_x_2092_, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object* v_x_2095_){
_start:
{
uint32_t v_x_917__boxed_2096_; uint8_t v_res_2097_; lean_object* v_r_2098_; 
v_x_917__boxed_2096_ = lean_unbox_uint32(v_x_2095_);
lean_dec(v_x_2095_);
v_res_2097_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_917__boxed_2096_);
v_r_2098_ = lean_box(v_res_2097_);
return v_r_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object* v___f_2099_, lean_object* v_s_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2099_);
v___x_2108_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2100_, v___x_2107_, v___y_2101_, lean_box(0), lean_box(0), v___y_2104_, v___y_2105_, v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object* v___f_2110_, lean_object* v_si_2111_, lean_object* v_val_2112_){
_start:
{
lean_object* v___y_2114_; lean_object* v___f_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___f_2120_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0));
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = lean_string_utf8_byte_size(v_val_2112_);
lean_inc_ref(v_val_2112_);
v___x_2123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2123_, 0, v_val_2112_);
lean_ctor_set(v___x_2123_, 1, v___x_2121_);
lean_ctor_set(v___x_2123_, 2, v___x_2122_);
v___x_2124_ = l_String_Slice_contains___redArg(v___f_2110_, v___x_2123_, v___f_2120_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_box(0);
lean_inc_ref(v_val_2112_);
v___x_2126_ = l_Lean_Name_str___override(v___x_2125_, v_val_2112_);
v___y_2114_ = v___x_2126_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2127_; 
lean_inc_ref(v_val_2112_);
v___x_2127_ = l_String_toName(v_val_2112_);
v___y_2114_ = v___x_2127_;
goto v___jp_2113_;
}
v___jp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_string_utf8_byte_size(v_val_2112_);
v___x_2117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2117_, 0, v_val_2112_);
lean_ctor_set(v___x_2117_, 1, v___x_2115_);
lean_ctor_set(v___x_2117_, 2, v___x_2116_);
v___x_2118_ = lean_box(0);
v___x_2119_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2119_, 0, v_si_2111_);
lean_ctor_set(v___x_2119_, 1, v___x_2117_);
lean_ctor_set(v___x_2119_, 2, v___y_2114_);
lean_ctor_set(v___x_2119_, 3, v___x_2118_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object* v_atomAsIdent_2128_, lean_object* v_stx_2129_){
_start:
{
switch(lean_obj_tag(v_stx_2129_))
{
case 3:
{
lean_object* v___x_2130_; 
lean_dec_ref(v_atomAsIdent_2128_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_stx_2129_);
return v___x_2130_;
}
case 2:
{
lean_object* v_info_2131_; lean_object* v_val_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_info_2131_ = lean_ctor_get(v_stx_2129_, 0);
lean_inc(v_info_2131_);
v_val_2132_ = lean_ctor_get(v_stx_2129_, 1);
lean_inc_ref(v_val_2132_);
lean_dec_ref_known(v_stx_2129_, 2);
v___x_2133_ = lean_apply_2(v_atomAsIdent_2128_, v_info_2131_, v_val_2132_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
default: 
{
lean_object* v___x_2135_; 
lean_dec(v_stx_2129_);
lean_dec_ref(v_atomAsIdent_2128_);
v___x_2135_ = lean_box(0);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_init_2161_, lean_object* v_cfgs_2162_, lean_object* v_k_2163_, lean_object* v_onErr_2164_){
_start:
{
lean_object* v_toApplicative_2165_; lean_object* v_toPure_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v_toApplicative_2165_ = lean_ctor_get(v_inst_2159_, 0);
v_toPure_2166_ = lean_ctor_get(v_toApplicative_2165_, 1);
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = lean_array_get_size(v_cfgs_2162_);
v___x_2169_ = lean_nat_dec_lt(v___x_2167_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
lean_inc(v_toPure_2166_);
lean_dec(v_onErr_2164_);
lean_dec(v_k_2163_);
lean_dec_ref(v_cfgs_2162_);
lean_dec_ref(v_inst_2160_);
lean_dec_ref(v_inst_2159_);
v___x_2170_ = lean_apply_2(v_toPure_2166_, lean_box(0), v_init_2161_);
return v___x_2170_;
}
else
{
lean_object* v___f_2171_; size_t v___x_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
lean_inc_ref(v_inst_2159_);
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_2171_, 0, v_inst_2159_);
lean_closure_set(v___f_2171_, 1, v_inst_2160_);
lean_closure_set(v___f_2171_, 2, v_k_2163_);
lean_closure_set(v___f_2171_, 3, v_onErr_2164_);
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = lean_usize_of_nat(v___x_2168_);
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2159_, v___f_2171_, v_cfgs_2162_, v___x_2172_, v___x_2173_, v_init_2161_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_init_2177_, lean_object* v_cfg_2178_, lean_object* v_k_2179_, lean_object* v_onErr_2180_){
_start:
{
lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2178_);
v___x_2200_ = l_Lean_Syntax_isOfKind(v_cfg_2178_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2201_ = l_Lean_Syntax_getNumArgs(v_cfg_2178_);
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_nat_dec_eq(v___x_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___f_2204_; lean_object* v_atomAsIdent_2205_; uint8_t v___x_2206_; 
v___f_2204_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3));
v_atomAsIdent_2205_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4));
v___x_2206_ = lean_nat_dec_le(v___x_2202_, v___x_2201_);
if (v___x_2206_ == 0)
{
lean_dec(v___x_2201_);
if (lean_obj_tag(v_cfg_2178_) == 2)
{
lean_object* v_info_2207_; lean_object* v_val_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_onErr_2180_);
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
v_info_2207_ = lean_ctor_get(v_cfg_2178_, 0);
v_val_2208_ = lean_ctor_get(v_cfg_2178_, 1);
lean_inc_ref(v_val_2208_);
lean_inc(v_info_2207_);
v___x_2209_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(v___f_2204_, v_info_2207_, v_val_2208_);
v___x_2210_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2211_ = l_Lean_mkCIdentFrom(v_cfg_2178_, v___x_2210_, v___x_2206_);
v___x_2212_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2213_ = l_Lean_TSyntax_getId(v___x_2209_);
v___x_2214_ = l_Lean_Name_eraseMacroScopes(v___x_2213_);
lean_dec(v___x_2213_);
v___x_2215_ = lean_box(0);
lean_inc(v___x_2209_);
v___x_2216_ = l_Lean_Syntax_identComponents(v___x_2209_, v___x_2215_);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2218_, 0, v_cfg_2178_);
lean_ctor_set(v___x_2218_, 1, v___x_2209_);
lean_ctor_set(v___x_2218_, 2, v___x_2211_);
lean_ctor_set(v___x_2218_, 3, v___x_2212_);
lean_ctor_set(v___x_2218_, 4, v___x_2214_);
lean_ctor_set(v___x_2218_, 5, v___x_2216_);
lean_ctor_set(v___x_2218_, 6, v___x_2217_);
v___x_2219_ = lean_apply_2(v_k_2179_, v_init_2177_, v___x_2218_);
return v___x_2219_;
}
else
{
lean_dec(v_k_2179_);
goto v___jp_2192_;
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = l_Lean_Syntax_getArg(v_cfg_2178_, v___x_2220_);
if (lean_obj_tag(v___x_2221_) == 2)
{
lean_object* v_val_2222_; lean_object* v___y_2224_; uint8_t v_val_2225_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_val_2222_ = lean_ctor_get(v___x_2221_, 1);
v___x_2236_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2237_ = lean_string_dec_eq(v_val_2222_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2239_ = lean_string_dec_eq(v_val_2222_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
lean_inc_ref(v_val_2222_);
lean_dec_ref_known(v___x_2221_, 2);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2241_ = lean_string_dec_eq(v_val_2222_, v___x_2240_);
lean_dec_ref(v_val_2222_);
if (v___x_2241_ == 0)
{
lean_dec(v___x_2201_);
lean_dec(v_k_2179_);
goto v___jp_2192_;
}
else
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = lean_unsigned_to_nat(5u);
v___x_2243_ = lean_nat_dec_le(v___x_2201_, v___x_2242_);
lean_dec(v___x_2201_);
if (v___x_2243_ == 0)
{
lean_dec(v_k_2179_);
goto v___jp_2192_;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = l_Lean_Syntax_getArg(v_cfg_2178_, v___x_2202_);
v___x_2245_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2205_, v___x_2244_);
if (lean_obj_tag(v___x_2245_) == 1)
{
lean_object* v_val_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec(v_onErr_2180_);
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
v_val_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_n(v_val_2246_, 2);
lean_dec_ref_known(v___x_2245_, 1);
v___x_2247_ = lean_unsigned_to_nat(3u);
v___x_2248_ = l_Lean_Syntax_getArg(v_cfg_2178_, v___x_2247_);
v___x_2249_ = lean_box(0);
v___x_2250_ = l_Lean_TSyntax_getId(v_val_2246_);
v___x_2251_ = l_Lean_Name_eraseMacroScopes(v___x_2250_);
lean_dec(v___x_2250_);
v___x_2252_ = l_Lean_Syntax_identComponents(v_val_2246_, v___x_2249_);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2254_, 0, v_cfg_2178_);
lean_ctor_set(v___x_2254_, 1, v_val_2246_);
lean_ctor_set(v___x_2254_, 2, v___x_2248_);
lean_ctor_set(v___x_2254_, 3, v___x_2249_);
lean_ctor_set(v___x_2254_, 4, v___x_2251_);
lean_ctor_set(v___x_2254_, 5, v___x_2252_);
lean_ctor_set(v___x_2254_, 6, v___x_2253_);
v___x_2255_ = lean_apply_2(v_k_2179_, v_init_2177_, v___x_2254_);
return v___x_2255_;
}
else
{
lean_dec(v___x_2245_);
lean_dec(v_k_2179_);
goto v___jp_2192_;
}
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_box(v___x_2237_);
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
v___y_2224_ = v___x_2257_;
v_val_2225_ = v___x_2237_;
goto v___jp_2223_;
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_box(v___x_2206_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
v___y_2224_ = v___x_2259_;
v_val_2225_ = v___x_2206_;
goto v___jp_2223_;
}
v___jp_2223_:
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(2u);
v___x_2227_ = lean_nat_dec_eq(v___x_2201_, v___x_2226_);
lean_dec(v___x_2201_);
if (v___x_2227_ == 0)
{
lean_dec(v___y_2224_);
lean_dec_ref_known(v___x_2221_, 2);
lean_dec(v_k_2179_);
goto v___jp_2192_;
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = l_Lean_Syntax_getArg(v_cfg_2178_, v___x_2202_);
v___x_2229_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2205_, v___x_2228_);
if (lean_obj_tag(v___x_2229_) == 1)
{
lean_dec(v_onErr_2180_);
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
if (v_val_2225_ == 0)
{
lean_object* v_val_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_val_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_val_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2232_ = l_Lean_mkCIdentFrom(v___x_2221_, v___x_2231_, v_val_2225_);
lean_dec_ref_known(v___x_2221_, 2);
v___y_2182_ = v_val_2230_;
v___y_2183_ = v___y_2224_;
v___y_2184_ = v___x_2232_;
goto v___jp_2181_;
}
else
{
lean_object* v_val_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_val_2233_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2235_ = l_Lean_mkCIdentFrom(v___x_2221_, v___x_2234_, v___x_2203_);
lean_dec_ref_known(v___x_2221_, 2);
v___y_2182_ = v_val_2233_;
v___y_2183_ = v___y_2224_;
v___y_2184_ = v___x_2235_;
goto v___jp_2181_;
}
}
else
{
lean_dec(v___x_2229_);
lean_dec(v___y_2224_);
lean_dec_ref_known(v___x_2221_, 2);
lean_dec(v_k_2179_);
goto v___jp_2192_;
}
}
}
}
else
{
lean_dec(v___x_2221_);
lean_dec(v___x_2201_);
lean_dec(v_k_2179_);
goto v___jp_2192_;
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec(v___x_2201_);
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = l_Lean_Syntax_getArg(v_cfg_2178_, v___x_2260_);
lean_dec(v_cfg_2178_);
v_cfg_2178_ = v___x_2261_;
goto _start;
}
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = l_Lean_Syntax_getArgs(v_cfg_2178_);
lean_dec(v_cfg_2178_);
v___x_2264_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2175_, v_inst_2176_, v_init_2177_, v___x_2263_, v_k_2179_, v_onErr_2180_);
return v___x_2264_;
}
v___jp_2181_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2185_ = l_Lean_TSyntax_getId(v___y_2182_);
v___x_2186_ = l_Lean_Name_eraseMacroScopes(v___x_2185_);
lean_dec(v___x_2185_);
v___x_2187_ = lean_box(0);
lean_inc(v___y_2182_);
v___x_2188_ = l_Lean_Syntax_identComponents(v___y_2182_, v___x_2187_);
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2190_, 0, v_cfg_2178_);
lean_ctor_set(v___x_2190_, 1, v___y_2182_);
lean_ctor_set(v___x_2190_, 2, v___y_2184_);
lean_ctor_set(v___x_2190_, 3, v___y_2183_);
lean_ctor_set(v___x_2190_, 4, v___x_2186_);
lean_ctor_set(v___x_2190_, 5, v___x_2188_);
lean_ctor_set(v___x_2190_, 6, v___x_2189_);
v___x_2191_ = lean_apply_2(v_k_2179_, v_init_2177_, v___x_2190_);
return v___x_2191_;
}
v___jp_2192_:
{
lean_object* v_toBind_2193_; lean_object* v_getRef_2194_; lean_object* v_withRef_2195_; lean_object* v___x_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; 
v_toBind_2193_ = lean_ctor_get(v_inst_2175_, 1);
lean_inc(v_toBind_2193_);
lean_dec_ref(v_inst_2175_);
v_getRef_2194_ = lean_ctor_get(v_inst_2176_, 0);
lean_inc(v_getRef_2194_);
v_withRef_2195_ = lean_ctor_get(v_inst_2176_, 1);
lean_inc(v_withRef_2195_);
lean_dec_ref(v_inst_2176_);
lean_inc(v_cfg_2178_);
v___x_2196_ = lean_apply_2(v_onErr_2180_, v_init_2177_, v_cfg_2178_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2197_, 0, v_cfg_2178_);
lean_closure_set(v___f_2197_, 1, v_withRef_2195_);
lean_closure_set(v___f_2197_, 2, v___x_2196_);
v___x_2198_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v_getRef_2194_, v___f_2197_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_k_2267_, lean_object* v_onErr_2268_, lean_object* v_x_2269_, lean_object* v_cfg_x27_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2265_, v_inst_2266_, v_x_2269_, v_cfg_x27_2270_, v_k_2267_, v_onErr_2268_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object* v_00_u03b1_2272_, lean_object* v_m_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_init_2276_, lean_object* v_cfg_2277_, lean_object* v_k_2278_, lean_object* v_onErr_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2274_, v_inst_2275_, v_init_2276_, v_cfg_2277_, v_k_2278_, v_onErr_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object* v_00_u03b1_2281_, lean_object* v_m_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_init_2285_, lean_object* v_cfgs_2286_, lean_object* v_k_2287_, lean_object* v_onErr_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2283_, v_inst_2284_, v_init_2285_, v_cfgs_2286_, v_k_2287_, v_onErr_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_2298_, lean_object* v_x_2299_){
_start:
{
if (lean_obj_tag(v_x_2299_) == 1)
{
lean_object* v_pre_2300_; 
v_pre_2300_ = lean_ctor_get(v_x_2299_, 0);
switch(lean_obj_tag(v_pre_2300_))
{
case 1:
{
lean_object* v_pre_2301_; 
v_pre_2301_ = lean_ctor_get(v_pre_2300_, 0);
switch(lean_obj_tag(v_pre_2301_))
{
case 0:
{
lean_object* v_str_2302_; lean_object* v_str_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v_str_2302_ = lean_ctor_get(v_x_2299_, 1);
v_str_2303_ = lean_ctor_get(v_pre_2300_, 1);
v___x_2304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_2305_ = lean_string_dec_eq(v_str_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_2307_ = lean_string_dec_eq(v_str_2303_, v___x_2306_);
if (v___x_2307_ == 0)
{
return v___x_2307_;
}
else
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_2309_ = lean_string_dec_eq(v_str_2302_, v___x_2308_);
if (v___x_2309_ == 0)
{
return v___x_2309_;
}
else
{
return v_suppressElabErrors_2298_;
}
}
}
else
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_2311_ = lean_string_dec_eq(v_str_2302_, v___x_2310_);
if (v___x_2311_ == 0)
{
return v___x_2311_;
}
else
{
return v_suppressElabErrors_2298_;
}
}
}
case 1:
{
lean_object* v_pre_2312_; 
v_pre_2312_ = lean_ctor_get(v_pre_2301_, 0);
if (lean_obj_tag(v_pre_2312_) == 0)
{
lean_object* v_str_2313_; lean_object* v_str_2314_; lean_object* v_str_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_str_2313_ = lean_ctor_get(v_x_2299_, 1);
v_str_2314_ = lean_ctor_get(v_pre_2300_, 1);
v_str_2315_ = lean_ctor_get(v_pre_2301_, 1);
v___x_2316_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_2317_ = lean_string_dec_eq(v_str_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_2319_ = lean_string_dec_eq(v_str_2314_, v___x_2318_);
if (v___x_2319_ == 0)
{
return v___x_2319_;
}
else
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_2321_ = lean_string_dec_eq(v_str_2313_, v___x_2320_);
if (v___x_2321_ == 0)
{
return v___x_2321_;
}
else
{
return v_suppressElabErrors_2298_;
}
}
}
}
else
{
uint8_t v___x_2322_; 
v___x_2322_ = 0;
return v___x_2322_;
}
}
default: 
{
uint8_t v___x_2323_; 
v___x_2323_ = 0;
return v___x_2323_;
}
}
}
case 0:
{
lean_object* v_str_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_str_2324_ = lean_ctor_get(v_x_2299_, 1);
v___x_2325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_2326_ = lean_string_dec_eq(v_str_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
return v___x_2326_;
}
else
{
return v_suppressElabErrors_2298_;
}
}
default: 
{
uint8_t v___x_2327_; 
v___x_2327_ = 0;
return v___x_2327_;
}
}
}
else
{
uint8_t v___x_2328_; 
v___x_2328_ = 0;
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2329_, lean_object* v_x_2330_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2331_; uint8_t v_res_2332_; lean_object* v_r_2333_; 
v_suppressElabErrors_boxed_2331_ = lean_unbox(v_suppressElabErrors_2329_);
v_res_2332_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_2331_, v_x_2330_);
lean_dec(v_x_2330_);
v_r_2333_ = lean_box(v_res_2332_);
return v_r_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2334_, lean_object* v_msgData_2335_, uint8_t v_severity_2336_, uint8_t v_isSilent_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___y_2344_; uint8_t v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; uint8_t v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v_toCold_2351_; lean_object* v___y_2352_; lean_object* v___y_2381_; lean_object* v___y_2382_; uint8_t v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; uint8_t v___y_2386_; uint8_t v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2408_; lean_object* v___y_2409_; uint8_t v___y_2410_; lean_object* v___y_2411_; uint8_t v___y_2412_; uint8_t v___y_2413_; lean_object* v___y_2414_; uint8_t v___y_2418_; uint8_t v___y_2419_; uint8_t v___x_2429_; uint8_t v___y_2431_; uint8_t v___x_2437_; 
v___x_2429_ = 2;
v___x_2437_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2336_, v___x_2429_);
if (v___x_2437_ == 0)
{
v___y_2431_ = v___x_2437_;
goto v___jp_2430_;
}
else
{
uint8_t v___x_2438_; 
lean_inc_ref(v_msgData_2335_);
v___x_2438_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2335_);
if (v___x_2438_ == 0)
{
v___y_2431_ = v___x_2438_;
goto v___jp_2430_;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v_msgData_2335_);
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
v___jp_2343_:
{
lean_object* v_currNamespace_2353_; lean_object* v_openDecls_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_env_2359_; lean_object* v_nextMacroScope_2360_; lean_object* v_ngen_2361_; lean_object* v_auxDeclNGen_2362_; lean_object* v_traceState_2363_; lean_object* v_cache_2364_; lean_object* v_recordedDeps_2365_; lean_object* v_messages_2366_; lean_object* v_infoState_2367_; lean_object* v_snapshotTasks_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2379_; 
v_currNamespace_2353_ = lean_ctor_get(v_toCold_2351_, 4);
v_openDecls_2354_ = lean_ctor_get(v_toCold_2351_, 5);
lean_inc(v_openDecls_2354_);
lean_inc(v_currNamespace_2353_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_currNamespace_2353_);
lean_ctor_set(v___x_2355_, 1, v_openDecls_2354_);
v___x_2356_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v___y_2349_);
lean_inc_ref(v___y_2346_);
lean_inc_ref(v___y_2344_);
v___x_2357_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2357_, 0, v___y_2344_);
lean_ctor_set(v___x_2357_, 1, v___y_2350_);
lean_ctor_set(v___x_2357_, 2, v___y_2347_);
lean_ctor_set(v___x_2357_, 3, v___y_2346_);
lean_ctor_set(v___x_2357_, 4, v___x_2356_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*5, v___y_2348_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*5 + 1, v___y_2345_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*5 + 2, v_isSilent_2337_);
v___x_2358_ = lean_st_ref_take(v___y_2352_);
v_env_2359_ = lean_ctor_get(v___x_2358_, 0);
v_nextMacroScope_2360_ = lean_ctor_get(v___x_2358_, 1);
v_ngen_2361_ = lean_ctor_get(v___x_2358_, 2);
v_auxDeclNGen_2362_ = lean_ctor_get(v___x_2358_, 3);
v_traceState_2363_ = lean_ctor_get(v___x_2358_, 4);
v_cache_2364_ = lean_ctor_get(v___x_2358_, 5);
v_recordedDeps_2365_ = lean_ctor_get(v___x_2358_, 6);
v_messages_2366_ = lean_ctor_get(v___x_2358_, 7);
v_infoState_2367_ = lean_ctor_get(v___x_2358_, 8);
v_snapshotTasks_2368_ = lean_ctor_get(v___x_2358_, 9);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2370_ = v___x_2358_;
v_isShared_2371_ = v_isSharedCheck_2379_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snapshotTasks_2368_);
lean_inc(v_infoState_2367_);
lean_inc(v_messages_2366_);
lean_inc(v_recordedDeps_2365_);
lean_inc(v_cache_2364_);
lean_inc(v_traceState_2363_);
lean_inc(v_auxDeclNGen_2362_);
lean_inc(v_ngen_2361_);
lean_inc(v_nextMacroScope_2360_);
lean_inc(v_env_2359_);
lean_dec(v___x_2358_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2379_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = l_Lean_MessageLog_add(v___x_2357_, v_messages_2366_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 7, v___x_2373_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_env_2359_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_nextMacroScope_2360_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v_ngen_2361_);
lean_ctor_set(v_reuseFailAlloc_2378_, 3, v_auxDeclNGen_2362_);
lean_ctor_set(v_reuseFailAlloc_2378_, 4, v_traceState_2363_);
lean_ctor_set(v_reuseFailAlloc_2378_, 5, v_cache_2364_);
lean_ctor_set(v_reuseFailAlloc_2378_, 6, v_recordedDeps_2365_);
lean_ctor_set(v_reuseFailAlloc_2378_, 7, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2378_, 8, v_infoState_2367_);
lean_ctor_set(v_reuseFailAlloc_2378_, 9, v_snapshotTasks_2368_);
v___x_2375_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_st_ref_put(v___y_2352_, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2372_);
return v___x_2377_;
}
}
}
v___jp_2380_:
{
lean_object* v_fileName_2389_; lean_object* v_fileMap_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2406_; 
v_fileName_2389_ = lean_ctor_get(v___y_2385_, 0);
v_fileMap_2390_ = lean_ctor_get(v___y_2385_, 1);
v___x_2391_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2335_);
v___x_2392_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_2391_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2406_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2406_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_inc_ref_n(v_fileMap_2390_, 2);
v___x_2397_ = l_Lean_FileMap_toPosition(v_fileMap_2390_, v___y_2384_);
lean_dec(v___y_2384_);
v___x_2398_ = l_Lean_FileMap_toPosition(v_fileMap_2390_, v___y_2388_);
lean_dec(v___y_2388_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
v___x_2400_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
if (v___y_2387_ == 0)
{
lean_del_object(v___x_2395_);
lean_dec_ref(v___y_2381_);
v___y_2344_ = v_fileName_2389_;
v___y_2345_ = v___y_2383_;
v___y_2346_ = v___x_2400_;
v___y_2347_ = v___x_2399_;
v___y_2348_ = v___y_2386_;
v___y_2349_ = v_a_2393_;
v___y_2350_ = v___x_2397_;
v_toCold_2351_ = v___y_2382_;
v___y_2352_ = v___y_2341_;
goto v___jp_2343_;
}
else
{
uint8_t v___x_2401_; 
lean_inc(v_a_2393_);
v___x_2401_ = l_Lean_MessageData_hasTag(v___y_2381_, v_a_2393_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_dec_ref_known(v___x_2399_, 1);
lean_dec_ref(v___x_2397_);
lean_dec(v_a_2393_);
v___x_2402_ = lean_box(0);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2402_);
v___x_2404_ = v___x_2395_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
else
{
lean_del_object(v___x_2395_);
v___y_2344_ = v_fileName_2389_;
v___y_2345_ = v___y_2383_;
v___y_2346_ = v___x_2400_;
v___y_2347_ = v___x_2399_;
v___y_2348_ = v___y_2386_;
v___y_2349_ = v_a_2393_;
v___y_2350_ = v___x_2397_;
v_toCold_2351_ = v___y_2382_;
v___y_2352_ = v___y_2341_;
goto v___jp_2343_;
}
}
}
}
v___jp_2407_:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Syntax_getTailPos_x3f(v___y_2411_, v___y_2413_);
lean_dec(v___y_2411_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_inc(v___y_2414_);
v___y_2381_ = v___y_2408_;
v___y_2382_ = v___y_2409_;
v___y_2383_ = v___y_2412_;
v___y_2384_ = v___y_2414_;
v___y_2385_ = v___y_2409_;
v___y_2386_ = v___y_2413_;
v___y_2387_ = v___y_2410_;
v___y_2388_ = v___y_2414_;
goto v___jp_2380_;
}
else
{
lean_object* v_val_2416_; 
v_val_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_val_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___y_2381_ = v___y_2408_;
v___y_2382_ = v___y_2409_;
v___y_2383_ = v___y_2412_;
v___y_2384_ = v___y_2414_;
v___y_2385_ = v___y_2409_;
v___y_2386_ = v___y_2413_;
v___y_2387_ = v___y_2410_;
v___y_2388_ = v_val_2416_;
goto v___jp_2380_;
}
}
v___jp_2417_:
{
lean_object* v_toCold_2420_; lean_object* v_ref_2421_; uint8_t v_suppressElabErrors_2422_; lean_object* v___x_2423_; lean_object* v___f_2424_; lean_object* v_ref_2425_; lean_object* v___x_2426_; 
v_toCold_2420_ = lean_ctor_get(v___y_2340_, 0);
v_ref_2421_ = lean_ctor_get(v___y_2340_, 2);
v_suppressElabErrors_2422_ = lean_ctor_get_uint8(v___y_2340_, sizeof(void*)*3 + 2);
v___x_2423_ = lean_box(v_suppressElabErrors_2422_);
v___f_2424_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2424_, 0, v___x_2423_);
v_ref_2425_ = l_Lean_replaceRef(v_ref_2334_, v_ref_2421_);
v___x_2426_ = l_Lean_Syntax_getPos_x3f(v_ref_2425_, v___y_2418_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_unsigned_to_nat(0u);
v___y_2408_ = v___f_2424_;
v___y_2409_ = v_toCold_2420_;
v___y_2410_ = v_suppressElabErrors_2422_;
v___y_2411_ = v_ref_2425_;
v___y_2412_ = v___y_2419_;
v___y_2413_ = v___y_2418_;
v___y_2414_ = v___x_2427_;
goto v___jp_2407_;
}
else
{
lean_object* v_val_2428_; 
v_val_2428_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_val_2428_);
lean_dec_ref_known(v___x_2426_, 1);
v___y_2408_ = v___f_2424_;
v___y_2409_ = v_toCold_2420_;
v___y_2410_ = v_suppressElabErrors_2422_;
v___y_2411_ = v_ref_2425_;
v___y_2412_ = v___y_2419_;
v___y_2413_ = v___y_2418_;
v___y_2414_ = v_val_2428_;
goto v___jp_2407_;
}
}
v___jp_2430_:
{
uint8_t v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = 1;
v___x_2433_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2336_, v___x_2432_);
if (v___x_2433_ == 0)
{
v___y_2418_ = v___y_2431_;
v___y_2419_ = v_severity_2336_;
goto v___jp_2417_;
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2434_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2340_);
v___x_2435_ = l_Lean_warningAsError;
v___x_2436_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_2434_, v___x_2435_);
lean_dec_ref(v___x_2434_);
if (v___x_2436_ == 0)
{
v___y_2418_ = v___y_2431_;
v___y_2419_ = v_severity_2336_;
goto v___jp_2417_;
}
else
{
v___y_2418_ = v___y_2431_;
v___y_2419_ = v___x_2429_;
goto v___jp_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2441_, lean_object* v_msgData_2442_, lean_object* v_severity_2443_, lean_object* v_isSilent_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
uint8_t v_severity_boxed_2450_; uint8_t v_isSilent_boxed_2451_; lean_object* v_res_2452_; 
v_severity_boxed_2450_ = lean_unbox(v_severity_2443_);
v_isSilent_boxed_2451_ = lean_unbox(v_isSilent_2444_);
v_res_2452_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2441_, v_msgData_2442_, v_severity_boxed_2450_, v_isSilent_boxed_2451_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v_ref_2441_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object* v_msgData_2453_, uint8_t v_severity_2454_, uint8_t v_isSilent_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_ref_2463_; lean_object* v___x_2464_; 
v_ref_2463_ = lean_ctor_get(v___y_2460_, 2);
v___x_2464_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2463_, v_msgData_2453_, v_severity_2454_, v_isSilent_2455_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2465_, lean_object* v_severity_2466_, lean_object* v_isSilent_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
uint8_t v_severity_boxed_2475_; uint8_t v_isSilent_boxed_2476_; lean_object* v_res_2477_; 
v_severity_boxed_2475_ = lean_unbox(v_severity_2466_);
v_isSilent_boxed_2476_ = lean_unbox(v_isSilent_2467_);
v_res_2477_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2465_, v_severity_boxed_2475_, v_isSilent_boxed_2476_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object* v_msgData_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v___x_2486_; uint8_t v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = 2;
v___x_2487_ = 0;
v___x_2488_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2478_, v___x_2486_, v___x_2487_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(lean_object* v_msgData_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object* v_ref_2498_, lean_object* v_msgData_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
uint8_t v___x_2507_; uint8_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = 2;
v___x_2508_ = 0;
v___x_2509_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2498_, v_msgData_2499_, v___x_2507_, v___x_2508_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object* v_ref_2510_, lean_object* v_msgData_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2510_, v_msgData_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v_ref_2510_);
return v_res_2519_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object* v_ex_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
if (lean_obj_tag(v_ex_2523_) == 0)
{
lean_object* v_ref_2534_; lean_object* v_msg_2535_; lean_object* v___x_2536_; 
v_ref_2534_ = lean_ctor_get(v_ex_2523_, 0);
lean_inc(v_ref_2534_);
v_msg_2535_ = lean_ctor_get(v_ex_2523_, 1);
lean_inc_ref(v_msg_2535_);
lean_dec_ref_known(v_ex_2523_, 2);
v___x_2536_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2534_, v_msg_2535_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v_ref_2534_);
return v___x_2536_;
}
else
{
lean_object* v_id_2537_; uint8_t v___x_2538_; 
v_id_2537_ = lean_ctor_get(v_ex_2523_, 0);
lean_inc(v_id_2537_);
v___x_2538_ = l_Lean_Elab_isAbortExceptionId(v_id_2537_);
if (v___x_2538_ == 0)
{
uint8_t v___x_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2564_; 
v___x_2539_ = l_Lean_Exception_isInterrupt(v_ex_2523_);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_ex_2523_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; lean_object* v_unused_2566_; 
v_unused_2565_ = lean_ctor_get(v_ex_2523_, 1);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_ex_2523_, 0);
lean_dec(v_unused_2566_);
v___x_2541_ = v_ex_2523_;
v_isShared_2542_ = v_isSharedCheck_2564_;
goto v_resetjp_2540_;
}
else
{
lean_dec(v_ex_2523_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2564_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
if (v___x_2539_ == 0)
{
lean_object* v_ref_2543_; lean_object* v___x_2544_; 
v_ref_2543_ = lean_ctor_get(v___y_2528_, 2);
v___x_2544_ = l_Lean_InternalExceptionId_getName(v_id_2537_);
lean_dec(v_id_2537_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
lean_del_object(v___x_2541_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
v___x_2547_ = l_Lean_MessageData_ofName(v_a_2545_);
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_2548_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v___x_2549_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2563_; 
v_a_2550_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2552_ = v___x_2544_;
v_isShared_2553_ = v_isSharedCheck_2563_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2544_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2563_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2554_ = lean_io_error_to_string(v_a_2550_);
v___x_2555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
v___x_2556_ = l_Lean_MessageData_ofFormat(v___x_2555_);
lean_inc(v_ref_2543_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 0);
lean_ctor_set(v___x_2541_, 1, v___x_2556_);
lean_ctor_set(v___x_2541_, 0, v_ref_2543_);
v___x_2558_ = v___x_2541_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_ref_2543_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2558_);
v___x_2560_ = v___x_2552_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
else
{
lean_del_object(v___x_2541_);
lean_dec(v_id_2537_);
goto v___jp_2531_;
}
}
}
else
{
lean_dec_ref_known(v_ex_2523_, 2);
lean_dec(v_id_2537_);
goto v___jp_2531_;
}
}
v___jp_2531_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_box(0);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object* v_ex_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object* v_a_2576_, lean_object* v_config_2577_, lean_object* v_____r_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_2576_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2594_; 
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2586_, 0);
lean_dec(v_unused_2595_);
v___x_2588_ = v___x_2586_;
v_isShared_2589_ = v_isSharedCheck_2594_;
goto v_resetjp_2587_;
}
else
{
lean_dec(v___x_2586_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2594_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v_config_2577_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2590_);
v___x_2592_ = v___x_2588_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_config_2577_);
v_a_2596_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2586_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2586_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object* v_a_2604_, lean_object* v_config_2605_, lean_object* v_____r_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2604_, v_config_2605_, v_____r_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object* v___f_2615_, lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_box(0);
lean_inc(v___y_2622_);
lean_inc_ref(v___y_2621_);
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
v___x_2625_ = lean_apply_8(v___f_2615_, v___x_2624_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, lean_box(0));
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(lean_object* v___f_2626_, lean_object* v_x_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2626_, v_x_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v_x_2627_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object* v_eval_2636_, lean_object* v_config_2637_, lean_object* v_item_2638_, uint8_t v_logExceptions_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v___y_2648_; lean_object* v___x_2666_; 
lean_inc(v_a_2645_);
lean_inc_ref(v_a_2644_);
lean_inc(v_a_2643_);
lean_inc_ref(v_a_2642_);
lean_inc(v_a_2641_);
lean_inc_ref(v_a_2640_);
lean_inc(v_config_2637_);
v___x_2666_ = lean_apply_9(v_eval_2636_, v_config_2637_, v_item_2638_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, lean_box(0));
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_dec(v_config_2637_);
return v___x_2666_;
}
else
{
lean_object* v_a_2667_; uint8_t v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
v___x_2668_ = l_Lean_Exception_isInterrupt(v_a_2667_);
if (v___x_2668_ == 0)
{
uint8_t v___x_2669_; 
lean_inc(v_a_2667_);
v___x_2669_ = l_Lean_Exception_isRuntime(v_a_2667_);
if (v___x_2669_ == 0)
{
if (v_logExceptions_2639_ == 0)
{
lean_dec(v_a_2667_);
lean_dec(v_config_2637_);
return v___x_2666_;
}
else
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2685_; 
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2686_);
v___x_2671_ = v___x_2666_;
v_isShared_2672_ = v_isSharedCheck_2685_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v___x_2666_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2685_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___f_2673_; 
lean_inc(v_config_2637_);
lean_inc(v_a_2667_);
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2673_, 0, v_a_2667_);
lean_closure_set(v___f_2673_, 1, v_config_2637_);
if (lean_obj_tag(v_a_2667_) == 1)
{
lean_object* v_extra_2674_; 
v_extra_2674_ = lean_ctor_get(v_a_2667_, 1);
if (lean_obj_tag(v_extra_2674_) == 0)
{
lean_object* v_id_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
lean_dec_ref(v___f_2673_);
v_id_2675_ = lean_ctor_get(v_a_2667_, 0);
v___x_2676_ = l_Lean_Elab_abortTermExceptionId;
v___x_2677_ = l_Lean_instBEqInternalExceptionId_beq(v_id_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2671_);
v___x_2678_ = lean_box(0);
v___x_2679_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2667_, v_config_2637_, v___x_2678_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
v___y_2648_ = v___x_2679_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2681_; 
lean_dec_ref_known(v_a_2667_, 2);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 0);
lean_ctor_set(v___x_2671_, 0, v_config_2637_);
v___x_2681_ = v___x_2671_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_config_2637_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
lean_object* v___x_2683_; 
lean_del_object(v___x_2671_);
lean_dec(v_config_2637_);
v___x_2683_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2673_, v_a_2667_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec_ref_known(v_a_2667_, 2);
v___y_2648_ = v___x_2683_;
goto v___jp_2647_;
}
}
else
{
lean_object* v___x_2684_; 
lean_del_object(v___x_2671_);
lean_dec(v_config_2637_);
v___x_2684_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2673_, v_a_2667_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2667_);
v___y_2648_ = v___x_2684_;
goto v___jp_2647_;
}
}
}
}
else
{
lean_dec(v_a_2667_);
lean_dec(v_config_2637_);
return v___x_2666_;
}
}
else
{
lean_dec(v_a_2667_);
lean_dec(v_config_2637_);
return v___x_2666_;
}
}
v___jp_2647_:
{
if (lean_obj_tag(v___y_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2657_; 
v_a_2649_ = lean_ctor_get(v___y_2648_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___y_2648_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2651_ = v___y_2648_;
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___y_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_a_2653_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_a_2653_);
lean_dec(v_a_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v_a_2653_);
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v_a_2658_ = lean_ctor_get(v___y_2648_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___y_2648_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___y_2648_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___y_2648_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object* v_eval_2687_, lean_object* v_config_2688_, lean_object* v_item_2689_, lean_object* v_logExceptions_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
uint8_t v_logExceptions_boxed_2698_; lean_object* v_res_2699_; 
v_logExceptions_boxed_2698_ = lean_unbox(v_logExceptions_2690_);
v_res_2699_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2687_, v_config_2688_, v_item_2689_, v_logExceptions_boxed_2698_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object* v_00_u03b1_2700_, lean_object* v_eval_2701_, lean_object* v_config_2702_, lean_object* v_item_2703_, uint8_t v_logExceptions_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2701_, v_config_2702_, v_item_2703_, v_logExceptions_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_eval_2714_, lean_object* v_config_2715_, lean_object* v_item_2716_, lean_object* v_logExceptions_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
uint8_t v_logExceptions_boxed_2725_; lean_object* v_res_2726_; 
v_logExceptions_boxed_2725_ = lean_unbox(v_logExceptions_2717_);
v_res_2726_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(v_00_u03b1_2713_, v_eval_2714_, v_config_2715_, v_item_2716_, v_logExceptions_boxed_2725_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object* v_ref_2727_, lean_object* v_msgData_2728_, uint8_t v_severity_2729_, uint8_t v_isSilent_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2727_, v_msgData_2728_, v_severity_2729_, v_isSilent_2730_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2739_, lean_object* v_msgData_2740_, lean_object* v_severity_2741_, lean_object* v_isSilent_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v_severity_boxed_2750_; uint8_t v_isSilent_boxed_2751_; lean_object* v_res_2752_; 
v_severity_boxed_2750_ = lean_unbox(v_severity_2741_);
v_isSilent_boxed_2751_ = lean_unbox(v_isSilent_2742_);
v_res_2752_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2739_, v_msgData_2740_, v_severity_boxed_2750_, v_isSilent_boxed_2751_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v_ref_2739_);
return v_res_2752_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v___x_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg(){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object* v_00_u03b1_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object* v_00_u03b1_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2778_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = l_Lean_Level_ofNat(v___x_2782_);
return v___x_2783_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2784_ = lean_box(0);
v___x_2785_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___x_2784_);
return v___x_2786_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3);
v___x_2788_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1));
v___x_2789_ = l_Lean_Expr_const___override(v___x_2788_, v___x_2787_);
return v___x_2789_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2793_ = lean_box(0);
v___x_2794_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6));
v___x_2795_ = l_Lean_Expr_const___override(v___x_2794_, v___x_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object* v_cfg_2799_, lean_object* v_cfgItem_2800_, lean_object* v_cfgType_x3f_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; 
if (lean_obj_tag(v_cfgType_x3f_2801_) == 1)
{
lean_object* v_val_2819_; lean_object* v___x_2820_; lean_object* v_infoState_2821_; uint8_t v_enabled_2822_; 
v_val_2819_ = lean_ctor_get(v_cfgType_x3f_2801_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v_cfgType_x3f_2801_, 1);
v___x_2820_ = lean_st_ref_get(v_a_2807_);
v_infoState_2821_ = lean_ctor_get(v___x_2820_, 8);
lean_inc_ref(v_infoState_2821_);
lean_dec(v___x_2820_);
v_enabled_2822_ = lean_ctor_get_uint8(v_infoState_2821_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2821_);
if (v_enabled_2822_ == 0)
{
lean_dec(v_val_2819_);
v___y_2810_ = v_a_2802_;
v___y_2811_ = v_a_2803_;
v___y_2812_ = v_a_2804_;
v___y_2813_ = v_a_2805_;
v___y_2814_ = v_a_2806_;
v___y_2815_ = v_a_2807_;
goto v___jp_2809_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = l_Lean_Syntax_getArg(v_cfgItem_2800_, v___x_2823_);
v___x_2825_ = l_Lean_Syntax_isAtom(v___x_2824_);
if (v___x_2825_ == 0)
{
lean_dec(v___x_2824_);
lean_dec(v_val_2819_);
v___y_2810_ = v_a_2802_;
v___y_2811_ = v_a_2803_;
v___y_2812_ = v_a_2804_;
v___y_2813_ = v_a_2805_;
v___y_2814_ = v_a_2806_;
v___y_2815_ = v_a_2807_;
goto v___jp_2809_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2826_ = lean_unsigned_to_nat(1u);
v___x_2827_ = l_Lean_Syntax_getArg(v_cfgItem_2800_, v___x_2826_);
v___x_2828_ = l_Lean_Syntax_isMissing(v___x_2827_);
lean_dec(v___x_2827_);
if (v___x_2828_ == 0)
{
lean_dec(v___x_2824_);
lean_dec(v_val_2819_);
v___y_2810_ = v_a_2802_;
v___y_2811_ = v_a_2803_;
v___y_2812_ = v_a_2804_;
v___y_2813_ = v_a_2805_;
v___y_2814_ = v_a_2806_;
v___y_2815_ = v_a_2807_;
goto v___jp_2809_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2829_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
v___x_2830_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
v___x_2831_ = l_Lean_mkAppB(v___x_2829_, v_val_2819_, v___x_2830_);
v___x_2832_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9));
v___x_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
lean_ctor_set(v___x_2833_, 1, v___x_2824_);
v___x_2834_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2835_ = lean_box(0);
v___x_2836_ = 0;
v___x_2837_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2837_, 0, v___x_2833_);
lean_ctor_set(v___x_2837_, 1, v___x_2834_);
lean_ctor_set(v___x_2837_, 2, v___x_2835_);
lean_ctor_set(v___x_2837_, 3, v___x_2831_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*4, v___x_2836_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*4 + 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v___x_2835_);
v___x_2839_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2838_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
lean_dec_ref(v___x_2839_);
v___y_2810_ = v_a_2802_;
v___y_2811_ = v_a_2803_;
v___y_2812_ = v_a_2804_;
v___y_2813_ = v_a_2805_;
v___y_2814_ = v_a_2806_;
v___y_2815_ = v_a_2807_;
goto v___jp_2809_;
}
}
}
}
else
{
lean_dec(v_cfgType_x3f_2801_);
v___y_2810_ = v_a_2802_;
v___y_2811_ = v_a_2803_;
v___y_2812_ = v_a_2804_;
v___y_2813_ = v_a_2805_;
v___y_2814_ = v_a_2806_;
v___y_2815_ = v_a_2807_;
goto v___jp_2809_;
}
v___jp_2809_:
{
uint8_t v___x_2816_; 
v___x_2816_ = l_Lean_Syntax_hasMissing(v_cfgItem_2800_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
lean_dec(v_cfg_2799_);
v___x_2817_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2817_;
}
else
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_cfg_2799_);
return v___x_2818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object* v_cfg_2840_, lean_object* v_cfgItem_2841_, lean_object* v_cfgType_x3f_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2840_, v_cfgItem_2841_, v_cfgType_x3f_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_cfgItem_2841_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object* v_00_u03b1_2851_, lean_object* v_cfg_2852_, lean_object* v_cfgItem_2853_, lean_object* v_cfgType_x3f_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2852_, v_cfgItem_2853_, v_cfgType_x3f_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object* v_00_u03b1_2863_, lean_object* v_cfg_2864_, lean_object* v_cfgItem_2865_, lean_object* v_cfgType_x3f_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(v_00_u03b1_2863_, v_cfg_2864_, v_cfgItem_2865_, v_cfgType_x3f_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_cfgItem_2865_);
return v_res_2874_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_s_2875_, lean_object* v_a_2876_, uint8_t v_b_2877_){
_start:
{
lean_object* v_str_2878_; lean_object* v_startInclusive_2879_; lean_object* v_endExclusive_2880_; lean_object* v___x_2881_; uint8_t v_decide_2882_; 
v_str_2878_ = lean_ctor_get(v_s_2875_, 0);
v_startInclusive_2879_ = lean_ctor_get(v_s_2875_, 1);
v_endExclusive_2880_ = lean_ctor_get(v_s_2875_, 2);
v___x_2881_ = lean_nat_sub(v_endExclusive_2880_, v_startInclusive_2879_);
v_decide_2882_ = lean_nat_dec_eq(v_a_2876_, v___x_2881_);
lean_dec(v___x_2881_);
if (v_decide_2882_ == 0)
{
lean_object* v___x_2883_; uint32_t v___x_2884_; uint32_t v___x_2885_; uint8_t v___x_2886_; 
v___x_2883_ = lean_nat_add(v_startInclusive_2879_, v_a_2876_);
lean_dec(v_a_2876_);
v___x_2884_ = lean_string_utf8_get_fast(v_str_2878_, v___x_2883_);
v___x_2885_ = 46;
v___x_2886_ = lean_uint32_dec_eq(v___x_2884_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_string_utf8_next_fast(v_str_2878_, v___x_2883_);
lean_dec(v___x_2883_);
v___x_2888_ = lean_nat_sub(v___x_2887_, v_startInclusive_2879_);
v_a_2876_ = v___x_2888_;
v_b_2877_ = v___x_2886_;
goto _start;
}
else
{
lean_dec(v___x_2883_);
return v___x_2886_;
}
}
else
{
lean_dec(v_a_2876_);
return v_b_2877_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_s_2890_, lean_object* v_a_2891_, lean_object* v_b_2892_){
_start:
{
uint8_t v_b_boxed_2893_; uint8_t v_res_2894_; lean_object* v_r_2895_; 
v_b_boxed_2893_ = lean_unbox(v_b_2892_);
v_res_2894_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2890_, v_a_2891_, v_b_boxed_2893_);
lean_dec_ref(v_s_2890_);
v_r_2895_ = lean_box(v_res_2894_);
return v_r_2895_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object* v_s_2896_){
_start:
{
lean_object* v_searcher_2897_; uint8_t v___x_2898_; uint8_t v___x_2899_; 
v_searcher_2897_ = lean_unsigned_to_nat(0u);
v___x_2898_ = 0;
v___x_2899_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2896_, v_searcher_2897_, v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object* v_s_2900_){
_start:
{
uint8_t v_res_2901_; lean_object* v_r_2902_; 
v_res_2901_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2900_);
lean_dec_ref(v_s_2900_);
v_r_2902_ = lean_box(v_res_2901_);
return v_r_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object* v_si_2903_, lean_object* v_val_2904_){
_start:
{
lean_object* v___y_2906_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2912_ = lean_unsigned_to_nat(0u);
v___x_2913_ = lean_string_utf8_byte_size(v_val_2904_);
lean_inc_ref(v_val_2904_);
v___x_2914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2914_, 0, v_val_2904_);
lean_ctor_set(v___x_2914_, 1, v___x_2912_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
v___x_2915_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_2914_);
lean_dec_ref_known(v___x_2914_, 3);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_box(0);
lean_inc_ref(v_val_2904_);
v___x_2917_ = l_Lean_Name_str___override(v___x_2916_, v_val_2904_);
v___y_2906_ = v___x_2917_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_2918_; 
lean_inc_ref(v_val_2904_);
v___x_2918_ = l_String_toName(v_val_2904_);
v___y_2906_ = v___x_2918_;
goto v___jp_2905_;
}
v___jp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = lean_string_utf8_byte_size(v_val_2904_);
v___x_2909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2909_, 0, v_val_2904_);
lean_ctor_set(v___x_2909_, 1, v___x_2907_);
lean_ctor_set(v___x_2909_, 2, v___x_2908_);
v___x_2910_ = lean_box(0);
v___x_2911_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2911_, 0, v_si_2903_);
lean_ctor_set(v___x_2911_, 1, v___x_2909_);
lean_ctor_set(v___x_2911_, 2, v___y_2906_);
lean_ctor_set(v___x_2911_, 3, v___x_2910_);
return v___x_2911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object* v_eval_2920_, uint8_t v_logExceptions_2921_, lean_object* v_onErr_2922_, lean_object* v_init_2923_, lean_object* v_cfg_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2954_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2924_);
v___x_2955_ = l_Lean_Syntax_isOfKind(v_cfg_2924_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = l_Lean_Syntax_getNumArgs(v_cfg_2924_);
v___x_2957_ = lean_unsigned_to_nat(1u);
v___x_2958_ = lean_nat_dec_eq(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v_atomAsIdent_2959_; uint8_t v___x_2960_; 
v_atomAsIdent_2959_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0));
v___x_2960_ = lean_nat_dec_le(v___x_2957_, v___x_2956_);
if (v___x_2960_ == 0)
{
lean_dec(v___x_2956_);
if (lean_obj_tag(v_cfg_2924_) == 2)
{
lean_object* v_info_2961_; lean_object* v_val_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec_ref(v_onErr_2922_);
v_info_2961_ = lean_ctor_get(v_cfg_2924_, 0);
v_val_2962_ = lean_ctor_get(v_cfg_2924_, 1);
lean_inc_ref(v_val_2962_);
lean_inc(v_info_2961_);
v___x_2963_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_2961_, v_val_2962_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2965_ = l_Lean_mkCIdentFrom(v_cfg_2924_, v___x_2964_, v___x_2960_);
v___x_2966_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2967_ = l_Lean_TSyntax_getId(v___x_2963_);
v___x_2968_ = l_Lean_Name_eraseMacroScopes(v___x_2967_);
lean_dec(v___x_2967_);
v___x_2969_ = lean_box(0);
lean_inc(v___x_2963_);
v___x_2970_ = l_Lean_Syntax_identComponents(v___x_2963_, v___x_2969_);
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2972_, 0, v_cfg_2924_);
lean_ctor_set(v___x_2972_, 1, v___x_2963_);
lean_ctor_set(v___x_2972_, 2, v___x_2965_);
lean_ctor_set(v___x_2972_, 3, v___x_2966_);
lean_ctor_set(v___x_2972_, 4, v___x_2968_);
lean_ctor_set(v___x_2972_, 5, v___x_2970_);
lean_ctor_set(v___x_2972_, 6, v___x_2971_);
v___x_2973_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2920_, v_init_2923_, v___x_2972_, v_logExceptions_2921_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
return v___x_2973_;
}
else
{
lean_dec_ref(v_eval_2920_);
goto v___jp_2943_;
}
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = lean_unsigned_to_nat(0u);
v___x_2975_ = l_Lean_Syntax_getArg(v_cfg_2924_, v___x_2974_);
if (lean_obj_tag(v___x_2975_) == 2)
{
lean_object* v_val_2976_; lean_object* v___y_2978_; uint8_t v_val_2979_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v_val_2976_ = lean_ctor_get(v___x_2975_, 1);
v___x_2990_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2991_ = lean_string_dec_eq(v_val_2976_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2993_ = lean_string_dec_eq(v_val_2976_, v___x_2992_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
lean_inc_ref(v_val_2976_);
lean_dec_ref_known(v___x_2975_, 2);
v___x_2994_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2995_ = lean_string_dec_eq(v_val_2976_, v___x_2994_);
lean_dec_ref(v_val_2976_);
if (v___x_2995_ == 0)
{
lean_dec(v___x_2956_);
lean_dec_ref(v_eval_2920_);
goto v___jp_2943_;
}
else
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = lean_unsigned_to_nat(5u);
v___x_2997_ = lean_nat_dec_le(v___x_2956_, v___x_2996_);
lean_dec(v___x_2956_);
if (v___x_2997_ == 0)
{
lean_dec_ref(v_eval_2920_);
goto v___jp_2943_;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = l_Lean_Syntax_getArg(v_cfg_2924_, v___x_2957_);
v___x_2999_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2959_, v___x_2998_);
if (lean_obj_tag(v___x_2999_) == 1)
{
lean_object* v_val_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec_ref(v_onErr_2922_);
v_val_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_n(v_val_3000_, 2);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = lean_unsigned_to_nat(3u);
v___x_3002_ = l_Lean_Syntax_getArg(v_cfg_2924_, v___x_3001_);
v___x_3003_ = lean_box(0);
v___x_3004_ = l_Lean_TSyntax_getId(v_val_3000_);
v___x_3005_ = l_Lean_Name_eraseMacroScopes(v___x_3004_);
lean_dec(v___x_3004_);
v___x_3006_ = l_Lean_Syntax_identComponents(v_val_3000_, v___x_3003_);
v___x_3007_ = lean_box(0);
v___x_3008_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3008_, 0, v_cfg_2924_);
lean_ctor_set(v___x_3008_, 1, v_val_3000_);
lean_ctor_set(v___x_3008_, 2, v___x_3002_);
lean_ctor_set(v___x_3008_, 3, v___x_3003_);
lean_ctor_set(v___x_3008_, 4, v___x_3005_);
lean_ctor_set(v___x_3008_, 5, v___x_3006_);
lean_ctor_set(v___x_3008_, 6, v___x_3007_);
v___x_3009_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2920_, v_init_2923_, v___x_3008_, v_logExceptions_2921_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
return v___x_3009_;
}
else
{
lean_dec(v___x_2999_);
lean_dec_ref(v_eval_2920_);
goto v___jp_2943_;
}
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_box(v___x_2991_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
v___y_2978_ = v___x_3011_;
v_val_2979_ = v___x_2991_;
goto v___jp_2977_;
}
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = lean_box(v___x_2960_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
v___y_2978_ = v___x_3013_;
v_val_2979_ = v___x_2960_;
goto v___jp_2977_;
}
v___jp_2977_:
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = lean_unsigned_to_nat(2u);
v___x_2981_ = lean_nat_dec_eq(v___x_2956_, v___x_2980_);
lean_dec(v___x_2956_);
if (v___x_2981_ == 0)
{
lean_dec(v___y_2978_);
lean_dec_ref_known(v___x_2975_, 2);
lean_dec_ref(v_eval_2920_);
goto v___jp_2943_;
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = l_Lean_Syntax_getArg(v_cfg_2924_, v___x_2957_);
v___x_2983_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2959_, v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 1)
{
lean_dec_ref(v_onErr_2922_);
if (v_val_2979_ == 0)
{
lean_object* v_val_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_val_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2986_ = l_Lean_mkCIdentFrom(v___x_2975_, v___x_2985_, v_val_2979_);
lean_dec_ref_known(v___x_2975_, 2);
v___y_2933_ = v_val_2984_;
v___y_2934_ = v___y_2978_;
v___y_2935_ = v___x_2986_;
goto v___jp_2932_;
}
else
{
lean_object* v_val_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_val_2987_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2987_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2988_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2989_ = l_Lean_mkCIdentFrom(v___x_2975_, v___x_2988_, v___x_2958_);
lean_dec_ref_known(v___x_2975_, 2);
v___y_2933_ = v_val_2987_;
v___y_2934_ = v___y_2978_;
v___y_2935_ = v___x_2989_;
goto v___jp_2932_;
}
}
else
{
lean_dec(v___x_2983_);
lean_dec(v___y_2978_);
lean_dec_ref_known(v___x_2975_, 2);
lean_dec_ref(v_eval_2920_);
goto v___jp_2943_;
}
}
}
}
else
{
lean_dec(v___x_2975_);
lean_dec(v___x_2956_);
lean_dec_ref(v_eval_2920_);
goto v___jp_2943_;
}
}
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec(v___x_2956_);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = l_Lean_Syntax_getArg(v_cfg_2924_, v___x_3014_);
lean_dec(v_cfg_2924_);
v_cfg_2924_ = v___x_3015_;
goto _start;
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = l_Lean_Syntax_getArgs(v_cfg_2924_);
lean_dec(v_cfg_2924_);
v___x_3018_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_2920_, v_logExceptions_2921_, v_onErr_2922_, v_init_2923_, v___x_3017_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec_ref(v___x_3017_);
return v___x_3018_;
}
v___jp_2932_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2936_ = l_Lean_TSyntax_getId(v___y_2933_);
v___x_2937_ = l_Lean_Name_eraseMacroScopes(v___x_2936_);
lean_dec(v___x_2936_);
v___x_2938_ = lean_box(0);
lean_inc(v___y_2933_);
v___x_2939_ = l_Lean_Syntax_identComponents(v___y_2933_, v___x_2938_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2941_, 0, v_cfg_2924_);
lean_ctor_set(v___x_2941_, 1, v___y_2933_);
lean_ctor_set(v___x_2941_, 2, v___y_2935_);
lean_ctor_set(v___x_2941_, 3, v___y_2934_);
lean_ctor_set(v___x_2941_, 4, v___x_2937_);
lean_ctor_set(v___x_2941_, 5, v___x_2939_);
lean_ctor_set(v___x_2941_, 6, v___x_2940_);
v___x_2942_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2920_, v_init_2923_, v___x_2941_, v_logExceptions_2921_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
return v___x_2942_;
}
v___jp_2943_:
{
lean_object* v_toCold_2944_; lean_object* v_currRecDepth_2945_; lean_object* v_ref_2946_; uint16_t v_optionFlags_2947_; uint8_t v_suppressElabErrors_2948_; uint8_t v_checkDeprecated_2949_; uint8_t v_isRecordingDeps_2950_; lean_object* v_ref_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_toCold_2944_ = lean_ctor_get(v___y_2929_, 0);
v_currRecDepth_2945_ = lean_ctor_get(v___y_2929_, 1);
v_ref_2946_ = lean_ctor_get(v___y_2929_, 2);
v_optionFlags_2947_ = lean_ctor_get_uint16(v___y_2929_, sizeof(void*)*3);
v_suppressElabErrors_2948_ = lean_ctor_get_uint8(v___y_2929_, sizeof(void*)*3 + 2);
v_checkDeprecated_2949_ = lean_ctor_get_uint8(v___y_2929_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2950_ = lean_ctor_get_uint8(v___y_2929_, sizeof(void*)*3 + 4);
v_ref_2951_ = l_Lean_replaceRef(v_cfg_2924_, v_ref_2946_);
lean_inc(v_currRecDepth_2945_);
lean_inc_ref(v_toCold_2944_);
v___x_2952_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2952_, 0, v_toCold_2944_);
lean_ctor_set(v___x_2952_, 1, v_currRecDepth_2945_);
lean_ctor_set(v___x_2952_, 2, v_ref_2951_);
lean_ctor_set_uint16(v___x_2952_, sizeof(void*)*3, v_optionFlags_2947_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*3 + 2, v_suppressElabErrors_2948_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*3 + 3, v_checkDeprecated_2949_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*3 + 4, v_isRecordingDeps_2950_);
lean_inc(v___y_2930_);
lean_inc(v___y_2928_);
lean_inc_ref(v___y_2927_);
lean_inc(v___y_2926_);
lean_inc_ref(v___y_2925_);
v___x_2953_ = lean_apply_9(v_onErr_2922_, v_init_2923_, v_cfg_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___x_2952_, v___y_2930_, lean_box(0));
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object* v_eval_3019_, uint8_t v_logExceptions_3020_, lean_object* v_onErr_3021_, lean_object* v_as_3022_, size_t v_i_3023_, size_t v_stop_3024_, lean_object* v_b_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_usize_dec_eq(v_i_3023_, v_stop_3024_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_array_uget_borrowed(v_as_3022_, v_i_3023_);
lean_inc(v___x_3034_);
lean_inc_ref(v_onErr_3021_);
lean_inc_ref(v_eval_3019_);
v___x_3035_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3019_, v_logExceptions_3020_, v_onErr_3021_, v_b_3025_, v___x_3034_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; size_t v___x_3037_; size_t v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = ((size_t)1ULL);
v___x_3038_ = lean_usize_add(v_i_3023_, v___x_3037_);
v_i_3023_ = v___x_3038_;
v_b_3025_ = v_a_3036_;
goto _start;
}
else
{
lean_dec_ref(v_onErr_3021_);
lean_dec_ref(v_eval_3019_);
return v___x_3035_;
}
}
else
{
lean_object* v___x_3040_; 
lean_dec_ref(v_onErr_3021_);
lean_dec_ref(v_eval_3019_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_b_3025_);
return v___x_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object* v_eval_3041_, uint8_t v_logExceptions_3042_, lean_object* v_onErr_3043_, lean_object* v_init_3044_, lean_object* v_cfgs_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3053_ = lean_unsigned_to_nat(0u);
v___x_3054_ = lean_array_get_size(v_cfgs_3045_);
v___x_3055_ = lean_nat_dec_lt(v___x_3053_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec_ref(v_onErr_3043_);
lean_dec_ref(v_eval_3041_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_init_3044_);
return v___x_3056_;
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___x_3054_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3041_, v_logExceptions_3042_, v_onErr_3043_, v_cfgs_3045_, v___x_3057_, v___x_3058_, v_init_3044_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
return v___x_3059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object* v_eval_3060_, lean_object* v_logExceptions_3061_, lean_object* v_onErr_3062_, lean_object* v_init_3063_, lean_object* v_cfgs_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
uint8_t v_logExceptions_boxed_3072_; lean_object* v_res_3073_; 
v_logExceptions_boxed_3072_ = lean_unbox(v_logExceptions_3061_);
v_res_3073_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3060_, v_logExceptions_boxed_3072_, v_onErr_3062_, v_init_3063_, v_cfgs_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_cfgs_3064_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_eval_3074_, lean_object* v_logExceptions_3075_, lean_object* v_onErr_3076_, lean_object* v_as_3077_, lean_object* v_i_3078_, lean_object* v_stop_3079_, lean_object* v_b_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
uint8_t v_logExceptions_boxed_3088_; size_t v_i_boxed_3089_; size_t v_stop_boxed_3090_; lean_object* v_res_3091_; 
v_logExceptions_boxed_3088_ = lean_unbox(v_logExceptions_3075_);
v_i_boxed_3089_ = lean_unbox_usize(v_i_3078_);
lean_dec(v_i_3078_);
v_stop_boxed_3090_ = lean_unbox_usize(v_stop_3079_);
lean_dec(v_stop_3079_);
v_res_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3074_, v_logExceptions_boxed_3088_, v_onErr_3076_, v_as_3077_, v_i_boxed_3089_, v_stop_boxed_3090_, v_b_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v_as_3077_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object* v_eval_3092_, lean_object* v_logExceptions_3093_, lean_object* v_onErr_3094_, lean_object* v_init_3095_, lean_object* v_cfg_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
uint8_t v_logExceptions_boxed_3104_; lean_object* v_res_3105_; 
v_logExceptions_boxed_3104_ = lean_unbox(v_logExceptions_3093_);
v_res_3105_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3092_, v_logExceptions_boxed_3104_, v_onErr_3094_, v_init_3095_, v_cfg_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object* v_eval_3106_, lean_object* v_init_3107_, lean_object* v_cfg_3108_, lean_object* v_onErr_3109_, uint8_t v_logExceptions_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3106_, v_logExceptions_3110_, v_onErr_3109_, v_init_3107_, v_cfg_3108_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object* v_eval_3119_, lean_object* v_init_3120_, lean_object* v_cfg_3121_, lean_object* v_onErr_3122_, lean_object* v_logExceptions_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
uint8_t v_logExceptions_boxed_3131_; lean_object* v_res_3132_; 
v_logExceptions_boxed_3131_ = lean_unbox(v_logExceptions_3123_);
v_res_3132_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3119_, v_init_3120_, v_cfg_3121_, v_onErr_3122_, v_logExceptions_boxed_3131_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object* v_00_u03b1_3133_, lean_object* v_eval_3134_, lean_object* v_init_3135_, lean_object* v_cfg_3136_, lean_object* v_onErr_3137_, uint8_t v_logExceptions_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3134_, v_logExceptions_3138_, v_onErr_3137_, v_init_3135_, v_cfg_3136_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object* v_00_u03b1_3147_, lean_object* v_eval_3148_, lean_object* v_init_3149_, lean_object* v_cfg_3150_, lean_object* v_onErr_3151_, lean_object* v_logExceptions_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
uint8_t v_logExceptions_boxed_3160_; lean_object* v_res_3161_; 
v_logExceptions_boxed_3160_ = lean_unbox(v_logExceptions_3152_);
v_res_3161_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(v_00_u03b1_3147_, v_eval_3148_, v_init_3149_, v_cfg_3150_, v_onErr_3151_, v_logExceptions_boxed_3160_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object* v_00_u03b1_3162_, lean_object* v_eval_3163_, uint8_t v_logExceptions_3164_, lean_object* v_onErr_3165_, lean_object* v_init_3166_, lean_object* v_cfg_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3163_, v_logExceptions_3164_, v_onErr_3165_, v_init_3166_, v_cfg_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(lean_object* v_00_u03b1_3176_, lean_object* v_eval_3177_, lean_object* v_logExceptions_3178_, lean_object* v_onErr_3179_, lean_object* v_init_3180_, lean_object* v_cfg_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v_logExceptions_boxed_3189_; lean_object* v_res_3190_; 
v_logExceptions_boxed_3189_ = lean_unbox(v_logExceptions_3178_);
v_res_3190_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_3176_, v_eval_3177_, v_logExceptions_boxed_3189_, v_onErr_3179_, v_init_3180_, v_cfg_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object* v_00_u03b1_3191_, lean_object* v_eval_3192_, uint8_t v_logExceptions_3193_, lean_object* v_onErr_3194_, lean_object* v_init_3195_, lean_object* v_cfgs_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3192_, v_logExceptions_3193_, v_onErr_3194_, v_init_3195_, v_cfgs_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3205_, lean_object* v_eval_3206_, lean_object* v_logExceptions_3207_, lean_object* v_onErr_3208_, lean_object* v_init_3209_, lean_object* v_cfgs_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
uint8_t v_logExceptions_boxed_3218_; lean_object* v_res_3219_; 
v_logExceptions_boxed_3218_ = lean_unbox(v_logExceptions_3207_);
v_res_3219_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_3205_, v_eval_3206_, v_logExceptions_boxed_3218_, v_onErr_3208_, v_init_3209_, v_cfgs_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec_ref(v_cfgs_3210_);
return v_res_3219_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object* v_s_3220_, lean_object* v_inst_3221_, lean_object* v_R_3222_, lean_object* v_a_3223_, uint8_t v_b_3224_, lean_object* v_c_3225_){
_start:
{
uint8_t v___x_3226_; 
v___x_3226_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_3220_, v_a_3223_, v_b_3224_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_s_3227_, lean_object* v_inst_3228_, lean_object* v_R_3229_, lean_object* v_a_3230_, lean_object* v_b_3231_, lean_object* v_c_3232_){
_start:
{
uint8_t v_b_boxed_3233_; uint8_t v_res_3234_; lean_object* v_r_3235_; 
v_b_boxed_3233_ = lean_unbox(v_b_3231_);
v_res_3234_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3227_, v_inst_3228_, v_R_3229_, v_a_3230_, v_b_boxed_3233_, v_c_3232_);
lean_dec_ref(v_s_3227_);
v_r_3235_ = lean_box(v_res_3234_);
return v_r_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3236_, lean_object* v_eval_3237_, uint8_t v_logExceptions_3238_, lean_object* v_onErr_3239_, lean_object* v_as_3240_, size_t v_i_3241_, size_t v_stop_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3237_, v_logExceptions_3238_, v_onErr_3239_, v_as_3240_, v_i_3241_, v_stop_3242_, v_b_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3252_, lean_object* v_eval_3253_, lean_object* v_logExceptions_3254_, lean_object* v_onErr_3255_, lean_object* v_as_3256_, lean_object* v_i_3257_, lean_object* v_stop_3258_, lean_object* v_b_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
uint8_t v_logExceptions_boxed_3267_; size_t v_i_boxed_3268_; size_t v_stop_boxed_3269_; lean_object* v_res_3270_; 
v_logExceptions_boxed_3267_ = lean_unbox(v_logExceptions_3254_);
v_i_boxed_3268_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_stop_boxed_3269_ = lean_unbox_usize(v_stop_3258_);
lean_dec(v_stop_3258_);
v_res_3270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_3252_, v_eval_3253_, v_logExceptions_boxed_3267_, v_onErr_3255_, v_as_3256_, v_i_boxed_3268_, v_stop_boxed_3269_, v_b_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v_as_3256_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object* v_eval_3271_, lean_object* v_init_3272_, lean_object* v_cfgs_3273_, lean_object* v_onErr_3274_, uint8_t v_logExceptions_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3271_, v_logExceptions_3275_, v_onErr_3274_, v_init_3272_, v_cfgs_3273_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object* v_eval_3284_, lean_object* v_init_3285_, lean_object* v_cfgs_3286_, lean_object* v_onErr_3287_, lean_object* v_logExceptions_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
uint8_t v_logExceptions_boxed_3296_; lean_object* v_res_3297_; 
v_logExceptions_boxed_3296_ = lean_unbox(v_logExceptions_3288_);
v_res_3297_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3284_, v_init_3285_, v_cfgs_3286_, v_onErr_3287_, v_logExceptions_boxed_3296_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec_ref(v_cfgs_3286_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object* v_00_u03b1_3298_, lean_object* v_eval_3299_, lean_object* v_init_3300_, lean_object* v_cfgs_3301_, lean_object* v_onErr_3302_, uint8_t v_logExceptions_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3299_, v_logExceptions_3303_, v_onErr_3302_, v_init_3300_, v_cfgs_3301_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object* v_00_u03b1_3312_, lean_object* v_eval_3313_, lean_object* v_init_3314_, lean_object* v_cfgs_3315_, lean_object* v_onErr_3316_, lean_object* v_logExceptions_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
uint8_t v_logExceptions_boxed_3325_; lean_object* v_res_3326_; 
v_logExceptions_boxed_3325_ = lean_unbox(v_logExceptions_3317_);
v_res_3326_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(v_00_u03b1_3312_, v_eval_3313_, v_init_3314_, v_cfgs_3315_, v_onErr_3316_, v_logExceptions_boxed_3325_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec_ref(v_cfgs_3315_);
return v_res_3326_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object* v_x_3327_){
_start:
{
uint8_t v___x_3328_; 
v___x_3328_ = 0;
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object* v_x_3329_){
_start:
{
uint8_t v_res_3330_; lean_object* v_r_3331_; 
v_res_3330_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3329_);
lean_dec(v_x_3329_);
v_r_3331_ = lean_box(v_res_3330_);
return v_r_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__8(lean_object* v___x_3332_, lean_object* v_ctx_x3f_3333_, size_t v_sz_3334_, size_t v_i_3335_, lean_object* v_bs_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
uint8_t v___x_3344_; 
v___x_3344_ = lean_usize_dec_lt(v_i_3335_, v_sz_3334_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref(v_ctx_x3f_3333_);
v___x_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3345_, 0, v_bs_3336_);
return v___x_3345_;
}
else
{
lean_object* v_assignment_3346_; lean_object* v_v_3347_; lean_object* v___x_3348_; lean_object* v_bs_x27_3349_; lean_object* v_a_3351_; lean_object* v_tree_3356_; lean_object* v___x_3357_; 
v_assignment_3346_ = lean_ctor_get(v___x_3332_, 0);
v_v_3347_ = lean_array_uget(v_bs_3336_, v_i_3335_);
v___x_3348_ = lean_unsigned_to_nat(0u);
v_bs_x27_3349_ = lean_array_uset(v_bs_3336_, v_i_3335_, v___x_3348_);
v_tree_3356_ = l_Lean_Elab_InfoTree_substitute(v_v_3347_, v_assignment_3346_);
lean_inc_ref(v_ctx_x3f_3333_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc(v___y_3340_);
lean_inc_ref(v___y_3339_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
v___x_3357_ = lean_apply_7(v_ctx_x3f_3333_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, lean_box(0));
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
if (lean_obj_tag(v_a_3358_) == 0)
{
v_a_3351_ = v_tree_3356_;
goto v___jp_3350_;
}
else
{
lean_object* v_val_3359_; lean_object* v___x_3360_; 
v_val_3359_ = lean_ctor_get(v_a_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v_a_3358_, 1);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v_val_3359_);
lean_ctor_set(v___x_3360_, 1, v_tree_3356_);
v_a_3351_ = v___x_3360_;
goto v___jp_3350_;
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref(v_tree_3356_);
lean_dec_ref(v_bs_x27_3349_);
lean_dec_ref(v_ctx_x3f_3333_);
v_a_3361_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3357_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3357_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
v___jp_3350_:
{
size_t v___x_3352_; size_t v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = ((size_t)1ULL);
v___x_3353_ = lean_usize_add(v_i_3335_, v___x_3352_);
v___x_3354_ = lean_array_uset(v_bs_x27_3349_, v_i_3335_, v_a_3351_);
v_i_3335_ = v___x_3353_;
v_bs_3336_ = v___x_3354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__8___boxed(lean_object* v___x_3369_, lean_object* v_ctx_x3f_3370_, lean_object* v_sz_3371_, lean_object* v_i_3372_, lean_object* v_bs_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
size_t v_sz_boxed_3381_; size_t v_i_boxed_3382_; lean_object* v_res_3383_; 
v_sz_boxed_3381_ = lean_unbox_usize(v_sz_3371_);
lean_dec(v_sz_3371_);
v_i_boxed_3382_ = lean_unbox_usize(v_i_3372_);
lean_dec(v_i_3372_);
v_res_3383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__8(v___x_3369_, v_ctx_x3f_3370_, v_sz_boxed_3381_, v_i_boxed_3382_, v_bs_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec_ref(v___x_3369_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7(lean_object* v___x_3384_, lean_object* v_ctx_x3f_3385_, lean_object* v_x_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
if (lean_obj_tag(v_x_3386_) == 0)
{
lean_object* v_cs_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3420_; 
v_cs_3394_ = lean_ctor_get(v_x_3386_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_x_3386_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3396_ = v_x_3386_;
v_isShared_3397_ = v_isSharedCheck_3420_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_cs_3394_);
lean_dec(v_x_3386_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3420_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
size_t v_sz_3398_; size_t v___x_3399_; lean_object* v___x_3400_; 
v_sz_3398_ = lean_array_size(v_cs_3394_);
v___x_3399_ = ((size_t)0ULL);
v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7_spec__8(v___x_3384_, v_ctx_x3f_3385_, v_sz_3398_, v___x_3399_, v_cs_3394_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3411_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3411_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3411_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v_a_3401_);
v___x_3406_ = v___x_3396_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3408_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3406_);
v___x_3408_ = v___x_3403_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_del_object(v___x_3396_);
v_a_3412_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3400_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3400_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
else
{
lean_object* v_vs_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3447_; 
v_vs_3421_ = lean_ctor_get(v_x_3386_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_x_3386_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3423_ = v_x_3386_;
v_isShared_3424_ = v_isSharedCheck_3447_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_vs_3421_);
lean_dec(v_x_3386_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3447_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
size_t v_sz_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v_sz_3425_ = lean_array_size(v_vs_3421_);
v___x_3426_ = ((size_t)0ULL);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__8(v___x_3384_, v_ctx_x3f_3385_, v_sz_3425_, v___x_3426_, v_vs_3421_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3438_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3438_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3438_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v_a_3428_);
v___x_3433_ = v___x_3423_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3435_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3433_);
v___x_3435_ = v___x_3430_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_del_object(v___x_3423_);
v_a_3439_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3427_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3427_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v___x_3448_, lean_object* v_ctx_x3f_3449_, size_t v_sz_3450_, size_t v_i_3451_, lean_object* v_bs_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_lt(v_i_3451_, v_sz_3450_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; 
lean_dec_ref(v_ctx_x3f_3449_);
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v_bs_3452_);
return v___x_3461_;
}
else
{
lean_object* v_v_3462_; lean_object* v___x_3463_; lean_object* v_bs_x27_3464_; lean_object* v___x_3465_; 
v_v_3462_ = lean_array_uget(v_bs_3452_, v_i_3451_);
v___x_3463_ = lean_unsigned_to_nat(0u);
v_bs_x27_3464_ = lean_array_uset(v_bs_3452_, v_i_3451_, v___x_3463_);
lean_inc_ref(v_ctx_x3f_3449_);
v___x_3465_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7(v___x_3448_, v_ctx_x3f_3449_, v_v_3462_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; size_t v___x_3467_; size_t v___x_3468_; lean_object* v___x_3469_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = ((size_t)1ULL);
v___x_3468_ = lean_usize_add(v_i_3451_, v___x_3467_);
v___x_3469_ = lean_array_uset(v_bs_x27_3464_, v_i_3451_, v_a_3466_);
v_i_3451_ = v___x_3468_;
v_bs_3452_ = v___x_3469_;
goto _start;
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v_bs_x27_3464_);
lean_dec_ref(v_ctx_x3f_3449_);
v_a_3471_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3465_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3465_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7_spec__8___boxed(lean_object* v___x_3479_, lean_object* v_ctx_x3f_3480_, lean_object* v_sz_3481_, lean_object* v_i_3482_, lean_object* v_bs_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
size_t v_sz_boxed_3491_; size_t v_i_boxed_3492_; lean_object* v_res_3493_; 
v_sz_boxed_3491_ = lean_unbox_usize(v_sz_3481_);
lean_dec(v_sz_3481_);
v_i_boxed_3492_ = lean_unbox_usize(v_i_3482_);
lean_dec(v_i_3482_);
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7_spec__8(v___x_3479_, v_ctx_x3f_3480_, v_sz_boxed_3491_, v_i_boxed_3492_, v_bs_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v___x_3479_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v___x_3494_, lean_object* v_ctx_x3f_3495_, lean_object* v_x_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7(v___x_3494_, v_ctx_x3f_3495_, v_x_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v___x_3494_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object* v___x_3505_, lean_object* v_ctx_x3f_3506_, lean_object* v_t_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_root_3515_; lean_object* v_tail_3516_; lean_object* v_size_3517_; size_t v_shift_3518_; lean_object* v_tailOff_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3555_; 
v_root_3515_ = lean_ctor_get(v_t_3507_, 0);
v_tail_3516_ = lean_ctor_get(v_t_3507_, 1);
v_size_3517_ = lean_ctor_get(v_t_3507_, 2);
v_shift_3518_ = lean_ctor_get_usize(v_t_3507_, 4);
v_tailOff_3519_ = lean_ctor_get(v_t_3507_, 3);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_t_3507_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3521_ = v_t_3507_;
v_isShared_3522_ = v_isSharedCheck_3555_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_tailOff_3519_);
lean_inc(v_size_3517_);
lean_inc(v_tail_3516_);
lean_inc(v_root_3515_);
lean_dec(v_t_3507_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3555_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; 
lean_inc_ref(v_ctx_x3f_3506_);
v___x_3523_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__7(v___x_3505_, v_ctx_x3f_3506_, v_root_3515_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; size_t v_sz_3525_; size_t v___x_3526_; lean_object* v___x_3527_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v_sz_3525_ = lean_array_size(v_tail_3516_);
v___x_3526_ = ((size_t)0ULL);
v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__8(v___x_3505_, v_ctx_x3f_3506_, v_sz_3525_, v___x_3526_, v_tail_3516_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3538_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v_a_3528_);
lean_ctor_set(v___x_3521_, 0, v_a_3524_);
v___x_3533_ = v___x_3521_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3524_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_a_3528_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_size_3517_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_tailOff_3519_);
lean_ctor_set_usize(v_reuseFailAlloc_3537_, 4, v_shift_3518_);
v___x_3533_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3535_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3533_);
v___x_3535_ = v___x_3530_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3524_);
lean_del_object(v___x_3521_);
lean_dec(v_tailOff_3519_);
lean_dec(v_size_3517_);
v_a_3539_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3527_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3527_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_del_object(v___x_3521_);
lean_dec(v_tailOff_3519_);
lean_dec(v_size_3517_);
lean_dec_ref(v_tail_3516_);
lean_dec_ref(v_ctx_x3f_3506_);
v_a_3547_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3523_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3523_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object* v___x_3556_, lean_object* v_ctx_x3f_3557_, lean_object* v_t_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3556_, v_ctx_x3f_3557_, v_t_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v___x_3556_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3567_, lean_object* v_ctx_x3f_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v_a_3574_, lean_object* v_a_x3f_3575_){
_start:
{
lean_object* v___x_3577_; lean_object* v_infoState_3578_; lean_object* v_trees_3579_; lean_object* v___x_3580_; 
v___x_3577_ = lean_st_ref_get(v___y_3567_);
v_infoState_3578_ = lean_ctor_get(v___x_3577_, 8);
lean_inc_ref(v_infoState_3578_);
lean_dec(v___x_3577_);
v_trees_3579_ = lean_ctor_get(v_infoState_3578_, 2);
lean_inc_ref(v_trees_3579_);
v___x_3580_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_3578_, v_ctx_x3f_3568_, v_trees_3579_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3567_);
lean_dec_ref(v_infoState_3578_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3620_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3620_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3620_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v_infoState_3586_; lean_object* v_env_3587_; lean_object* v_nextMacroScope_3588_; lean_object* v_ngen_3589_; lean_object* v_auxDeclNGen_3590_; lean_object* v_traceState_3591_; lean_object* v_cache_3592_; lean_object* v_recordedDeps_3593_; lean_object* v_messages_3594_; lean_object* v_snapshotTasks_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3619_; 
v___x_3585_ = lean_st_ref_take(v___y_3567_);
v_infoState_3586_ = lean_ctor_get(v___x_3585_, 8);
v_env_3587_ = lean_ctor_get(v___x_3585_, 0);
v_nextMacroScope_3588_ = lean_ctor_get(v___x_3585_, 1);
v_ngen_3589_ = lean_ctor_get(v___x_3585_, 2);
v_auxDeclNGen_3590_ = lean_ctor_get(v___x_3585_, 3);
v_traceState_3591_ = lean_ctor_get(v___x_3585_, 4);
v_cache_3592_ = lean_ctor_get(v___x_3585_, 5);
v_recordedDeps_3593_ = lean_ctor_get(v___x_3585_, 6);
v_messages_3594_ = lean_ctor_get(v___x_3585_, 7);
v_snapshotTasks_3595_ = lean_ctor_get(v___x_3585_, 9);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3597_ = v___x_3585_;
v_isShared_3598_ = v_isSharedCheck_3619_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_snapshotTasks_3595_);
lean_inc(v_infoState_3586_);
lean_inc(v_messages_3594_);
lean_inc(v_recordedDeps_3593_);
lean_inc(v_cache_3592_);
lean_inc(v_traceState_3591_);
lean_inc(v_auxDeclNGen_3590_);
lean_inc(v_ngen_3589_);
lean_inc(v_nextMacroScope_3588_);
lean_inc(v_env_3587_);
lean_dec(v___x_3585_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3619_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
uint8_t v_enabled_3599_; lean_object* v_assignment_3600_; lean_object* v_lazyAssignment_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3617_; 
v_enabled_3599_ = lean_ctor_get_uint8(v_infoState_3586_, sizeof(void*)*3);
v_assignment_3600_ = lean_ctor_get(v_infoState_3586_, 0);
v_lazyAssignment_3601_ = lean_ctor_get(v_infoState_3586_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_infoState_3586_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v_infoState_3586_, 2);
lean_dec(v_unused_3618_);
v___x_3603_ = v_infoState_3586_;
v_isShared_3604_ = v_isSharedCheck_3617_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_lazyAssignment_3601_);
lean_inc(v_assignment_3600_);
lean_dec(v_infoState_3586_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3617_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_box(0);
v___x_3606_ = l_Lean_PersistentArray_append___redArg(v_a_3574_, v_a_3581_);
lean_dec(v_a_3581_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 2, v___x_3606_);
v___x_3608_ = v___x_3603_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_assignment_3600_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_lazyAssignment_3601_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v___x_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, sizeof(void*)*3, v_enabled_3599_);
v___x_3608_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3610_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 8, v___x_3608_);
v___x_3610_ = v___x_3597_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_env_3587_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_nextMacroScope_3588_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v_ngen_3589_);
lean_ctor_set(v_reuseFailAlloc_3615_, 3, v_auxDeclNGen_3590_);
lean_ctor_set(v_reuseFailAlloc_3615_, 4, v_traceState_3591_);
lean_ctor_set(v_reuseFailAlloc_3615_, 5, v_cache_3592_);
lean_ctor_set(v_reuseFailAlloc_3615_, 6, v_recordedDeps_3593_);
lean_ctor_set(v_reuseFailAlloc_3615_, 7, v_messages_3594_);
lean_ctor_set(v_reuseFailAlloc_3615_, 8, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3615_, 9, v_snapshotTasks_3595_);
v___x_3610_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_st_ref_put(v___y_3567_, v___x_3610_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3605_);
v___x_3613_ = v___x_3583_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3605_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec_ref(v_a_3574_);
v_a_3621_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3580_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3580_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3629_, lean_object* v_ctx_x3f_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v_a_3636_, lean_object* v_a_x3f_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3629_, v_ctx_x3f_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v_a_3636_, v_a_x3f_3637_);
lean_dec(v_a_x3f_3637_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3629_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v_infoState_3643_; lean_object* v_trees_3644_; lean_object* v___x_3645_; lean_object* v_infoState_3646_; lean_object* v_env_3647_; lean_object* v_nextMacroScope_3648_; lean_object* v_ngen_3649_; lean_object* v_auxDeclNGen_3650_; lean_object* v_traceState_3651_; lean_object* v_cache_3652_; lean_object* v_recordedDeps_3653_; lean_object* v_messages_3654_; lean_object* v_snapshotTasks_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3678_; 
v___x_3642_ = lean_st_ref_get(v___y_3640_);
v_infoState_3643_ = lean_ctor_get(v___x_3642_, 8);
lean_inc_ref(v_infoState_3643_);
lean_dec(v___x_3642_);
v_trees_3644_ = lean_ctor_get(v_infoState_3643_, 2);
lean_inc_ref(v_trees_3644_);
lean_dec_ref(v_infoState_3643_);
v___x_3645_ = lean_st_ref_take(v___y_3640_);
v_infoState_3646_ = lean_ctor_get(v___x_3645_, 8);
v_env_3647_ = lean_ctor_get(v___x_3645_, 0);
v_nextMacroScope_3648_ = lean_ctor_get(v___x_3645_, 1);
v_ngen_3649_ = lean_ctor_get(v___x_3645_, 2);
v_auxDeclNGen_3650_ = lean_ctor_get(v___x_3645_, 3);
v_traceState_3651_ = lean_ctor_get(v___x_3645_, 4);
v_cache_3652_ = lean_ctor_get(v___x_3645_, 5);
v_recordedDeps_3653_ = lean_ctor_get(v___x_3645_, 6);
v_messages_3654_ = lean_ctor_get(v___x_3645_, 7);
v_snapshotTasks_3655_ = lean_ctor_get(v___x_3645_, 9);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3657_ = v___x_3645_;
v_isShared_3658_ = v_isSharedCheck_3678_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_snapshotTasks_3655_);
lean_inc(v_infoState_3646_);
lean_inc(v_messages_3654_);
lean_inc(v_recordedDeps_3653_);
lean_inc(v_cache_3652_);
lean_inc(v_traceState_3651_);
lean_inc(v_auxDeclNGen_3650_);
lean_inc(v_ngen_3649_);
lean_inc(v_nextMacroScope_3648_);
lean_inc(v_env_3647_);
lean_dec(v___x_3645_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3678_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
uint8_t v_enabled_3659_; lean_object* v_assignment_3660_; lean_object* v_lazyAssignment_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3676_; 
v_enabled_3659_ = lean_ctor_get_uint8(v_infoState_3646_, sizeof(void*)*3);
v_assignment_3660_ = lean_ctor_get(v_infoState_3646_, 0);
v_lazyAssignment_3661_ = lean_ctor_get(v_infoState_3646_, 1);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_infoState_3646_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v_infoState_3646_, 2);
lean_dec(v_unused_3677_);
v___x_3663_ = v_infoState_3646_;
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_lazyAssignment_3661_);
lean_inc(v_assignment_3660_);
lean_dec(v_infoState_3646_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3676_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3665_ = lean_unsigned_to_nat(32u);
v___x_3666_ = lean_mk_empty_array_with_capacity(v___x_3665_);
lean_dec_ref(v___x_3666_);
v___x_3667_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 2, v___x_3667_);
v___x_3669_ = v___x_3663_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_assignment_3660_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_lazyAssignment_3661_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v___x_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3, v_enabled_3659_);
v___x_3669_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 8, v___x_3669_);
v___x_3671_ = v___x_3657_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_env_3647_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_nextMacroScope_3648_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_ngen_3649_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_auxDeclNGen_3650_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_traceState_3651_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_cache_3652_);
lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_recordedDeps_3653_);
lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_messages_3654_);
lean_ctor_set(v_reuseFailAlloc_3674_, 8, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_snapshotTasks_3655_);
v___x_3671_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = lean_st_ref_put(v___y_3640_, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_trees_3644_);
return v___x_3673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3679_);
lean_dec(v___y_3679_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object* v_x_3682_, lean_object* v_ctx_x3f_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3691_; lean_object* v_infoState_3692_; uint8_t v_enabled_3693_; 
v___x_3691_ = lean_st_ref_get(v___y_3689_);
v_infoState_3692_ = lean_ctor_get(v___x_3691_, 8);
lean_inc_ref(v_infoState_3692_);
lean_dec(v___x_3691_);
v_enabled_3693_ = lean_ctor_get_uint8(v_infoState_3692_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3692_);
if (v_enabled_3693_ == 0)
{
lean_object* v___x_3694_; 
lean_dec_ref(v_ctx_x3f_3683_);
lean_inc(v___y_3689_);
lean_inc_ref(v___y_3688_);
lean_inc(v___y_3687_);
lean_inc_ref(v___y_3686_);
lean_inc(v___y_3685_);
lean_inc_ref(v___y_3684_);
v___x_3694_ = lean_apply_7(v_x_3682_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, lean_box(0));
return v___x_3694_;
}
else
{
lean_object* v___x_3695_; lean_object* v_a_3696_; lean_object* v_r_3697_; 
v___x_3695_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3689_);
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref(v___x_3695_);
lean_inc(v___y_3689_);
lean_inc_ref(v___y_3688_);
lean_inc(v___y_3687_);
lean_inc_ref(v___y_3686_);
lean_inc(v___y_3685_);
lean_inc_ref(v___y_3684_);
v_r_3697_ = lean_apply_7(v_x_3682_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, lean_box(0));
if (lean_obj_tag(v_r_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3722_; 
v_a_3698_ = lean_ctor_get(v_r_3697_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_r_3697_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3700_ = v_r_3697_;
v_isShared_3701_ = v_isSharedCheck_3722_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v_r_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3722_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
lean_inc(v_a_3698_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set_tag(v___x_3700_, 1);
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3704_; 
v___x_3704_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3689_, v_ctx_x3f_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v_a_3696_, v___x_3703_);
lean_dec_ref(v___x_3703_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v___x_3704_, 0);
lean_dec(v_unused_3712_);
v___x_3706_ = v___x_3704_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_dec(v___x_3704_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v_a_3698_);
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3698_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v_a_3698_);
v_a_3713_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3704_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3704_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_a_3723_ = lean_ctor_get(v_r_3697_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v_r_3697_, 1);
v___x_3724_ = lean_box(0);
v___x_3725_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3689_, v_ctx_x3f_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v_a_3696_, v___x_3724_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; 
v_unused_3733_ = lean_ctor_get(v___x_3725_, 0);
lean_dec(v_unused_3733_);
v___x_3727_ = v___x_3725_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v___x_3725_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
lean_ctor_set_tag(v___x_3727_, 1);
lean_ctor_set(v___x_3727_, 0, v_a_3723_);
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3723_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v_a_3723_);
v_a_3734_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3725_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3725_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_3742_, lean_object* v_ctx_x3f_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3742_, v_ctx_x3f_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; lean_object* v_env_3757_; lean_object* v___x_3758_; lean_object* v_toCold_3759_; lean_object* v_mctx_3760_; lean_object* v_currNamespace_3761_; lean_object* v_openDecls_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v_ngen_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3756_ = lean_st_ref_get(v___y_3754_);
v_env_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc_ref(v_env_3757_);
lean_dec(v___x_3756_);
v___x_3758_ = lean_st_ref_get(v___y_3752_);
v_toCold_3759_ = lean_ctor_get(v___y_3753_, 0);
v_mctx_3760_ = lean_ctor_get(v___x_3758_, 0);
lean_inc_ref(v_mctx_3760_);
lean_dec(v___x_3758_);
v_currNamespace_3761_ = lean_ctor_get(v_toCold_3759_, 4);
v_openDecls_3762_ = lean_ctor_get(v_toCold_3759_, 5);
v___x_3763_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3753_);
v___x_3764_ = lean_st_ref_get(v___y_3754_);
v_ngen_3765_ = lean_ctor_get(v___x_3764_, 2);
lean_inc_ref(v_ngen_3765_);
lean_dec(v___x_3764_);
v___x_3766_ = lean_box(0);
v___x_3767_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_3762_);
lean_inc(v_currNamespace_3761_);
v___x_3768_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3768_, 0, v_env_3757_);
lean_ctor_set(v___x_3768_, 1, v___x_3766_);
lean_ctor_set(v___x_3768_, 2, v___x_3767_);
lean_ctor_set(v___x_3768_, 3, v_mctx_3760_);
lean_ctor_set(v___x_3768_, 4, v___x_3763_);
lean_ctor_set(v___x_3768_, 5, v_currNamespace_3761_);
lean_ctor_set(v___x_3768_, 6, v_openDecls_3762_);
lean_ctor_set(v___x_3768_, 7, v_ngen_3765_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; lean_object* v_toCold_3783_; lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3808_; 
v___x_3782_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3778_, v___y_3779_, v___y_3780_);
v_toCold_3783_ = lean_ctor_get(v___y_3779_, 0);
v_a_3784_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3786_ = v___x_3782_;
v_isShared_3787_ = v_isSharedCheck_3808_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3782_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3808_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v_fileMap_3788_; lean_object* v_env_3789_; lean_object* v_mctx_3790_; lean_object* v_options_3791_; lean_object* v_currNamespace_3792_; lean_object* v_openDecls_3793_; lean_object* v_ngen_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3805_; 
v_fileMap_3788_ = lean_ctor_get(v_toCold_3783_, 1);
v_env_3789_ = lean_ctor_get(v_a_3784_, 0);
v_mctx_3790_ = lean_ctor_get(v_a_3784_, 3);
v_options_3791_ = lean_ctor_get(v_a_3784_, 4);
v_currNamespace_3792_ = lean_ctor_get(v_a_3784_, 5);
v_openDecls_3793_ = lean_ctor_get(v_a_3784_, 6);
v_ngen_3794_ = lean_ctor_get(v_a_3784_, 7);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_a_3784_);
if (v_isSharedCheck_3805_ == 0)
{
lean_object* v_unused_3806_; lean_object* v_unused_3807_; 
v_unused_3806_ = lean_ctor_get(v_a_3784_, 2);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_a_3784_, 1);
lean_dec(v_unused_3807_);
v___x_3796_ = v_a_3784_;
v_isShared_3797_ = v_isSharedCheck_3805_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_ngen_3794_);
lean_inc(v_openDecls_3793_);
lean_inc(v_currNamespace_3792_);
lean_inc(v_options_3791_);
lean_inc(v_mctx_3790_);
lean_inc(v_env_3789_);
lean_dec(v_a_3784_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3805_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = lean_box(0);
lean_inc_ref(v_fileMap_3788_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 2, v_fileMap_3788_);
lean_ctor_set(v___x_3796_, 1, v___x_3798_);
v___x_3800_ = v___x_3796_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_env_3789_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3804_, 2, v_fileMap_3788_);
lean_ctor_set(v_reuseFailAlloc_3804_, 3, v_mctx_3790_);
lean_ctor_set(v_reuseFailAlloc_3804_, 4, v_options_3791_);
lean_ctor_set(v_reuseFailAlloc_3804_, 5, v_currNamespace_3792_);
lean_ctor_set(v_reuseFailAlloc_3804_, 6, v_openDecls_3793_);
lean_ctor_set(v_reuseFailAlloc_3804_, 7, v_ngen_3794_);
v___x_3800_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3802_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3800_);
v___x_3802_ = v___x_3786_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___x_3824_; lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3834_; 
v___x_3824_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3834_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3834_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_a_3825_);
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3830_);
v___x_3832_ = v___x_3827_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object* v_x_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v___f_3852_; lean_object* v___x_3853_; 
v___f_3852_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0));
v___x_3853_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3844_, v___f_3852_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object* v_x_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object* v_00_u03b1_3863_, lean_object* v_x_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object* v_00_u03b1_3873_, lean_object* v_x_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(v_00_u03b1_3873_, v_x_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
return v_res_3882_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg(){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___closed__0);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg___boxed(lean_object* v___dummy_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg();
return v_res_3888_;
}
}
static uint64_t _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_3909_; uint64_t v___x_3910_; 
v___x_3909_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3909_);
return v___x_3910_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6(void){
_start:
{
uint64_t v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = lean_uint64_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5);
v___x_3912_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3913_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set_uint64(v___x_3913_, sizeof(void*)*1, v___x_3911_);
return v___x_3913_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7(void){
_start:
{
uint8_t v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3914_ = 1;
v___x_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = lean_box(0);
v___x_3917_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1));
v___x_3918_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_3919_ = lean_box(1);
v___x_3920_ = 0;
v___x_3921_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6);
v___x_3922_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v___x_3919_);
lean_ctor_set(v___x_3922_, 2, v___x_3918_);
lean_ctor_set(v___x_3922_, 3, v___x_3917_);
lean_ctor_set(v___x_3922_, 4, v___x_3916_);
lean_ctor_set(v___x_3922_, 5, v___x_3915_);
lean_ctor_set(v___x_3922_, 6, v___x_3916_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*7, v___x_3920_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*7 + 1, v___x_3920_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*7 + 2, v___x_3920_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*7 + 3, v___x_3914_);
return v___x_3922_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3924_ = lean_unsigned_to_nat(0u);
v___x_3925_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
lean_ctor_set(v___x_3925_, 2, v___x_3924_);
lean_ctor_set(v___x_3925_, 3, v___x_3924_);
lean_ctor_set(v___x_3925_, 4, v___x_3923_);
lean_ctor_set(v___x_3925_, 5, v___x_3923_);
lean_ctor_set(v___x_3925_, 6, v___x_3923_);
lean_ctor_set(v___x_3925_, 7, v___x_3923_);
lean_ctor_set(v___x_3925_, 8, v___x_3923_);
lean_ctor_set(v___x_3925_, 9, v___x_3923_);
lean_ctor_set(v___x_3925_, 10, v___x_3923_);
return v___x_3925_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9(void){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3___redArg();
return v___x_3926_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
return v___x_3928_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_unsigned_to_nat(0u);
v___x_3930_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
lean_ctor_set(v___x_3931_, 2, v___x_3929_);
return v___x_3931_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__12(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3932_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11);
v___x_3933_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10);
v___x_3934_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3935_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
v___x_3936_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
lean_ctor_set(v___x_3936_, 1, v___x_3934_);
lean_ctor_set(v___x_3936_, 2, v___x_3933_);
lean_ctor_set(v___x_3936_, 3, v___x_3934_);
lean_ctor_set(v___x_3936_, 4, v___x_3934_);
lean_ctor_set(v___x_3936_, 5, v___x_3934_);
lean_ctor_set(v___x_3936_, 6, v___x_3934_);
lean_ctor_set(v___x_3936_, 7, v___x_3932_);
return v___x_3936_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__13(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
lean_ctor_set(v___x_3938_, 2, v___x_3937_);
lean_ctor_set(v___x_3938_, 3, v___x_3937_);
lean_ctor_set(v___x_3938_, 4, v___x_3937_);
return v___x_3938_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__14(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3939_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__13, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__13_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__13);
v___x_3940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_3941_ = lean_box(1);
v___x_3942_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__12);
v___x_3943_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8);
v___x_3944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
lean_ctor_set(v___x_3944_, 1, v___x_3942_);
lean_ctor_set(v___x_3944_, 2, v___x_3941_);
lean_ctor_set(v___x_3944_, 3, v___x_3940_);
lean_ctor_set(v___x_3944_, 4, v___x_3939_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object* v_mx_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3949_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed), 9, 2);
lean_closure_set(v___x_3949_, 0, lean_box(0));
lean_closure_set(v___x_3949_, 1, v_mx_3945_);
v___x_3950_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2));
v___x_3951_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3952_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7);
v___x_3953_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__14, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__14_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__14);
v___x_3954_ = lean_st_mk_ref(v___x_3953_);
v___x_3955_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3949_, v___x_3950_, v___x_3951_, v___x_3952_, v___x_3954_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3965_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v_fst_3960_; lean_object* v___x_3961_; lean_object* v___x_3963_; 
v_fst_3960_ = lean_ctor_get(v_a_3956_, 0);
lean_inc(v_fst_3960_);
lean_dec(v_a_3956_);
v___x_3961_ = lean_st_ref_get(v___x_3954_);
lean_dec(v___x_3954_);
lean_dec(v___x_3961_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v_fst_3960_);
v___x_3963_ = v___x_3958_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_fst_3960_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v___x_3954_);
v_a_3966_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3955_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3955_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object* v_mx_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3974_, v_a_3975_, v_a_3976_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object* v_00_u03b1_3979_, lean_object* v_mx_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3980_, v_a_3981_, v_a_3982_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object* v_00_u03b1_3985_, lean_object* v_mx_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_3985_, v_mx_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1_spec__3(lean_object* v_00_u03b2_3991_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1___redArg(){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1___redArg___boxed(lean_object* v___dummy_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1___redArg();
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_ConfigEval_runConfigElab_spec__1(lean_object* v_00_u03b2_3997_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_4020_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object* v_00_u03b1_4031_, lean_object* v_x_4032_, lean_object* v_ctx_x3f_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_4032_, v_ctx_x3f_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4042_, lean_object* v_x_4043_, lean_object* v_ctx_x3f_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_4042_, v_x_4043_, v_ctx_x3f_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object* v_eval_4053_, uint8_t v_logExceptions_4054_, lean_object* v_onErr_4055_, lean_object* v_init_4056_, lean_object* v_cfg_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_4053_, v_logExceptions_4054_, v_onErr_4055_, v_init_4056_, v_cfg_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object* v_eval_4066_, lean_object* v_logExceptions_4067_, lean_object* v_onErr_4068_, lean_object* v_init_4069_, lean_object* v_cfg_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
uint8_t v_logExceptions_boxed_4078_; lean_object* v_res_4079_; 
v_logExceptions_boxed_4078_ = lean_unbox(v_logExceptions_4067_);
v_res_4079_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4066_, v_logExceptions_boxed_4078_, v_onErr_4068_, v_init_4069_, v_cfg_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object* v_eval_4080_, lean_object* v_init_4081_, lean_object* v_cfg_4082_, lean_object* v_onErr_4083_, uint8_t v_logExceptions_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; uint8_t v___x_4089_; 
v___x_4088_ = lean_unsigned_to_nat(0u);
lean_inc(v_cfg_4082_);
v___x_4089_ = l_Lean_Syntax_matchesNull(v_cfg_4082_, v___x_4088_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4090_; lean_object* v___f_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v___x_4090_ = lean_box(v_logExceptions_4084_);
lean_inc(v_cfg_4082_);
lean_inc(v_init_4081_);
v___f_4091_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4091_, 0, v_eval_4080_);
lean_closure_set(v___f_4091_, 1, v___x_4090_);
lean_closure_set(v___f_4091_, 2, v_onErr_4083_);
lean_closure_set(v___f_4091_, 3, v_init_4081_);
lean_closure_set(v___f_4091_, 4, v_cfg_4082_);
v___x_4092_ = l_Lean_Syntax_getNumArgs(v_cfg_4082_);
v___x_4093_ = lean_unsigned_to_nat(1u);
v___x_4094_ = lean_nat_dec_eq(v___x_4092_, v___x_4093_);
lean_dec(v___x_4092_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; 
lean_dec(v_cfg_4082_);
lean_dec(v_init_4081_);
v___x_4095_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4091_, v_a_4085_, v_a_4086_);
return v___x_4095_;
}
else
{
lean_object* v___x_4096_; uint8_t v___x_4097_; 
v___x_4096_ = l_Lean_Syntax_getArg(v_cfg_4082_, v___x_4088_);
lean_dec(v_cfg_4082_);
v___x_4097_ = l_Lean_Syntax_matchesNull(v___x_4096_, v___x_4088_);
if (v___x_4097_ == 0)
{
lean_object* v___x_4098_; 
lean_dec(v_init_4081_);
v___x_4098_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4091_, v_a_4085_, v_a_4086_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; 
lean_dec_ref(v___f_4091_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_init_4081_);
return v___x_4099_;
}
}
}
else
{
lean_object* v___x_4100_; 
lean_dec_ref(v_onErr_4083_);
lean_dec(v_cfg_4082_);
lean_dec_ref(v_eval_4080_);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v_init_4081_);
return v___x_4100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object* v_eval_4101_, lean_object* v_init_4102_, lean_object* v_cfg_4103_, lean_object* v_onErr_4104_, lean_object* v_logExceptions_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
uint8_t v_logExceptions_boxed_4109_; lean_object* v_res_4110_; 
v_logExceptions_boxed_4109_ = lean_unbox(v_logExceptions_4105_);
v_res_4110_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4101_, v_init_4102_, v_cfg_4103_, v_onErr_4104_, v_logExceptions_boxed_4109_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object* v_00_u03b1_4111_, lean_object* v_eval_4112_, lean_object* v_init_4113_, lean_object* v_cfg_4114_, lean_object* v_onErr_4115_, uint8_t v_logExceptions_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4112_, v_init_4113_, v_cfg_4114_, v_onErr_4115_, v_logExceptions_4116_, v_a_4117_, v_a_4118_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object* v_00_u03b1_4121_, lean_object* v_eval_4122_, lean_object* v_init_4123_, lean_object* v_cfg_4124_, lean_object* v_onErr_4125_, lean_object* v_logExceptions_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
uint8_t v_logExceptions_boxed_4130_; lean_object* v_res_4131_; 
v_logExceptions_boxed_4130_ = lean_unbox(v_logExceptions_4126_);
v_res_4131_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(v_00_u03b1_4121_, v_eval_4122_, v_init_4123_, v_cfg_4124_, v_onErr_4125_, v_logExceptions_boxed_4130_, v_a_4127_, v_a_4128_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object* v_eval_4132_, uint8_t v_logExceptions_4133_, lean_object* v_onErr_4134_, lean_object* v_init_4135_, lean_object* v_cfgs_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_4132_, v_logExceptions_4133_, v_onErr_4134_, v_init_4135_, v_cfgs_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object* v_eval_4145_, lean_object* v_logExceptions_4146_, lean_object* v_onErr_4147_, lean_object* v_init_4148_, lean_object* v_cfgs_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
uint8_t v_logExceptions_boxed_4157_; lean_object* v_res_4158_; 
v_logExceptions_boxed_4157_ = lean_unbox(v_logExceptions_4146_);
v_res_4158_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4145_, v_logExceptions_boxed_4157_, v_onErr_4147_, v_init_4148_, v_cfgs_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v_cfgs_4149_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object* v_eval_4159_, lean_object* v_init_4160_, lean_object* v_cfgs_4161_, lean_object* v_onErr_4162_, uint8_t v_logExceptions_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v___x_4167_ = lean_array_get_size(v_cfgs_4161_);
v___x_4168_ = lean_unsigned_to_nat(0u);
v___x_4169_ = lean_nat_dec_eq(v___x_4167_, v___x_4168_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; lean_object* v___f_4171_; lean_object* v___x_4172_; 
v___x_4170_ = lean_box(v_logExceptions_4163_);
v___f_4171_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4171_, 0, v_eval_4159_);
lean_closure_set(v___f_4171_, 1, v___x_4170_);
lean_closure_set(v___f_4171_, 2, v_onErr_4162_);
lean_closure_set(v___f_4171_, 3, v_init_4160_);
lean_closure_set(v___f_4171_, 4, v_cfgs_4161_);
v___x_4172_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4171_, v_a_4164_, v_a_4165_);
return v___x_4172_;
}
else
{
lean_object* v___x_4173_; 
lean_dec_ref(v_onErr_4162_);
lean_dec_ref(v_cfgs_4161_);
lean_dec_ref(v_eval_4159_);
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_init_4160_);
return v___x_4173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object* v_eval_4174_, lean_object* v_init_4175_, lean_object* v_cfgs_4176_, lean_object* v_onErr_4177_, lean_object* v_logExceptions_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
uint8_t v_logExceptions_boxed_4182_; lean_object* v_res_4183_; 
v_logExceptions_boxed_4182_ = lean_unbox(v_logExceptions_4178_);
v_res_4183_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4174_, v_init_4175_, v_cfgs_4176_, v_onErr_4177_, v_logExceptions_boxed_4182_, v_a_4179_, v_a_4180_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object* v_00_u03b1_4184_, lean_object* v_eval_4185_, lean_object* v_init_4186_, lean_object* v_cfgs_4187_, lean_object* v_onErr_4188_, uint8_t v_logExceptions_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4185_, v_init_4186_, v_cfgs_4187_, v_onErr_4188_, v_logExceptions_4189_, v_a_4190_, v_a_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object* v_00_u03b1_4194_, lean_object* v_eval_4195_, lean_object* v_init_4196_, lean_object* v_cfgs_4197_, lean_object* v_onErr_4198_, lean_object* v_logExceptions_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
uint8_t v_logExceptions_boxed_4203_; lean_object* v_res_4204_; 
v_logExceptions_boxed_4203_ = lean_unbox(v_logExceptions_4199_);
v_res_4204_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(v_00_u03b1_4194_, v_eval_4195_, v_init_4196_, v_cfgs_4197_, v_onErr_4198_, v_logExceptions_boxed_4203_, v_a_4200_, v_a_4201_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
return v_res_4204_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_ConfigEval_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_Types(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

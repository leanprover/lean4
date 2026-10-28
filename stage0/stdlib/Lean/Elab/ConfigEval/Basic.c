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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v___y_243_);
lean_inc(v___y_244_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_246_);
v___x_255_ = lean_apply_7(v___x_3566__overap_254_, v___y_246_, v___y_245_, v___y_242_, v___y_244_, v___y_247_, v___y_243_, lean_box(0));
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
v___y_242_ = v___y_260_;
v___y_243_ = v___y_263_;
v___y_244_ = v___y_261_;
v___y_245_ = v___y_259_;
v___y_246_ = v___y_258_;
v___y_247_ = v___y_262_;
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
v___y_242_ = v___y_260_;
v___y_243_ = v___y_263_;
v___y_244_ = v___y_261_;
v___y_245_ = v___y_259_;
v___y_246_ = v___y_258_;
v___y_247_ = v___y_262_;
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1447_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1448_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
lean_ctor_set(v___x_1450_, 2, v___x_1449_);
lean_ctor_set(v___x_1450_, 3, v___x_1449_);
lean_ctor_set(v___x_1450_, 4, v___x_1448_);
lean_ctor_set(v___x_1450_, 5, v___x_1448_);
lean_ctor_set(v___x_1450_, 6, v___x_1448_);
lean_ctor_set(v___x_1450_, 7, v___x_1448_);
lean_ctor_set(v___x_1450_, 8, v___x_1448_);
lean_ctor_set(v___x_1450_, 9, v___x_1448_);
lean_ctor_set(v___x_1450_, 10, v___x_1448_);
lean_ctor_set(v___x_1450_, 11, v___x_1447_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_unsigned_to_nat(32u);
v___x_1452_ = lean_mk_empty_array_with_capacity(v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1454_ = ((size_t)5ULL);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_unsigned_to_nat(32u);
v___x_1457_ = lean_mk_empty_array_with_capacity(v___x_1456_);
v___x_1458_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1459_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___x_1457_);
lean_ctor_set(v___x_1459_, 2, v___x_1455_);
lean_ctor_set(v___x_1459_, 3, v___x_1455_);
lean_ctor_set_usize(v___x_1459_, 4, v___x_1454_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_box(1);
v___x_1461_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1462_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v___x_1460_);
return v___x_1463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1466_ = l_Lean_stringToMessageData(v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1469_ = l_Lean_stringToMessageData(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1472_ = l_Lean_stringToMessageData(v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1475_ = l_Lean_stringToMessageData(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1481_ = l_Lean_stringToMessageData(v___x_1480_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1484_ = l_Lean_stringToMessageData(v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1485_, lean_object* v_declHint_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_env_1491_; uint8_t v___x_1492_; 
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_st_ref_get(v___y_1487_);
v_env_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc_ref(v_env_1491_);
lean_dec(v___x_1490_);
v___x_1492_ = l_Lean_Name_isAnonymous(v_declHint_1486_);
if (v___x_1492_ == 0)
{
uint8_t v_isExporting_1493_; 
v_isExporting_1493_ = lean_ctor_get_uint8(v_env_1491_, sizeof(void*)*13);
if (v_isExporting_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_dec_ref(v_env_1491_);
lean_dec(v_declHint_1486_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_msg_1485_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
lean_inc_ref(v_env_1491_);
v___x_1495_ = l_Lean_Environment_setExporting(v_env_1491_, v___x_1492_);
lean_inc(v_declHint_1486_);
lean_inc_ref(v___x_1495_);
v___x_1496_ = l_Lean_Environment_contains(v___x_1495_, v_declHint_1486_, v_isExporting_1493_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_dec_ref(v___x_1495_);
lean_dec_ref(v_env_1491_);
lean_dec(v_declHint_1486_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_msg_1485_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_c_1503_; lean_object* v___x_1504_; 
v___x_1498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1499_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1500_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1495_);
v___x_1501_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1495_);
lean_ctor_set(v___x_1501_, 1, v___x_1498_);
lean_ctor_set(v___x_1501_, 2, v___x_1499_);
lean_ctor_set(v___x_1501_, 3, v___x_1500_);
lean_inc(v_declHint_1486_);
v___x_1502_ = l_Lean_MessageData_ofConstName(v_declHint_1486_, v___x_1492_);
v_c_1503_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1503_, 0, v___x_1501_);
lean_ctor_set(v_c_1503_, 1, v___x_1502_);
v___x_1504_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1495_, v_declHint_1486_);
lean_dec_ref(v___x_1495_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_env_1491_);
lean_dec(v_declHint_1486_);
v___x_1505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v_c_1503_);
v___x_1507_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Lean_MessageData_note(v___x_1508_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_msg_1485_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v_val_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1546_; 
v_val_1512_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1514_ = v___x_1504_;
v_isShared_1515_ = v_isSharedCheck_1546_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_val_1512_);
lean_dec(v___x_1504_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1546_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v_moduleNames_1517_; lean_object* v_mod_1518_; uint8_t v___x_1519_; 
v___x_1516_ = l_Lean_Environment_header(v_env_1491_);
lean_dec_ref(v_env_1491_);
v_moduleNames_1517_ = lean_ctor_get(v___x_1516_, 4);
lean_inc_ref(v_moduleNames_1517_);
lean_dec_ref(v___x_1516_);
v_mod_1518_ = lean_array_get(v___x_1489_, v_moduleNames_1517_, v_val_1512_);
lean_dec(v_val_1512_);
lean_dec_ref(v_moduleNames_1517_);
v___x_1519_ = l_Lean_isPrivateName(v_declHint_1486_);
lean_dec(v_declHint_1486_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v_c_1503_);
v___x_1522_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = l_Lean_MessageData_ofName(v_mod_1518_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Lean_MessageData_note(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_msg_1485_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1529_);
v___x_1531_ = v___x_1514_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v_c_1503_);
v___x_1535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_MessageData_ofName(v_mod_1518_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_MessageData_note(v___x_1540_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_msg_1485_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1542_);
v___x_1544_ = v___x_1514_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1547_; 
lean_dec_ref(v_env_1491_);
lean_dec(v_declHint_1486_);
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_msg_1485_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1548_, lean_object* v_declHint_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1548_, v_declHint_1549_, v___y_1550_);
lean_dec(v___y_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_1553_, lean_object* v_declHint_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1572_; 
v___x_1562_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1553_, v_declHint_1554_, v___y_1560_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = l_Lean_unknownIdentifierMessageTag;
v___x_1568_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v_a_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_1573_, lean_object* v_declHint_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1573_, v_declHint_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1583_, lean_object* v_msg_1584_, lean_object* v_declHint_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v_a_1594_; lean_object* v___x_1595_; 
v___x_1593_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1584_, v_declHint_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1583_, v_a_1594_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1596_, lean_object* v_msg_1597_, lean_object* v_declHint_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1596_, v_msg_1597_, v_declHint_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v_ref_1596_);
return v_res_1606_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_1610_, lean_object* v_constName_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1619_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1620_ = 0;
lean_inc(v_constName_1611_);
v___x_1621_ = l_Lean_MessageData_ofConstName(v_constName_1611_, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1610_, v___x_1624_, v_constName_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1626_, lean_object* v_constName_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1626_, v_constName_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v_ref_1626_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_ref_1644_; lean_object* v___x_1645_; 
v_ref_1644_ = lean_ctor_get(v___y_1641_, 2);
v___x_1645_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1644_, v_constName_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object* v_constName_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v_env_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = lean_st_ref_get(v___y_1661_);
v_env_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_env_1664_);
lean_dec(v___x_1663_);
v___x_1665_ = 0;
lean_inc(v_constName_1655_);
v___x_1666_ = l_Lean_Environment_findConstVal_x3f(v_env_1664_, v_constName_1655_, v___x_1665_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1667_;
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_constName_1655_);
v_val_1668_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1666_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_val_1668_);
lean_dec(v___x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 0);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_val_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
if (lean_obj_tag(v_a_1685_) == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = l_List_reverse___redArg(v_a_1686_);
return v___x_1687_;
}
else
{
lean_object* v_head_1688_; lean_object* v_tail_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1698_; 
v_head_1688_ = lean_ctor_get(v_a_1685_, 0);
v_tail_1689_ = lean_ctor_get(v_a_1685_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_a_1685_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1691_ = v_a_1685_;
v_isShared_1692_ = v_isSharedCheck_1698_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_tail_1689_);
lean_inc(v_head_1688_);
lean_dec(v_a_1685_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1698_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1693_ = l_Lean_mkLevelParam(v_head_1688_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v_a_1686_);
lean_ctor_set(v___x_1691_, 0, v___x_1693_);
v___x_1695_ = v___x_1691_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_a_1686_);
v___x_1695_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
v_a_1685_ = v_tail_1689_;
v_a_1686_ = v___x_1695_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object* v_constName_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
lean_inc(v_constName_1699_);
v___x_1707_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1719_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1719_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1719_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_levelParams_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v_levelParams_1712_ = lean_ctor_get(v_a_1708_, 1);
lean_inc(v_levelParams_1712_);
lean_dec(v_a_1708_);
v___x_1713_ = lean_box(0);
v___x_1714_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_1712_, v___x_1713_);
v___x_1715_ = l_Lean_mkConst(v_constName_1699_, v___x_1714_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1715_);
v___x_1717_ = v___x_1710_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_constName_1699_);
v_a_1720_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1707_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1707_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object* v_constName_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; lean_object* v_infoState_1741_; uint8_t v_enabled_1742_; 
v___x_1740_ = lean_st_ref_get(v___y_1738_);
v_infoState_1741_ = lean_ctor_get(v___x_1740_, 8);
lean_inc_ref(v_infoState_1741_);
lean_dec(v___x_1740_);
v_enabled_1742_ = lean_ctor_get_uint8(v_infoState_1741_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1741_);
if (v_enabled_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec_ref(v_t_1737_);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v_infoState_1746_; lean_object* v_env_1747_; lean_object* v_nextMacroScope_1748_; lean_object* v_ngen_1749_; lean_object* v_auxDeclNGen_1750_; lean_object* v_traceState_1751_; lean_object* v_cache_1752_; lean_object* v_recordedDeps_1753_; lean_object* v_messages_1754_; lean_object* v_snapshotTasks_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1777_; 
v___x_1745_ = lean_st_ref_take(v___y_1738_);
v_infoState_1746_ = lean_ctor_get(v___x_1745_, 8);
v_env_1747_ = lean_ctor_get(v___x_1745_, 0);
v_nextMacroScope_1748_ = lean_ctor_get(v___x_1745_, 1);
v_ngen_1749_ = lean_ctor_get(v___x_1745_, 2);
v_auxDeclNGen_1750_ = lean_ctor_get(v___x_1745_, 3);
v_traceState_1751_ = lean_ctor_get(v___x_1745_, 4);
v_cache_1752_ = lean_ctor_get(v___x_1745_, 5);
v_recordedDeps_1753_ = lean_ctor_get(v___x_1745_, 6);
v_messages_1754_ = lean_ctor_get(v___x_1745_, 7);
v_snapshotTasks_1755_ = lean_ctor_get(v___x_1745_, 9);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1757_ = v___x_1745_;
v_isShared_1758_ = v_isSharedCheck_1777_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_snapshotTasks_1755_);
lean_inc(v_infoState_1746_);
lean_inc(v_messages_1754_);
lean_inc(v_recordedDeps_1753_);
lean_inc(v_cache_1752_);
lean_inc(v_traceState_1751_);
lean_inc(v_auxDeclNGen_1750_);
lean_inc(v_ngen_1749_);
lean_inc(v_nextMacroScope_1748_);
lean_inc(v_env_1747_);
lean_dec(v___x_1745_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1777_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
uint8_t v_enabled_1759_; lean_object* v_assignment_1760_; lean_object* v_lazyAssignment_1761_; lean_object* v_trees_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1776_; 
v_enabled_1759_ = lean_ctor_get_uint8(v_infoState_1746_, sizeof(void*)*3);
v_assignment_1760_ = lean_ctor_get(v_infoState_1746_, 0);
v_lazyAssignment_1761_ = lean_ctor_get(v_infoState_1746_, 1);
v_trees_1762_ = lean_ctor_get(v_infoState_1746_, 2);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_infoState_1746_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1764_ = v_infoState_1746_;
v_isShared_1765_ = v_isSharedCheck_1776_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_trees_1762_);
lean_inc(v_lazyAssignment_1761_);
lean_inc(v_assignment_1760_);
lean_dec(v_infoState_1746_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1776_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1766_ = lean_box(0);
v___x_1767_ = l_Lean_PersistentArray_push___redArg(v_trees_1762_, v_t_1737_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 2, v___x_1767_);
v___x_1769_ = v___x_1764_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_assignment_1760_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_lazyAssignment_1761_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v___x_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1775_, sizeof(void*)*3, v_enabled_1759_);
v___x_1769_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 8, v___x_1769_);
v___x_1771_ = v___x_1757_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_env_1747_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_nextMacroScope_1748_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_ngen_1749_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_auxDeclNGen_1750_);
lean_ctor_set(v_reuseFailAlloc_1774_, 4, v_traceState_1751_);
lean_ctor_set(v_reuseFailAlloc_1774_, 5, v_cache_1752_);
lean_ctor_set(v_reuseFailAlloc_1774_, 6, v_recordedDeps_1753_);
lean_ctor_set(v_reuseFailAlloc_1774_, 7, v_messages_1754_);
lean_ctor_set(v_reuseFailAlloc_1774_, 8, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1774_, 9, v_snapshotTasks_1755_);
v___x_1771_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_st_ref_put(v___y_1738_, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1766_);
return v___x_1773_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1778_, v___y_1779_);
lean_dec(v___y_1779_);
return v_res_1781_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_unsigned_to_nat(32u);
v___x_1783_ = lean_mk_empty_array_with_capacity(v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1785_ = ((size_t)5ULL);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_unsigned_to_nat(32u);
v___x_1788_ = lean_mk_empty_array_with_capacity(v___x_1787_);
v___x_1789_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
v___x_1790_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1788_);
lean_ctor_set(v___x_1790_, 2, v___x_1786_);
lean_ctor_set(v___x_1790_, 3, v___x_1786_);
lean_ctor_set_usize(v___x_1790_, 4, v___x_1785_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object* v_t_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v_infoState_1800_; uint8_t v_enabled_1801_; 
v___x_1799_ = lean_st_ref_get(v___y_1797_);
v_infoState_1800_ = lean_ctor_get(v___x_1799_, 8);
lean_inc_ref(v_infoState_1800_);
lean_dec(v___x_1799_);
v_enabled_1801_ = lean_ctor_get_uint8(v_infoState_1800_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1800_);
if (v_enabled_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_dec_ref(v_t_1791_);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
v___x_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_t_1791_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_1805_, v___y_1797_);
return v___x_1806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object* v_t_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object* v_stx_1816_, lean_object* v_n_1817_, lean_object* v_expectedType_x3f_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_1817_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = lean_box(0);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_stx_1816_);
v___x_1830_ = l_Lean_LocalContext_empty;
v___x_1831_ = 0;
v___x_1832_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1832_, 0, v___x_1829_);
lean_ctor_set(v___x_1832_, 1, v___x_1830_);
lean_ctor_set(v___x_1832_, 2, v_expectedType_x3f_1818_);
lean_ctor_set(v___x_1832_, 3, v_a_1827_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*4, v___x_1831_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*4 + 1, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
v___x_1834_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1833_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
return v___x_1834_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_expectedType_x3f_1818_);
lean_dec(v_stx_1816_);
v_a_1835_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1826_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1826_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object* v_stx_1843_, lean_object* v_n_1844_, lean_object* v_expectedType_x3f_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1843_, v_n_1844_, v_expectedType_x3f_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object* v_item_1854_, lean_object* v_projFn_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___x_1863_; lean_object* v_infoState_1864_; uint8_t v_enabled_1865_; 
v___x_1863_ = lean_st_ref_get(v_a_1861_);
v_infoState_1864_ = lean_ctor_get(v___x_1863_, 8);
lean_inc_ref(v_infoState_1864_);
lean_dec(v___x_1863_);
v_enabled_1865_ = lean_ctor_get_uint8(v_infoState_1864_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1864_);
if (v_enabled_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec(v_projFn_1855_);
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v_env_1869_; uint8_t v___x_1870_; 
v___x_1868_ = lean_st_ref_get(v_a_1861_);
v_env_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_ref(v_env_1869_);
lean_dec(v___x_1868_);
lean_inc(v_projFn_1855_);
v___x_1870_ = l_Lean_Environment_contains(v_env_1869_, v_projFn_1855_, v_enabled_1865_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v_projFn_1855_);
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1854_);
v___x_1874_ = lean_box(0);
v___x_1875_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_1873_, v_projFn_1855_, v___x_1874_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object* v_item_1876_, lean_object* v_projFn_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1876_, v_projFn_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec_ref(v_item_1876_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object* v_t_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1886_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1904_, lean_object* v_constName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1914_, lean_object* v_constName_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1914_, v_constName_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_1924_, lean_object* v_ref_1925_, lean_object* v_constName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1925_, v_constName_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_ref_1936_, lean_object* v_constName_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_1935_, v_ref_1936_, v_constName_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v_ref_1936_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1946_, lean_object* v_ref_1947_, lean_object* v_msg_1948_, lean_object* v_declHint_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1947_, v_msg_1948_, v_declHint_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1958_, lean_object* v_ref_1959_, lean_object* v_msg_1960_, lean_object* v_declHint_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1958_, v_ref_1959_, v_msg_1960_, v_declHint_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_ref_1959_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_1970_, lean_object* v_declHint_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1970_, v_declHint_1971_, v___y_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1980_, lean_object* v_declHint_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object* v_info_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_info_1990_);
v___x_1999_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1998_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(lean_object* v_info_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2008_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2011_ = lean_box(1);
v___x_2012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2013_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_2014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_2012_);
lean_ctor_set(v___x_2014_, 2, v___x_2011_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object* v_item_2015_, lean_object* v_structName_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v_infoState_2025_; uint8_t v_enabled_2026_; 
v___x_2024_ = lean_st_ref_get(v_a_2022_);
v_infoState_2025_ = lean_ctor_get(v___x_2024_, 8);
lean_inc_ref(v_infoState_2025_);
lean_dec(v___x_2024_);
v_enabled_2026_ = lean_ctor_get_uint8(v_infoState_2025_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2025_);
if (v_enabled_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec(v_structName_2016_);
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
else
{
lean_object* v___x_2029_; lean_object* v_env_2030_; uint8_t v___x_2031_; 
v___x_2029_ = lean_st_ref_get(v_a_2022_);
v_env_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_ref(v_env_2030_);
lean_dec(v___x_2029_);
lean_inc(v_structName_2016_);
v___x_2031_ = l_Lean_Environment_contains(v_env_2030_, v_structName_2016_, v_enabled_2026_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec(v_structName_2016_);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2034_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_2015_);
v___x_2035_ = l_Lean_Syntax_getId(v___x_2034_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2038_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2034_);
lean_ctor_set(v___x_2038_, 1, v___x_2036_);
lean_ctor_set(v___x_2038_, 2, v___x_2037_);
lean_ctor_set(v___x_2038_, 3, v_structName_2016_);
v___x_2039_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2038_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
return v___x_2039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object* v_item_2040_, lean_object* v_structName_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2040_, v_structName_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec_ref(v_item_2040_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object* v_cfg_2050_, lean_object* v_withRef_2051_, lean_object* v___x_2052_, lean_object* v_oldRef_2053_){
_start:
{
lean_object* v_ref_2054_; lean_object* v___x_2055_; 
v_ref_2054_ = l_Lean_replaceRef(v_cfg_2050_, v_oldRef_2053_);
v___x_2055_ = lean_apply_3(v_withRef_2051_, lean_box(0), v_ref_2054_, v___x_2052_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object* v_cfg_2056_, lean_object* v_withRef_2057_, lean_object* v___x_2058_, lean_object* v_oldRef_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(v_cfg_2056_, v_withRef_2057_, v___x_2058_, v_oldRef_2059_);
lean_dec(v_oldRef_2059_);
lean_dec(v_cfg_2056_);
return v_res_2060_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t v_x_2061_){
_start:
{
uint32_t v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = 46;
v___x_2063_ = lean_uint32_dec_eq(v_x_2061_, v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object* v_x_2064_){
_start:
{
uint32_t v_x_917__boxed_2065_; uint8_t v_res_2066_; lean_object* v_r_2067_; 
v_x_917__boxed_2065_ = lean_unbox_uint32(v_x_2064_);
lean_dec(v_x_2064_);
v_res_2066_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_917__boxed_2065_);
v_r_2067_ = lean_box(v_res_2066_);
return v_r_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object* v___f_2068_, lean_object* v_s_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2068_);
v___x_2077_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2069_, v___x_2076_, v___y_2070_, lean_box(0), lean_box(0), v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object* v___f_2079_, lean_object* v_si_2080_, lean_object* v_val_2081_){
_start:
{
lean_object* v___y_2083_; lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___f_2089_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0));
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_string_utf8_byte_size(v_val_2081_);
lean_inc_ref(v_val_2081_);
v___x_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2092_, 0, v_val_2081_);
lean_ctor_set(v___x_2092_, 1, v___x_2090_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
v___x_2093_ = l_String_Slice_contains___redArg(v___f_2079_, v___x_2092_, v___f_2089_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_box(0);
lean_inc_ref(v_val_2081_);
v___x_2095_ = l_Lean_Name_str___override(v___x_2094_, v_val_2081_);
v___y_2083_ = v___x_2095_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2096_; 
lean_inc_ref(v_val_2081_);
v___x_2096_ = l_String_toName(v_val_2081_);
v___y_2083_ = v___x_2096_;
goto v___jp_2082_;
}
v___jp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_string_utf8_byte_size(v_val_2081_);
v___x_2086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2086_, 0, v_val_2081_);
lean_ctor_set(v___x_2086_, 1, v___x_2084_);
lean_ctor_set(v___x_2086_, 2, v___x_2085_);
v___x_2087_ = lean_box(0);
v___x_2088_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2088_, 0, v_si_2080_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
lean_ctor_set(v___x_2088_, 2, v___y_2083_);
lean_ctor_set(v___x_2088_, 3, v___x_2087_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object* v_atomAsIdent_2097_, lean_object* v_stx_2098_){
_start:
{
switch(lean_obj_tag(v_stx_2098_))
{
case 3:
{
lean_object* v___x_2099_; 
lean_dec_ref(v_atomAsIdent_2097_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_stx_2098_);
return v___x_2099_;
}
case 2:
{
lean_object* v_info_2100_; lean_object* v_val_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_info_2100_ = lean_ctor_get(v_stx_2098_, 0);
lean_inc(v_info_2100_);
v_val_2101_ = lean_ctor_get(v_stx_2098_, 1);
lean_inc_ref(v_val_2101_);
lean_dec_ref_known(v_stx_2098_, 2);
v___x_2102_ = lean_apply_2(v_atomAsIdent_2097_, v_info_2100_, v_val_2101_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
default: 
{
lean_object* v___x_2104_; 
lean_dec(v_stx_2098_);
lean_dec_ref(v_atomAsIdent_2097_);
v___x_2104_ = lean_box(0);
return v___x_2104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_init_2130_, lean_object* v_cfgs_2131_, lean_object* v_k_2132_, lean_object* v_onErr_2133_){
_start:
{
lean_object* v_toApplicative_2134_; lean_object* v_toPure_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_toApplicative_2134_ = lean_ctor_get(v_inst_2128_, 0);
v_toPure_2135_ = lean_ctor_get(v_toApplicative_2134_, 1);
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_array_get_size(v_cfgs_2131_);
v___x_2138_ = lean_nat_dec_lt(v___x_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; 
lean_inc(v_toPure_2135_);
lean_dec(v_onErr_2133_);
lean_dec(v_k_2132_);
lean_dec_ref(v_cfgs_2131_);
lean_dec_ref(v_inst_2129_);
lean_dec_ref(v_inst_2128_);
v___x_2139_ = lean_apply_2(v_toPure_2135_, lean_box(0), v_init_2130_);
return v___x_2139_;
}
else
{
lean_object* v___f_2140_; size_t v___x_2141_; size_t v___x_2142_; lean_object* v___x_2143_; 
lean_inc_ref(v_inst_2128_);
v___f_2140_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_2140_, 0, v_inst_2128_);
lean_closure_set(v___f_2140_, 1, v_inst_2129_);
lean_closure_set(v___f_2140_, 2, v_k_2132_);
lean_closure_set(v___f_2140_, 3, v_onErr_2133_);
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = lean_usize_of_nat(v___x_2137_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2128_, v___f_2140_, v_cfgs_2131_, v___x_2141_, v___x_2142_, v_init_2130_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_init_2146_, lean_object* v_cfg_2147_, lean_object* v_k_2148_, lean_object* v_onErr_2149_){
_start:
{
lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2147_);
v___x_2169_ = l_Lean_Syntax_isOfKind(v_cfg_2147_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2170_ = l_Lean_Syntax_getNumArgs(v_cfg_2147_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_dec_eq(v___x_2170_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___f_2173_; lean_object* v_atomAsIdent_2174_; uint8_t v___x_2175_; 
v___f_2173_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3));
v_atomAsIdent_2174_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4));
v___x_2175_ = lean_nat_dec_le(v___x_2171_, v___x_2170_);
if (v___x_2175_ == 0)
{
lean_dec(v___x_2170_);
if (lean_obj_tag(v_cfg_2147_) == 2)
{
lean_object* v_info_2176_; lean_object* v_val_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_dec(v_onErr_2149_);
lean_dec_ref(v_inst_2145_);
lean_dec_ref(v_inst_2144_);
v_info_2176_ = lean_ctor_get(v_cfg_2147_, 0);
v_val_2177_ = lean_ctor_get(v_cfg_2147_, 1);
lean_inc_ref(v_val_2177_);
lean_inc(v_info_2176_);
v___x_2178_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(v___f_2173_, v_info_2176_, v_val_2177_);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2180_ = l_Lean_mkCIdentFrom(v_cfg_2147_, v___x_2179_, v___x_2175_);
v___x_2181_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2182_ = l_Lean_TSyntax_getId(v___x_2178_);
v___x_2183_ = l_Lean_Name_eraseMacroScopes(v___x_2182_);
lean_dec(v___x_2182_);
v___x_2184_ = lean_box(0);
lean_inc(v___x_2178_);
v___x_2185_ = l_Lean_Syntax_identComponents(v___x_2178_, v___x_2184_);
v___x_2186_ = lean_box(0);
v___x_2187_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2187_, 0, v_cfg_2147_);
lean_ctor_set(v___x_2187_, 1, v___x_2178_);
lean_ctor_set(v___x_2187_, 2, v___x_2180_);
lean_ctor_set(v___x_2187_, 3, v___x_2181_);
lean_ctor_set(v___x_2187_, 4, v___x_2183_);
lean_ctor_set(v___x_2187_, 5, v___x_2185_);
lean_ctor_set(v___x_2187_, 6, v___x_2186_);
v___x_2188_ = lean_apply_2(v_k_2148_, v_init_2146_, v___x_2187_);
return v___x_2188_;
}
else
{
lean_dec(v_k_2148_);
goto v___jp_2161_;
}
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = l_Lean_Syntax_getArg(v_cfg_2147_, v___x_2189_);
if (lean_obj_tag(v___x_2190_) == 2)
{
lean_object* v_val_2191_; lean_object* v___y_2193_; uint8_t v_val_2194_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_val_2191_ = lean_ctor_get(v___x_2190_, 1);
v___x_2205_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2206_ = lean_string_dec_eq(v_val_2191_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2208_ = lean_string_dec_eq(v_val_2191_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
lean_inc_ref(v_val_2191_);
lean_dec_ref_known(v___x_2190_, 2);
v___x_2209_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2210_ = lean_string_dec_eq(v_val_2191_, v___x_2209_);
lean_dec_ref(v_val_2191_);
if (v___x_2210_ == 0)
{
lean_dec(v___x_2170_);
lean_dec(v_k_2148_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_unsigned_to_nat(5u);
v___x_2212_ = lean_nat_dec_le(v___x_2170_, v___x_2211_);
lean_dec(v___x_2170_);
if (v___x_2212_ == 0)
{
lean_dec(v_k_2148_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = l_Lean_Syntax_getArg(v_cfg_2147_, v___x_2171_);
v___x_2214_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2174_, v___x_2213_);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec(v_onErr_2149_);
lean_dec_ref(v_inst_2145_);
lean_dec_ref(v_inst_2144_);
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc_n(v_val_2215_, 2);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_unsigned_to_nat(3u);
v___x_2217_ = l_Lean_Syntax_getArg(v_cfg_2147_, v___x_2216_);
v___x_2218_ = lean_box(0);
v___x_2219_ = l_Lean_TSyntax_getId(v_val_2215_);
v___x_2220_ = l_Lean_Name_eraseMacroScopes(v___x_2219_);
lean_dec(v___x_2219_);
v___x_2221_ = l_Lean_Syntax_identComponents(v_val_2215_, v___x_2218_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2223_, 0, v_cfg_2147_);
lean_ctor_set(v___x_2223_, 1, v_val_2215_);
lean_ctor_set(v___x_2223_, 2, v___x_2217_);
lean_ctor_set(v___x_2223_, 3, v___x_2218_);
lean_ctor_set(v___x_2223_, 4, v___x_2220_);
lean_ctor_set(v___x_2223_, 5, v___x_2221_);
lean_ctor_set(v___x_2223_, 6, v___x_2222_);
v___x_2224_ = lean_apply_2(v_k_2148_, v_init_2146_, v___x_2223_);
return v___x_2224_;
}
else
{
lean_dec(v___x_2214_);
lean_dec(v_k_2148_);
goto v___jp_2161_;
}
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_box(v___x_2206_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
v___y_2193_ = v___x_2226_;
v_val_2194_ = v___x_2206_;
goto v___jp_2192_;
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_box(v___x_2175_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
v___y_2193_ = v___x_2228_;
v_val_2194_ = v___x_2175_;
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = lean_unsigned_to_nat(2u);
v___x_2196_ = lean_nat_dec_eq(v___x_2170_, v___x_2195_);
lean_dec(v___x_2170_);
if (v___x_2196_ == 0)
{
lean_dec(v___y_2193_);
lean_dec_ref_known(v___x_2190_, 2);
lean_dec(v_k_2148_);
goto v___jp_2161_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = l_Lean_Syntax_getArg(v_cfg_2147_, v___x_2171_);
v___x_2198_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2174_, v___x_2197_);
if (lean_obj_tag(v___x_2198_) == 1)
{
lean_dec(v_onErr_2149_);
lean_dec_ref(v_inst_2145_);
lean_dec_ref(v_inst_2144_);
if (v_val_2194_ == 0)
{
lean_object* v_val_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_val_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_val_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2201_ = l_Lean_mkCIdentFrom(v___x_2190_, v___x_2200_, v_val_2194_);
lean_dec_ref_known(v___x_2190_, 2);
v___y_2151_ = v___y_2193_;
v___y_2152_ = v_val_2199_;
v___y_2153_ = v___x_2201_;
goto v___jp_2150_;
}
else
{
lean_object* v_val_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_val_2202_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_val_2202_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2203_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2204_ = l_Lean_mkCIdentFrom(v___x_2190_, v___x_2203_, v___x_2172_);
lean_dec_ref_known(v___x_2190_, 2);
v___y_2151_ = v___y_2193_;
v___y_2152_ = v_val_2202_;
v___y_2153_ = v___x_2204_;
goto v___jp_2150_;
}
}
else
{
lean_dec(v___x_2198_);
lean_dec(v___y_2193_);
lean_dec_ref_known(v___x_2190_, 2);
lean_dec(v_k_2148_);
goto v___jp_2161_;
}
}
}
}
else
{
lean_dec(v___x_2190_);
lean_dec(v___x_2170_);
lean_dec(v_k_2148_);
goto v___jp_2161_;
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v___x_2170_);
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = l_Lean_Syntax_getArg(v_cfg_2147_, v___x_2229_);
lean_dec(v_cfg_2147_);
v_cfg_2147_ = v___x_2230_;
goto _start;
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = l_Lean_Syntax_getArgs(v_cfg_2147_);
lean_dec(v_cfg_2147_);
v___x_2233_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2144_, v_inst_2145_, v_init_2146_, v___x_2232_, v_k_2148_, v_onErr_2149_);
return v___x_2233_;
}
v___jp_2150_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2154_ = l_Lean_TSyntax_getId(v___y_2152_);
v___x_2155_ = l_Lean_Name_eraseMacroScopes(v___x_2154_);
lean_dec(v___x_2154_);
v___x_2156_ = lean_box(0);
lean_inc(v___y_2152_);
v___x_2157_ = l_Lean_Syntax_identComponents(v___y_2152_, v___x_2156_);
v___x_2158_ = lean_box(0);
v___x_2159_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2159_, 0, v_cfg_2147_);
lean_ctor_set(v___x_2159_, 1, v___y_2152_);
lean_ctor_set(v___x_2159_, 2, v___y_2153_);
lean_ctor_set(v___x_2159_, 3, v___y_2151_);
lean_ctor_set(v___x_2159_, 4, v___x_2155_);
lean_ctor_set(v___x_2159_, 5, v___x_2157_);
lean_ctor_set(v___x_2159_, 6, v___x_2158_);
v___x_2160_ = lean_apply_2(v_k_2148_, v_init_2146_, v___x_2159_);
return v___x_2160_;
}
v___jp_2161_:
{
lean_object* v_toBind_2162_; lean_object* v_getRef_2163_; lean_object* v_withRef_2164_; lean_object* v___x_2165_; lean_object* v___f_2166_; lean_object* v___x_2167_; 
v_toBind_2162_ = lean_ctor_get(v_inst_2144_, 1);
lean_inc(v_toBind_2162_);
lean_dec_ref(v_inst_2144_);
v_getRef_2163_ = lean_ctor_get(v_inst_2145_, 0);
lean_inc(v_getRef_2163_);
v_withRef_2164_ = lean_ctor_get(v_inst_2145_, 1);
lean_inc(v_withRef_2164_);
lean_dec_ref(v_inst_2145_);
lean_inc(v_cfg_2147_);
v___x_2165_ = lean_apply_2(v_onErr_2149_, v_init_2146_, v_cfg_2147_);
v___f_2166_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2166_, 0, v_cfg_2147_);
lean_closure_set(v___f_2166_, 1, v_withRef_2164_);
lean_closure_set(v___f_2166_, 2, v___x_2165_);
v___x_2167_ = lean_apply_4(v_toBind_2162_, lean_box(0), lean_box(0), v_getRef_2163_, v___f_2166_);
return v___x_2167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_k_2236_, lean_object* v_onErr_2237_, lean_object* v_x_2238_, lean_object* v_cfg_x27_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2234_, v_inst_2235_, v_x_2238_, v_cfg_x27_2239_, v_k_2236_, v_onErr_2237_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object* v_00_u03b1_2241_, lean_object* v_m_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_init_2245_, lean_object* v_cfg_2246_, lean_object* v_k_2247_, lean_object* v_onErr_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2243_, v_inst_2244_, v_init_2245_, v_cfg_2246_, v_k_2247_, v_onErr_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object* v_00_u03b1_2250_, lean_object* v_m_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_init_2254_, lean_object* v_cfgs_2255_, lean_object* v_k_2256_, lean_object* v_onErr_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2252_, v_inst_2253_, v_init_2254_, v_cfgs_2255_, v_k_2256_, v_onErr_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_2267_, lean_object* v_x_2268_){
_start:
{
if (lean_obj_tag(v_x_2268_) == 1)
{
lean_object* v_pre_2269_; 
v_pre_2269_ = lean_ctor_get(v_x_2268_, 0);
switch(lean_obj_tag(v_pre_2269_))
{
case 1:
{
lean_object* v_pre_2270_; 
v_pre_2270_ = lean_ctor_get(v_pre_2269_, 0);
switch(lean_obj_tag(v_pre_2270_))
{
case 0:
{
lean_object* v_str_2271_; lean_object* v_str_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_str_2271_ = lean_ctor_get(v_x_2268_, 1);
v_str_2272_ = lean_ctor_get(v_pre_2269_, 1);
v___x_2273_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_2274_ = lean_string_dec_eq(v_str_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_2276_ = lean_string_dec_eq(v_str_2272_, v___x_2275_);
if (v___x_2276_ == 0)
{
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_2278_ = lean_string_dec_eq(v_str_2271_, v___x_2277_);
if (v___x_2278_ == 0)
{
return v___x_2278_;
}
else
{
return v_suppressElabErrors_2267_;
}
}
}
else
{
lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_2280_ = lean_string_dec_eq(v_str_2271_, v___x_2279_);
if (v___x_2280_ == 0)
{
return v___x_2280_;
}
else
{
return v_suppressElabErrors_2267_;
}
}
}
case 1:
{
lean_object* v_pre_2281_; 
v_pre_2281_ = lean_ctor_get(v_pre_2270_, 0);
if (lean_obj_tag(v_pre_2281_) == 0)
{
lean_object* v_str_2282_; lean_object* v_str_2283_; lean_object* v_str_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_str_2282_ = lean_ctor_get(v_x_2268_, 1);
v_str_2283_ = lean_ctor_get(v_pre_2269_, 1);
v_str_2284_ = lean_ctor_get(v_pre_2270_, 1);
v___x_2285_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_2286_ = lean_string_dec_eq(v_str_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
return v___x_2286_;
}
else
{
lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_2288_ = lean_string_dec_eq(v_str_2283_, v___x_2287_);
if (v___x_2288_ == 0)
{
return v___x_2288_;
}
else
{
lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_2290_ = lean_string_dec_eq(v_str_2282_, v___x_2289_);
if (v___x_2290_ == 0)
{
return v___x_2290_;
}
else
{
return v_suppressElabErrors_2267_;
}
}
}
}
else
{
uint8_t v___x_2291_; 
v___x_2291_ = 0;
return v___x_2291_;
}
}
default: 
{
uint8_t v___x_2292_; 
v___x_2292_ = 0;
return v___x_2292_;
}
}
}
case 0:
{
lean_object* v_str_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_str_2293_ = lean_ctor_get(v_x_2268_, 1);
v___x_2294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_2295_ = lean_string_dec_eq(v_str_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
return v___x_2295_;
}
else
{
return v_suppressElabErrors_2267_;
}
}
default: 
{
uint8_t v___x_2296_; 
v___x_2296_ = 0;
return v___x_2296_;
}
}
}
else
{
uint8_t v___x_2297_; 
v___x_2297_ = 0;
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2298_, lean_object* v_x_2299_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2300_; uint8_t v_res_2301_; lean_object* v_r_2302_; 
v_suppressElabErrors_boxed_2300_ = lean_unbox(v_suppressElabErrors_2298_);
v_res_2301_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_2300_, v_x_2299_);
lean_dec(v_x_2299_);
v_r_2302_ = lean_box(v_res_2301_);
return v_r_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2303_, lean_object* v_msgData_2304_, uint8_t v_severity_2305_, uint8_t v_isSilent_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; uint8_t v___y_2317_; lean_object* v___y_2318_; uint8_t v___y_2319_; lean_object* v_toCold_2320_; lean_object* v___y_2321_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; uint8_t v___y_2353_; uint8_t v___y_2354_; lean_object* v___y_2355_; uint8_t v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2377_; uint8_t v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; uint8_t v___y_2382_; lean_object* v___y_2383_; uint8_t v___y_2387_; uint8_t v___y_2388_; uint8_t v___x_2398_; uint8_t v___y_2400_; uint8_t v___x_2406_; 
v___x_2398_ = 2;
v___x_2406_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2305_, v___x_2398_);
if (v___x_2406_ == 0)
{
v___y_2400_ = v___x_2406_;
goto v___jp_2399_;
}
else
{
uint8_t v___x_2407_; 
lean_inc_ref(v_msgData_2304_);
v___x_2407_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2304_);
if (v___x_2407_ == 0)
{
v___y_2400_ = v___x_2407_;
goto v___jp_2399_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec_ref(v_msgData_2304_);
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
v___jp_2312_:
{
lean_object* v_currNamespace_2322_; lean_object* v_openDecls_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v_env_2328_; lean_object* v_nextMacroScope_2329_; lean_object* v_ngen_2330_; lean_object* v_auxDeclNGen_2331_; lean_object* v_traceState_2332_; lean_object* v_cache_2333_; lean_object* v_recordedDeps_2334_; lean_object* v_messages_2335_; lean_object* v_infoState_2336_; lean_object* v_snapshotTasks_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2348_; 
v_currNamespace_2322_ = lean_ctor_get(v_toCold_2320_, 4);
v_openDecls_2323_ = lean_ctor_get(v_toCold_2320_, 5);
lean_inc(v_openDecls_2323_);
lean_inc(v_currNamespace_2322_);
v___x_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2324_, 0, v_currNamespace_2322_);
lean_ctor_set(v___x_2324_, 1, v_openDecls_2323_);
v___x_2325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v___y_2315_);
lean_inc_ref(v___y_2318_);
lean_inc_ref(v___y_2314_);
v___x_2326_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2326_, 0, v___y_2314_);
lean_ctor_set(v___x_2326_, 1, v___y_2316_);
lean_ctor_set(v___x_2326_, 2, v___y_2313_);
lean_ctor_set(v___x_2326_, 3, v___y_2318_);
lean_ctor_set(v___x_2326_, 4, v___x_2325_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*5, v___y_2319_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*5 + 1, v___y_2317_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*5 + 2, v_isSilent_2306_);
v___x_2327_ = lean_st_ref_take(v___y_2321_);
v_env_2328_ = lean_ctor_get(v___x_2327_, 0);
v_nextMacroScope_2329_ = lean_ctor_get(v___x_2327_, 1);
v_ngen_2330_ = lean_ctor_get(v___x_2327_, 2);
v_auxDeclNGen_2331_ = lean_ctor_get(v___x_2327_, 3);
v_traceState_2332_ = lean_ctor_get(v___x_2327_, 4);
v_cache_2333_ = lean_ctor_get(v___x_2327_, 5);
v_recordedDeps_2334_ = lean_ctor_get(v___x_2327_, 6);
v_messages_2335_ = lean_ctor_get(v___x_2327_, 7);
v_infoState_2336_ = lean_ctor_get(v___x_2327_, 8);
v_snapshotTasks_2337_ = lean_ctor_get(v___x_2327_, 9);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2339_ = v___x_2327_;
v_isShared_2340_ = v_isSharedCheck_2348_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_snapshotTasks_2337_);
lean_inc(v_infoState_2336_);
lean_inc(v_messages_2335_);
lean_inc(v_recordedDeps_2334_);
lean_inc(v_cache_2333_);
lean_inc(v_traceState_2332_);
lean_inc(v_auxDeclNGen_2331_);
lean_inc(v_ngen_2330_);
lean_inc(v_nextMacroScope_2329_);
lean_inc(v_env_2328_);
lean_dec(v___x_2327_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2348_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2341_ = lean_box(0);
v___x_2342_ = l_Lean_MessageLog_add(v___x_2326_, v_messages_2335_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 7, v___x_2342_);
v___x_2344_ = v___x_2339_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_env_2328_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_nextMacroScope_2329_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_ngen_2330_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_auxDeclNGen_2331_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_traceState_2332_);
lean_ctor_set(v_reuseFailAlloc_2347_, 5, v_cache_2333_);
lean_ctor_set(v_reuseFailAlloc_2347_, 6, v_recordedDeps_2334_);
lean_ctor_set(v_reuseFailAlloc_2347_, 7, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2347_, 8, v_infoState_2336_);
lean_ctor_set(v_reuseFailAlloc_2347_, 9, v_snapshotTasks_2337_);
v___x_2344_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_st_ref_put(v___y_2321_, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2341_);
return v___x_2346_;
}
}
}
v___jp_2349_:
{
lean_object* v_fileName_2358_; lean_object* v_fileMap_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2375_; 
v_fileName_2358_ = lean_ctor_get(v___y_2355_, 0);
v_fileMap_2359_ = lean_ctor_get(v___y_2355_, 1);
v___x_2360_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2304_);
v___x_2361_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_2360_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_inc_ref_n(v_fileMap_2359_, 2);
v___x_2366_ = l_Lean_FileMap_toPosition(v_fileMap_2359_, v___y_2352_);
lean_dec(v___y_2352_);
v___x_2367_ = l_Lean_FileMap_toPosition(v_fileMap_2359_, v___y_2357_);
lean_dec(v___y_2357_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
if (v___y_2353_ == 0)
{
lean_del_object(v___x_2364_);
lean_dec_ref(v___y_2350_);
v___y_2313_ = v___x_2368_;
v___y_2314_ = v_fileName_2358_;
v___y_2315_ = v_a_2362_;
v___y_2316_ = v___x_2366_;
v___y_2317_ = v___y_2354_;
v___y_2318_ = v___x_2369_;
v___y_2319_ = v___y_2356_;
v_toCold_2320_ = v___y_2351_;
v___y_2321_ = v___y_2310_;
goto v___jp_2312_;
}
else
{
uint8_t v___x_2370_; 
lean_inc(v_a_2362_);
v___x_2370_ = l_Lean_MessageData_hasTag(v___y_2350_, v_a_2362_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_dec_ref_known(v___x_2368_, 1);
lean_dec_ref(v___x_2366_);
lean_dec(v_a_2362_);
v___x_2371_ = lean_box(0);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2371_);
v___x_2373_ = v___x_2364_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
else
{
lean_del_object(v___x_2364_);
v___y_2313_ = v___x_2368_;
v___y_2314_ = v_fileName_2358_;
v___y_2315_ = v_a_2362_;
v___y_2316_ = v___x_2366_;
v___y_2317_ = v___y_2354_;
v___y_2318_ = v___x_2369_;
v___y_2319_ = v___y_2356_;
v_toCold_2320_ = v___y_2351_;
v___y_2321_ = v___y_2310_;
goto v___jp_2312_;
}
}
}
}
v___jp_2376_:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_Syntax_getTailPos_x3f(v___y_2380_, v___y_2382_);
lean_dec(v___y_2380_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_inc(v___y_2383_);
v___y_2350_ = v___y_2377_;
v___y_2351_ = v___y_2379_;
v___y_2352_ = v___y_2383_;
v___y_2353_ = v___y_2378_;
v___y_2354_ = v___y_2381_;
v___y_2355_ = v___y_2379_;
v___y_2356_ = v___y_2382_;
v___y_2357_ = v___y_2383_;
goto v___jp_2349_;
}
else
{
lean_object* v_val_2385_; 
v_val_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_val_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___y_2350_ = v___y_2377_;
v___y_2351_ = v___y_2379_;
v___y_2352_ = v___y_2383_;
v___y_2353_ = v___y_2378_;
v___y_2354_ = v___y_2381_;
v___y_2355_ = v___y_2379_;
v___y_2356_ = v___y_2382_;
v___y_2357_ = v_val_2385_;
goto v___jp_2349_;
}
}
v___jp_2386_:
{
lean_object* v_toCold_2389_; lean_object* v_ref_2390_; uint8_t v_suppressElabErrors_2391_; lean_object* v___x_2392_; lean_object* v___f_2393_; lean_object* v_ref_2394_; lean_object* v___x_2395_; 
v_toCold_2389_ = lean_ctor_get(v___y_2309_, 0);
v_ref_2390_ = lean_ctor_get(v___y_2309_, 2);
v_suppressElabErrors_2391_ = lean_ctor_get_uint8(v___y_2309_, sizeof(void*)*3 + 2);
v___x_2392_ = lean_box(v_suppressElabErrors_2391_);
v___f_2393_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2393_, 0, v___x_2392_);
v_ref_2394_ = l_Lean_replaceRef(v_ref_2303_, v_ref_2390_);
v___x_2395_ = l_Lean_Syntax_getPos_x3f(v_ref_2394_, v___y_2387_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_unsigned_to_nat(0u);
v___y_2377_ = v___f_2393_;
v___y_2378_ = v_suppressElabErrors_2391_;
v___y_2379_ = v_toCold_2389_;
v___y_2380_ = v_ref_2394_;
v___y_2381_ = v___y_2388_;
v___y_2382_ = v___y_2387_;
v___y_2383_ = v___x_2396_;
goto v___jp_2376_;
}
else
{
lean_object* v_val_2397_; 
v_val_2397_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_val_2397_);
lean_dec_ref_known(v___x_2395_, 1);
v___y_2377_ = v___f_2393_;
v___y_2378_ = v_suppressElabErrors_2391_;
v___y_2379_ = v_toCold_2389_;
v___y_2380_ = v_ref_2394_;
v___y_2381_ = v___y_2388_;
v___y_2382_ = v___y_2387_;
v___y_2383_ = v_val_2397_;
goto v___jp_2376_;
}
}
v___jp_2399_:
{
uint8_t v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = 1;
v___x_2402_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2305_, v___x_2401_);
if (v___x_2402_ == 0)
{
v___y_2387_ = v___y_2400_;
v___y_2388_ = v_severity_2305_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2403_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2309_);
v___x_2404_ = l_Lean_warningAsError;
v___x_2405_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_2403_, v___x_2404_);
lean_dec_ref(v___x_2403_);
if (v___x_2405_ == 0)
{
v___y_2387_ = v___y_2400_;
v___y_2388_ = v_severity_2305_;
goto v___jp_2386_;
}
else
{
v___y_2387_ = v___y_2400_;
v___y_2388_ = v___x_2398_;
goto v___jp_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2410_, lean_object* v_msgData_2411_, lean_object* v_severity_2412_, lean_object* v_isSilent_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v_severity_boxed_2419_; uint8_t v_isSilent_boxed_2420_; lean_object* v_res_2421_; 
v_severity_boxed_2419_ = lean_unbox(v_severity_2412_);
v_isSilent_boxed_2420_ = lean_unbox(v_isSilent_2413_);
v_res_2421_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2410_, v_msgData_2411_, v_severity_boxed_2419_, v_isSilent_boxed_2420_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v_ref_2410_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object* v_msgData_2422_, uint8_t v_severity_2423_, uint8_t v_isSilent_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_ref_2432_; lean_object* v___x_2433_; 
v_ref_2432_ = lean_ctor_get(v___y_2429_, 2);
v___x_2433_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2432_, v_msgData_2422_, v_severity_2423_, v_isSilent_2424_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2434_, lean_object* v_severity_2435_, lean_object* v_isSilent_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v_severity_boxed_2444_; uint8_t v_isSilent_boxed_2445_; lean_object* v_res_2446_; 
v_severity_boxed_2444_ = lean_unbox(v_severity_2435_);
v_isSilent_boxed_2445_ = lean_unbox(v_isSilent_2436_);
v_res_2446_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2434_, v_severity_boxed_2444_, v_isSilent_boxed_2445_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object* v_msgData_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = 2;
v___x_2456_ = 0;
v___x_2457_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2447_, v___x_2455_, v___x_2456_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(lean_object* v_msgData_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object* v_ref_2467_, lean_object* v_msgData_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
uint8_t v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = 2;
v___x_2477_ = 0;
v___x_2478_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2467_, v_msgData_2468_, v___x_2476_, v___x_2477_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object* v_ref_2479_, lean_object* v_msgData_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2479_, v_msgData_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v_ref_2479_);
return v_res_2488_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0));
v___x_2491_ = l_Lean_stringToMessageData(v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object* v_ex_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
if (lean_obj_tag(v_ex_2492_) == 0)
{
lean_object* v_ref_2503_; lean_object* v_msg_2504_; lean_object* v___x_2505_; 
v_ref_2503_ = lean_ctor_get(v_ex_2492_, 0);
lean_inc(v_ref_2503_);
v_msg_2504_ = lean_ctor_get(v_ex_2492_, 1);
lean_inc_ref(v_msg_2504_);
lean_dec_ref_known(v_ex_2492_, 2);
v___x_2505_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2503_, v_msg_2504_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v_ref_2503_);
return v___x_2505_;
}
else
{
lean_object* v_id_2506_; uint8_t v___x_2507_; 
v_id_2506_ = lean_ctor_get(v_ex_2492_, 0);
lean_inc(v_id_2506_);
v___x_2507_ = l_Lean_Elab_isAbortExceptionId(v_id_2506_);
if (v___x_2507_ == 0)
{
uint8_t v___x_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2533_; 
v___x_2508_ = l_Lean_Exception_isInterrupt(v_ex_2492_);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_ex_2492_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; lean_object* v_unused_2535_; 
v_unused_2534_ = lean_ctor_get(v_ex_2492_, 1);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_ex_2492_, 0);
lean_dec(v_unused_2535_);
v___x_2510_ = v_ex_2492_;
v_isShared_2511_ = v_isSharedCheck_2533_;
goto v_resetjp_2509_;
}
else
{
lean_dec(v_ex_2492_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2533_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
if (v___x_2508_ == 0)
{
lean_object* v_ref_2512_; lean_object* v___x_2513_; 
v_ref_2512_ = lean_ctor_get(v___y_2497_, 2);
v___x_2513_ = l_Lean_InternalExceptionId_getName(v_id_2506_);
lean_dec(v_id_2506_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_del_object(v___x_2510_);
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
v___x_2516_ = l_Lean_MessageData_ofName(v_a_2514_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_2517_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2518_;
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2532_; 
v_a_2519_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2521_ = v___x_2513_;
v_isShared_2522_ = v_isSharedCheck_2532_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2513_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2532_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2523_ = lean_io_error_to_string(v_a_2519_);
v___x_2524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
v___x_2525_ = l_Lean_MessageData_ofFormat(v___x_2524_);
lean_inc(v_ref_2512_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set_tag(v___x_2510_, 0);
lean_ctor_set(v___x_2510_, 1, v___x_2525_);
lean_ctor_set(v___x_2510_, 0, v_ref_2512_);
v___x_2527_ = v___x_2510_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_ref_2512_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2529_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2527_);
v___x_2529_ = v___x_2521_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
else
{
lean_del_object(v___x_2510_);
lean_dec(v_id_2506_);
goto v___jp_2500_;
}
}
}
else
{
lean_dec(v_id_2506_);
lean_dec_ref_known(v_ex_2492_, 2);
goto v___jp_2500_;
}
}
v___jp_2500_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_box(0);
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
return v___x_2502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object* v_ex_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object* v_a_2545_, lean_object* v_config_2546_, lean_object* v_____r_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_2545_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2564_);
v___x_2557_ = v___x_2555_;
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
else
{
lean_dec(v___x_2555_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_config_2546_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_config_2546_);
v_a_2565_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2555_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2555_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object* v_a_2573_, lean_object* v_config_2574_, lean_object* v_____r_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2573_, v_config_2574_, v_____r_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object* v___f_2584_, lean_object* v_x_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_box(0);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc_ref(v___y_2586_);
v___x_2594_ = lean_apply_8(v___f_2584_, v___x_2593_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(lean_object* v___f_2595_, lean_object* v_x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2595_, v_x_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_x_2596_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object* v_eval_2605_, lean_object* v_config_2606_, lean_object* v_item_2607_, uint8_t v_logExceptions_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___y_2617_; lean_object* v___x_2635_; 
lean_inc(v_a_2614_);
lean_inc_ref(v_a_2613_);
lean_inc(v_a_2612_);
lean_inc_ref(v_a_2611_);
lean_inc(v_a_2610_);
lean_inc_ref(v_a_2609_);
lean_inc(v_config_2606_);
v___x_2635_ = lean_apply_9(v_eval_2605_, v_config_2606_, v_item_2607_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, lean_box(0));
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_dec(v_config_2606_);
return v___x_2635_;
}
else
{
lean_object* v_a_2636_; uint8_t v___x_2637_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
v___x_2637_ = l_Lean_Exception_isInterrupt(v_a_2636_);
if (v___x_2637_ == 0)
{
uint8_t v___x_2638_; 
lean_inc(v_a_2636_);
v___x_2638_ = l_Lean_Exception_isRuntime(v_a_2636_);
if (v___x_2638_ == 0)
{
if (v_logExceptions_2608_ == 0)
{
lean_dec(v_a_2636_);
lean_dec(v_config_2606_);
return v___x_2635_;
}
else
{
lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2654_; 
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2655_);
v___x_2640_ = v___x_2635_;
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
else
{
lean_dec(v___x_2635_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___f_2642_; 
lean_inc(v_config_2606_);
lean_inc(v_a_2636_);
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2642_, 0, v_a_2636_);
lean_closure_set(v___f_2642_, 1, v_config_2606_);
if (lean_obj_tag(v_a_2636_) == 1)
{
lean_object* v_extra_2643_; 
v_extra_2643_ = lean_ctor_get(v_a_2636_, 1);
if (lean_obj_tag(v_extra_2643_) == 0)
{
lean_object* v_id_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
lean_dec_ref(v___f_2642_);
v_id_2644_ = lean_ctor_get(v_a_2636_, 0);
v___x_2645_ = l_Lean_Elab_abortTermExceptionId;
v___x_2646_ = l_Lean_instBEqInternalExceptionId_beq(v_id_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_del_object(v___x_2640_);
v___x_2647_ = lean_box(0);
v___x_2648_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2636_, v_config_2606_, v___x_2647_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
v___y_2617_ = v___x_2648_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2650_; 
lean_dec_ref_known(v_a_2636_, 2);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 0);
lean_ctor_set(v___x_2640_, 0, v_config_2606_);
v___x_2650_ = v___x_2640_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_config_2606_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
else
{
lean_object* v___x_2652_; 
lean_del_object(v___x_2640_);
lean_dec(v_config_2606_);
v___x_2652_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2642_, v_a_2636_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
lean_dec_ref_known(v_a_2636_, 2);
v___y_2617_ = v___x_2652_;
goto v___jp_2616_;
}
}
else
{
lean_object* v___x_2653_; 
lean_del_object(v___x_2640_);
lean_dec(v_config_2606_);
v___x_2653_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2642_, v_a_2636_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
lean_dec(v_a_2636_);
v___y_2617_ = v___x_2653_;
goto v___jp_2616_;
}
}
}
}
else
{
lean_dec(v_a_2636_);
lean_dec(v_config_2606_);
return v___x_2635_;
}
}
else
{
lean_dec(v_a_2636_);
lean_dec(v_config_2606_);
return v___x_2635_;
}
}
v___jp_2616_:
{
if (lean_obj_tag(v___y_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2626_; 
v_a_2618_ = lean_ctor_get(v___y_2617_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___y_2617_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2620_ = v___y_2617_;
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___y_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v_a_2622_; lean_object* v___x_2624_; 
v_a_2622_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_a_2622_);
lean_dec(v_a_2618_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v_a_2622_);
v___x_2624_ = v___x_2620_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
v_a_2627_ = lean_ctor_get(v___y_2617_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___y_2617_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___y_2617_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___y_2617_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object* v_eval_2656_, lean_object* v_config_2657_, lean_object* v_item_2658_, lean_object* v_logExceptions_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
uint8_t v_logExceptions_boxed_2667_; lean_object* v_res_2668_; 
v_logExceptions_boxed_2667_ = lean_unbox(v_logExceptions_2659_);
v_res_2668_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2656_, v_config_2657_, v_item_2658_, v_logExceptions_boxed_2667_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object* v_00_u03b1_2669_, lean_object* v_eval_2670_, lean_object* v_config_2671_, lean_object* v_item_2672_, uint8_t v_logExceptions_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2670_, v_config_2671_, v_item_2672_, v_logExceptions_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object* v_00_u03b1_2682_, lean_object* v_eval_2683_, lean_object* v_config_2684_, lean_object* v_item_2685_, lean_object* v_logExceptions_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
uint8_t v_logExceptions_boxed_2694_; lean_object* v_res_2695_; 
v_logExceptions_boxed_2694_ = lean_unbox(v_logExceptions_2686_);
v_res_2695_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(v_00_u03b1_2682_, v_eval_2683_, v_config_2684_, v_item_2685_, v_logExceptions_boxed_2694_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object* v_ref_2696_, lean_object* v_msgData_2697_, uint8_t v_severity_2698_, uint8_t v_isSilent_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2696_, v_msgData_2697_, v_severity_2698_, v_isSilent_2699_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2708_, lean_object* v_msgData_2709_, lean_object* v_severity_2710_, lean_object* v_isSilent_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v_severity_boxed_2719_; uint8_t v_isSilent_boxed_2720_; lean_object* v_res_2721_; 
v_severity_boxed_2719_ = lean_unbox(v_severity_2710_);
v_isSilent_boxed_2720_ = lean_unbox(v_isSilent_2711_);
v_res_2721_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2708_, v_msgData_2709_, v_severity_boxed_2719_, v_isSilent_boxed_2720_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v_ref_2708_);
return v_res_2721_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_box(0);
v___x_2723_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v___x_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg(){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object* v_00_u03b1_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object* v_00_u03b1_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2747_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_unsigned_to_nat(1u);
v___x_2752_ = l_Lean_Level_ofNat(v___x_2751_);
return v___x_2752_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2);
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v___x_2753_);
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3);
v___x_2757_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1));
v___x_2758_ = l_Lean_Expr_const___override(v___x_2757_, v___x_2756_);
return v___x_2758_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6));
v___x_2764_ = l_Lean_Expr_const___override(v___x_2763_, v___x_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object* v_cfg_2768_, lean_object* v_cfgItem_2769_, lean_object* v_cfgType_x3f_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; 
if (lean_obj_tag(v_cfgType_x3f_2770_) == 1)
{
lean_object* v_val_2788_; lean_object* v___x_2789_; lean_object* v_infoState_2790_; uint8_t v_enabled_2791_; 
v_val_2788_ = lean_ctor_get(v_cfgType_x3f_2770_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v_cfgType_x3f_2770_, 1);
v___x_2789_ = lean_st_ref_get(v_a_2776_);
v_infoState_2790_ = lean_ctor_get(v___x_2789_, 8);
lean_inc_ref(v_infoState_2790_);
lean_dec(v___x_2789_);
v_enabled_2791_ = lean_ctor_get_uint8(v_infoState_2790_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2790_);
if (v_enabled_2791_ == 0)
{
lean_dec(v_val_2788_);
v___y_2779_ = v_a_2771_;
v___y_2780_ = v_a_2772_;
v___y_2781_ = v_a_2773_;
v___y_2782_ = v_a_2774_;
v___y_2783_ = v_a_2775_;
v___y_2784_ = v_a_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = l_Lean_Syntax_getArg(v_cfgItem_2769_, v___x_2792_);
v___x_2794_ = l_Lean_Syntax_isAtom(v___x_2793_);
if (v___x_2794_ == 0)
{
lean_dec(v___x_2793_);
lean_dec(v_val_2788_);
v___y_2779_ = v_a_2771_;
v___y_2780_ = v_a_2772_;
v___y_2781_ = v_a_2773_;
v___y_2782_ = v_a_2774_;
v___y_2783_ = v_a_2775_;
v___y_2784_ = v_a_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = l_Lean_Syntax_getArg(v_cfgItem_2769_, v___x_2795_);
v___x_2797_ = l_Lean_Syntax_isMissing(v___x_2796_);
lean_dec(v___x_2796_);
if (v___x_2797_ == 0)
{
lean_dec(v___x_2793_);
lean_dec(v_val_2788_);
v___y_2779_ = v_a_2771_;
v___y_2780_ = v_a_2772_;
v___y_2781_ = v_a_2773_;
v___y_2782_ = v_a_2774_;
v___y_2783_ = v_a_2775_;
v___y_2784_ = v_a_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2798_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
v___x_2799_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
v___x_2800_ = l_Lean_mkAppB(v___x_2798_, v_val_2788_, v___x_2799_);
v___x_2801_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9));
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v___x_2793_);
v___x_2803_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2804_ = lean_box(0);
v___x_2805_ = 0;
v___x_2806_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2806_, 0, v___x_2802_);
lean_ctor_set(v___x_2806_, 1, v___x_2803_);
lean_ctor_set(v___x_2806_, 2, v___x_2804_);
lean_ctor_set(v___x_2806_, 3, v___x_2800_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*4, v___x_2805_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*4 + 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v___x_2804_);
v___x_2808_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2807_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec_ref(v___x_2808_);
v___y_2779_ = v_a_2771_;
v___y_2780_ = v_a_2772_;
v___y_2781_ = v_a_2773_;
v___y_2782_ = v_a_2774_;
v___y_2783_ = v_a_2775_;
v___y_2784_ = v_a_2776_;
goto v___jp_2778_;
}
}
}
}
else
{
lean_dec(v_cfgType_x3f_2770_);
v___y_2779_ = v_a_2771_;
v___y_2780_ = v_a_2772_;
v___y_2781_ = v_a_2773_;
v___y_2782_ = v_a_2774_;
v___y_2783_ = v_a_2775_;
v___y_2784_ = v_a_2776_;
goto v___jp_2778_;
}
v___jp_2778_:
{
uint8_t v___x_2785_; 
v___x_2785_ = l_Lean_Syntax_hasMissing(v_cfgItem_2769_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; 
lean_dec(v_cfg_2768_);
v___x_2786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_cfg_2768_);
return v___x_2787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object* v_cfg_2809_, lean_object* v_cfgItem_2810_, lean_object* v_cfgType_x3f_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2809_, v_cfgItem_2810_, v_cfgType_x3f_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_cfgItem_2810_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object* v_00_u03b1_2820_, lean_object* v_cfg_2821_, lean_object* v_cfgItem_2822_, lean_object* v_cfgType_x3f_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2821_, v_cfgItem_2822_, v_cfgType_x3f_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object* v_00_u03b1_2832_, lean_object* v_cfg_2833_, lean_object* v_cfgItem_2834_, lean_object* v_cfgType_x3f_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(v_00_u03b1_2832_, v_cfg_2833_, v_cfgItem_2834_, v_cfgType_x3f_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_cfgItem_2834_);
return v_res_2843_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_s_2844_, lean_object* v_a_2845_, uint8_t v_b_2846_){
_start:
{
lean_object* v_str_2847_; lean_object* v_startInclusive_2848_; lean_object* v_endExclusive_2849_; lean_object* v___x_2850_; uint8_t v_decide_2851_; 
v_str_2847_ = lean_ctor_get(v_s_2844_, 0);
v_startInclusive_2848_ = lean_ctor_get(v_s_2844_, 1);
v_endExclusive_2849_ = lean_ctor_get(v_s_2844_, 2);
v___x_2850_ = lean_nat_sub(v_endExclusive_2849_, v_startInclusive_2848_);
v_decide_2851_ = lean_nat_dec_eq(v_a_2845_, v___x_2850_);
lean_dec(v___x_2850_);
if (v_decide_2851_ == 0)
{
lean_object* v___x_2852_; uint32_t v___x_2853_; uint32_t v___x_2854_; uint8_t v___x_2855_; 
v___x_2852_ = lean_nat_add(v_startInclusive_2848_, v_a_2845_);
lean_dec(v_a_2845_);
v___x_2853_ = lean_string_utf8_get_fast(v_str_2847_, v___x_2852_);
v___x_2854_ = 46;
v___x_2855_ = lean_uint32_dec_eq(v___x_2853_, v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_string_utf8_next_fast(v_str_2847_, v___x_2852_);
lean_dec(v___x_2852_);
v___x_2857_ = lean_nat_sub(v___x_2856_, v_startInclusive_2848_);
v_a_2845_ = v___x_2857_;
v_b_2846_ = v___x_2855_;
goto _start;
}
else
{
lean_dec(v___x_2852_);
return v___x_2855_;
}
}
else
{
lean_dec(v_a_2845_);
return v_b_2846_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_s_2859_, lean_object* v_a_2860_, lean_object* v_b_2861_){
_start:
{
uint8_t v_b_boxed_2862_; uint8_t v_res_2863_; lean_object* v_r_2864_; 
v_b_boxed_2862_ = lean_unbox(v_b_2861_);
v_res_2863_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2859_, v_a_2860_, v_b_boxed_2862_);
lean_dec_ref(v_s_2859_);
v_r_2864_ = lean_box(v_res_2863_);
return v_r_2864_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object* v_s_2865_){
_start:
{
lean_object* v_searcher_2866_; uint8_t v___x_2867_; uint8_t v___x_2868_; 
v_searcher_2866_ = lean_unsigned_to_nat(0u);
v___x_2867_ = 0;
v___x_2868_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2865_, v_searcher_2866_, v___x_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object* v_s_2869_){
_start:
{
uint8_t v_res_2870_; lean_object* v_r_2871_; 
v_res_2870_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2869_);
lean_dec_ref(v_s_2869_);
v_r_2871_ = lean_box(v_res_2870_);
return v_r_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object* v_si_2872_, lean_object* v_val_2873_){
_start:
{
lean_object* v___y_2875_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2881_ = lean_unsigned_to_nat(0u);
v___x_2882_ = lean_string_utf8_byte_size(v_val_2873_);
lean_inc_ref(v_val_2873_);
v___x_2883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2883_, 0, v_val_2873_);
lean_ctor_set(v___x_2883_, 1, v___x_2881_);
lean_ctor_set(v___x_2883_, 2, v___x_2882_);
v___x_2884_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_2883_);
lean_dec_ref_known(v___x_2883_, 3);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_box(0);
lean_inc_ref(v_val_2873_);
v___x_2886_ = l_Lean_Name_str___override(v___x_2885_, v_val_2873_);
v___y_2875_ = v___x_2886_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2887_; 
lean_inc_ref(v_val_2873_);
v___x_2887_ = l_String_toName(v_val_2873_);
v___y_2875_ = v___x_2887_;
goto v___jp_2874_;
}
v___jp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2876_ = lean_unsigned_to_nat(0u);
v___x_2877_ = lean_string_utf8_byte_size(v_val_2873_);
v___x_2878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2878_, 0, v_val_2873_);
lean_ctor_set(v___x_2878_, 1, v___x_2876_);
lean_ctor_set(v___x_2878_, 2, v___x_2877_);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2880_, 0, v_si_2872_);
lean_ctor_set(v___x_2880_, 1, v___x_2878_);
lean_ctor_set(v___x_2880_, 2, v___y_2875_);
lean_ctor_set(v___x_2880_, 3, v___x_2879_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object* v_eval_2889_, uint8_t v_logExceptions_2890_, lean_object* v_onErr_2891_, lean_object* v_init_2892_, lean_object* v_cfg_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2893_);
v___x_2924_ = l_Lean_Syntax_isOfKind(v_cfg_2893_, v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2925_ = l_Lean_Syntax_getNumArgs(v_cfg_2893_);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_dec_eq(v___x_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v_atomAsIdent_2928_; uint8_t v___x_2929_; 
v_atomAsIdent_2928_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0));
v___x_2929_ = lean_nat_dec_le(v___x_2926_, v___x_2925_);
if (v___x_2929_ == 0)
{
lean_dec(v___x_2925_);
if (lean_obj_tag(v_cfg_2893_) == 2)
{
lean_object* v_info_2930_; lean_object* v_val_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v_onErr_2891_);
v_info_2930_ = lean_ctor_get(v_cfg_2893_, 0);
v_val_2931_ = lean_ctor_get(v_cfg_2893_, 1);
lean_inc_ref(v_val_2931_);
lean_inc(v_info_2930_);
v___x_2932_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_2930_, v_val_2931_);
v___x_2933_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2934_ = l_Lean_mkCIdentFrom(v_cfg_2893_, v___x_2933_, v___x_2929_);
v___x_2935_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2936_ = l_Lean_TSyntax_getId(v___x_2932_);
v___x_2937_ = l_Lean_Name_eraseMacroScopes(v___x_2936_);
lean_dec(v___x_2936_);
v___x_2938_ = lean_box(0);
lean_inc(v___x_2932_);
v___x_2939_ = l_Lean_Syntax_identComponents(v___x_2932_, v___x_2938_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2941_, 0, v_cfg_2893_);
lean_ctor_set(v___x_2941_, 1, v___x_2932_);
lean_ctor_set(v___x_2941_, 2, v___x_2934_);
lean_ctor_set(v___x_2941_, 3, v___x_2935_);
lean_ctor_set(v___x_2941_, 4, v___x_2937_);
lean_ctor_set(v___x_2941_, 5, v___x_2939_);
lean_ctor_set(v___x_2941_, 6, v___x_2940_);
v___x_2942_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2889_, v_init_2892_, v___x_2941_, v_logExceptions_2890_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2942_;
}
else
{
lean_dec_ref(v_eval_2889_);
goto v___jp_2912_;
}
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = l_Lean_Syntax_getArg(v_cfg_2893_, v___x_2943_);
if (lean_obj_tag(v___x_2944_) == 2)
{
lean_object* v_val_2945_; lean_object* v___y_2947_; uint8_t v_val_2948_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_val_2945_ = lean_ctor_get(v___x_2944_, 1);
v___x_2959_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2960_ = lean_string_dec_eq(v_val_2945_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2962_ = lean_string_dec_eq(v_val_2945_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
lean_inc_ref(v_val_2945_);
lean_dec_ref_known(v___x_2944_, 2);
v___x_2963_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2964_ = lean_string_dec_eq(v_val_2945_, v___x_2963_);
lean_dec_ref(v_val_2945_);
if (v___x_2964_ == 0)
{
lean_dec(v___x_2925_);
lean_dec_ref(v_eval_2889_);
goto v___jp_2912_;
}
else
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = lean_unsigned_to_nat(5u);
v___x_2966_ = lean_nat_dec_le(v___x_2925_, v___x_2965_);
lean_dec(v___x_2925_);
if (v___x_2966_ == 0)
{
lean_dec_ref(v_eval_2889_);
goto v___jp_2912_;
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = l_Lean_Syntax_getArg(v_cfg_2893_, v___x_2926_);
v___x_2968_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2928_, v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 1)
{
lean_object* v_val_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v_onErr_2891_);
v_val_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc_n(v_val_2969_, 2);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = lean_unsigned_to_nat(3u);
v___x_2971_ = l_Lean_Syntax_getArg(v_cfg_2893_, v___x_2970_);
v___x_2972_ = lean_box(0);
v___x_2973_ = l_Lean_TSyntax_getId(v_val_2969_);
v___x_2974_ = l_Lean_Name_eraseMacroScopes(v___x_2973_);
lean_dec(v___x_2973_);
v___x_2975_ = l_Lean_Syntax_identComponents(v_val_2969_, v___x_2972_);
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2977_, 0, v_cfg_2893_);
lean_ctor_set(v___x_2977_, 1, v_val_2969_);
lean_ctor_set(v___x_2977_, 2, v___x_2971_);
lean_ctor_set(v___x_2977_, 3, v___x_2972_);
lean_ctor_set(v___x_2977_, 4, v___x_2974_);
lean_ctor_set(v___x_2977_, 5, v___x_2975_);
lean_ctor_set(v___x_2977_, 6, v___x_2976_);
v___x_2978_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2889_, v_init_2892_, v___x_2977_, v_logExceptions_2890_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2978_;
}
else
{
lean_dec(v___x_2968_);
lean_dec_ref(v_eval_2889_);
goto v___jp_2912_;
}
}
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_box(v___x_2960_);
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
v___y_2947_ = v___x_2980_;
v_val_2948_ = v___x_2960_;
goto v___jp_2946_;
}
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = lean_box(v___x_2929_);
v___x_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
v___y_2947_ = v___x_2982_;
v_val_2948_ = v___x_2929_;
goto v___jp_2946_;
}
v___jp_2946_:
{
lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = lean_unsigned_to_nat(2u);
v___x_2950_ = lean_nat_dec_eq(v___x_2925_, v___x_2949_);
lean_dec(v___x_2925_);
if (v___x_2950_ == 0)
{
lean_dec(v___y_2947_);
lean_dec_ref_known(v___x_2944_, 2);
lean_dec_ref(v_eval_2889_);
goto v___jp_2912_;
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = l_Lean_Syntax_getArg(v_cfg_2893_, v___x_2926_);
v___x_2952_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2928_, v___x_2951_);
if (lean_obj_tag(v___x_2952_) == 1)
{
lean_dec_ref(v_onErr_2891_);
if (v_val_2948_ == 0)
{
lean_object* v_val_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_val_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_val_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2955_ = l_Lean_mkCIdentFrom(v___x_2944_, v___x_2954_, v_val_2948_);
lean_dec_ref_known(v___x_2944_, 2);
v___y_2902_ = v___y_2947_;
v___y_2903_ = v_val_2953_;
v___y_2904_ = v___x_2955_;
goto v___jp_2901_;
}
else
{
lean_object* v_val_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_val_2956_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_val_2956_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2957_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2958_ = l_Lean_mkCIdentFrom(v___x_2944_, v___x_2957_, v___x_2927_);
lean_dec_ref_known(v___x_2944_, 2);
v___y_2902_ = v___y_2947_;
v___y_2903_ = v_val_2956_;
v___y_2904_ = v___x_2958_;
goto v___jp_2901_;
}
}
else
{
lean_dec(v___x_2952_);
lean_dec(v___y_2947_);
lean_dec_ref_known(v___x_2944_, 2);
lean_dec_ref(v_eval_2889_);
goto v___jp_2912_;
}
}
}
}
else
{
lean_dec(v___x_2944_);
lean_dec(v___x_2925_);
lean_dec_ref(v_eval_2889_);
goto v___jp_2912_;
}
}
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec(v___x_2925_);
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = l_Lean_Syntax_getArg(v_cfg_2893_, v___x_2983_);
lean_dec(v_cfg_2893_);
v_cfg_2893_ = v___x_2984_;
goto _start;
}
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = l_Lean_Syntax_getArgs(v_cfg_2893_);
lean_dec(v_cfg_2893_);
v___x_2987_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_2889_, v_logExceptions_2890_, v_onErr_2891_, v_init_2892_, v___x_2986_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec_ref(v___x_2986_);
return v___x_2987_;
}
v___jp_2901_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2905_ = l_Lean_TSyntax_getId(v___y_2903_);
v___x_2906_ = l_Lean_Name_eraseMacroScopes(v___x_2905_);
lean_dec(v___x_2905_);
v___x_2907_ = lean_box(0);
lean_inc(v___y_2903_);
v___x_2908_ = l_Lean_Syntax_identComponents(v___y_2903_, v___x_2907_);
v___x_2909_ = lean_box(0);
v___x_2910_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2910_, 0, v_cfg_2893_);
lean_ctor_set(v___x_2910_, 1, v___y_2903_);
lean_ctor_set(v___x_2910_, 2, v___y_2904_);
lean_ctor_set(v___x_2910_, 3, v___y_2902_);
lean_ctor_set(v___x_2910_, 4, v___x_2906_);
lean_ctor_set(v___x_2910_, 5, v___x_2908_);
lean_ctor_set(v___x_2910_, 6, v___x_2909_);
v___x_2911_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2889_, v_init_2892_, v___x_2910_, v_logExceptions_2890_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2911_;
}
v___jp_2912_:
{
lean_object* v_toCold_2913_; lean_object* v_currRecDepth_2914_; lean_object* v_ref_2915_; uint16_t v_optionFlags_2916_; uint8_t v_suppressElabErrors_2917_; uint8_t v_checkDeprecated_2918_; uint8_t v_isRecordingDeps_2919_; lean_object* v_ref_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_toCold_2913_ = lean_ctor_get(v___y_2898_, 0);
v_currRecDepth_2914_ = lean_ctor_get(v___y_2898_, 1);
v_ref_2915_ = lean_ctor_get(v___y_2898_, 2);
v_optionFlags_2916_ = lean_ctor_get_uint16(v___y_2898_, sizeof(void*)*3);
v_suppressElabErrors_2917_ = lean_ctor_get_uint8(v___y_2898_, sizeof(void*)*3 + 2);
v_checkDeprecated_2918_ = lean_ctor_get_uint8(v___y_2898_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2919_ = lean_ctor_get_uint8(v___y_2898_, sizeof(void*)*3 + 4);
v_ref_2920_ = l_Lean_replaceRef(v_cfg_2893_, v_ref_2915_);
lean_inc(v_currRecDepth_2914_);
lean_inc_ref(v_toCold_2913_);
v___x_2921_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2921_, 0, v_toCold_2913_);
lean_ctor_set(v___x_2921_, 1, v_currRecDepth_2914_);
lean_ctor_set(v___x_2921_, 2, v_ref_2920_);
lean_ctor_set_uint16(v___x_2921_, sizeof(void*)*3, v_optionFlags_2916_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3 + 2, v_suppressElabErrors_2917_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3 + 3, v_checkDeprecated_2918_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3 + 4, v_isRecordingDeps_2919_);
lean_inc(v___y_2899_);
lean_inc(v___y_2897_);
lean_inc_ref(v___y_2896_);
lean_inc(v___y_2895_);
lean_inc_ref(v___y_2894_);
v___x_2922_ = lean_apply_9(v_onErr_2891_, v_init_2892_, v_cfg_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___x_2921_, v___y_2899_, lean_box(0));
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object* v_eval_2988_, uint8_t v_logExceptions_2989_, lean_object* v_onErr_2990_, lean_object* v_as_2991_, size_t v_i_2992_, size_t v_stop_2993_, lean_object* v_b_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_usize_dec_eq(v_i_2992_, v_stop_2993_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_array_uget_borrowed(v_as_2991_, v_i_2992_);
lean_inc(v___x_3003_);
lean_inc_ref(v_onErr_2990_);
lean_inc_ref(v_eval_2988_);
v___x_3004_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_2988_, v_logExceptions_2989_, v_onErr_2990_, v_b_2994_, v___x_3003_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; size_t v___x_3006_; size_t v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = ((size_t)1ULL);
v___x_3007_ = lean_usize_add(v_i_2992_, v___x_3006_);
v_i_2992_ = v___x_3007_;
v_b_2994_ = v_a_3005_;
goto _start;
}
else
{
lean_dec_ref(v_onErr_2990_);
lean_dec_ref(v_eval_2988_);
return v___x_3004_;
}
}
else
{
lean_object* v___x_3009_; 
lean_dec_ref(v_onErr_2990_);
lean_dec_ref(v_eval_2988_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_b_2994_);
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object* v_eval_3010_, uint8_t v_logExceptions_3011_, lean_object* v_onErr_3012_, lean_object* v_init_3013_, lean_object* v_cfgs_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = lean_array_get_size(v_cfgs_3014_);
v___x_3024_ = lean_nat_dec_lt(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; 
lean_dec_ref(v_onErr_3012_);
lean_dec_ref(v_eval_3010_);
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_init_3013_);
return v___x_3025_;
}
else
{
size_t v___x_3026_; size_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = lean_usize_of_nat(v___x_3023_);
v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3010_, v_logExceptions_3011_, v_onErr_3012_, v_cfgs_3014_, v___x_3026_, v___x_3027_, v_init_3013_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
return v___x_3028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object* v_eval_3029_, lean_object* v_logExceptions_3030_, lean_object* v_onErr_3031_, lean_object* v_init_3032_, lean_object* v_cfgs_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
uint8_t v_logExceptions_boxed_3041_; lean_object* v_res_3042_; 
v_logExceptions_boxed_3041_ = lean_unbox(v_logExceptions_3030_);
v_res_3042_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3029_, v_logExceptions_boxed_3041_, v_onErr_3031_, v_init_3032_, v_cfgs_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v_cfgs_3033_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_eval_3043_, lean_object* v_logExceptions_3044_, lean_object* v_onErr_3045_, lean_object* v_as_3046_, lean_object* v_i_3047_, lean_object* v_stop_3048_, lean_object* v_b_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v_logExceptions_boxed_3057_; size_t v_i_boxed_3058_; size_t v_stop_boxed_3059_; lean_object* v_res_3060_; 
v_logExceptions_boxed_3057_ = lean_unbox(v_logExceptions_3044_);
v_i_boxed_3058_ = lean_unbox_usize(v_i_3047_);
lean_dec(v_i_3047_);
v_stop_boxed_3059_ = lean_unbox_usize(v_stop_3048_);
lean_dec(v_stop_3048_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3043_, v_logExceptions_boxed_3057_, v_onErr_3045_, v_as_3046_, v_i_boxed_3058_, v_stop_boxed_3059_, v_b_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v_as_3046_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object* v_eval_3061_, lean_object* v_logExceptions_3062_, lean_object* v_onErr_3063_, lean_object* v_init_3064_, lean_object* v_cfg_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
uint8_t v_logExceptions_boxed_3073_; lean_object* v_res_3074_; 
v_logExceptions_boxed_3073_ = lean_unbox(v_logExceptions_3062_);
v_res_3074_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3061_, v_logExceptions_boxed_3073_, v_onErr_3063_, v_init_3064_, v_cfg_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object* v_eval_3075_, lean_object* v_init_3076_, lean_object* v_cfg_3077_, lean_object* v_onErr_3078_, uint8_t v_logExceptions_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3075_, v_logExceptions_3079_, v_onErr_3078_, v_init_3076_, v_cfg_3077_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object* v_eval_3088_, lean_object* v_init_3089_, lean_object* v_cfg_3090_, lean_object* v_onErr_3091_, lean_object* v_logExceptions_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
uint8_t v_logExceptions_boxed_3100_; lean_object* v_res_3101_; 
v_logExceptions_boxed_3100_ = lean_unbox(v_logExceptions_3092_);
v_res_3101_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3088_, v_init_3089_, v_cfg_3090_, v_onErr_3091_, v_logExceptions_boxed_3100_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object* v_00_u03b1_3102_, lean_object* v_eval_3103_, lean_object* v_init_3104_, lean_object* v_cfg_3105_, lean_object* v_onErr_3106_, uint8_t v_logExceptions_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3103_, v_logExceptions_3107_, v_onErr_3106_, v_init_3104_, v_cfg_3105_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_eval_3117_, lean_object* v_init_3118_, lean_object* v_cfg_3119_, lean_object* v_onErr_3120_, lean_object* v_logExceptions_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
uint8_t v_logExceptions_boxed_3129_; lean_object* v_res_3130_; 
v_logExceptions_boxed_3129_ = lean_unbox(v_logExceptions_3121_);
v_res_3130_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(v_00_u03b1_3116_, v_eval_3117_, v_init_3118_, v_cfg_3119_, v_onErr_3120_, v_logExceptions_boxed_3129_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object* v_00_u03b1_3131_, lean_object* v_eval_3132_, uint8_t v_logExceptions_3133_, lean_object* v_onErr_3134_, lean_object* v_init_3135_, lean_object* v_cfg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3132_, v_logExceptions_3133_, v_onErr_3134_, v_init_3135_, v_cfg_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(lean_object* v_00_u03b1_3145_, lean_object* v_eval_3146_, lean_object* v_logExceptions_3147_, lean_object* v_onErr_3148_, lean_object* v_init_3149_, lean_object* v_cfg_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
uint8_t v_logExceptions_boxed_3158_; lean_object* v_res_3159_; 
v_logExceptions_boxed_3158_ = lean_unbox(v_logExceptions_3147_);
v_res_3159_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_3145_, v_eval_3146_, v_logExceptions_boxed_3158_, v_onErr_3148_, v_init_3149_, v_cfg_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object* v_00_u03b1_3160_, lean_object* v_eval_3161_, uint8_t v_logExceptions_3162_, lean_object* v_onErr_3163_, lean_object* v_init_3164_, lean_object* v_cfgs_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3161_, v_logExceptions_3162_, v_onErr_3163_, v_init_3164_, v_cfgs_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3174_, lean_object* v_eval_3175_, lean_object* v_logExceptions_3176_, lean_object* v_onErr_3177_, lean_object* v_init_3178_, lean_object* v_cfgs_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
uint8_t v_logExceptions_boxed_3187_; lean_object* v_res_3188_; 
v_logExceptions_boxed_3187_ = lean_unbox(v_logExceptions_3176_);
v_res_3188_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_3174_, v_eval_3175_, v_logExceptions_boxed_3187_, v_onErr_3177_, v_init_3178_, v_cfgs_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec_ref(v_cfgs_3179_);
return v_res_3188_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object* v_s_3189_, lean_object* v_inst_3190_, lean_object* v_R_3191_, lean_object* v_a_3192_, uint8_t v_b_3193_, lean_object* v_c_3194_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_3189_, v_a_3192_, v_b_3193_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_s_3196_, lean_object* v_inst_3197_, lean_object* v_R_3198_, lean_object* v_a_3199_, lean_object* v_b_3200_, lean_object* v_c_3201_){
_start:
{
uint8_t v_b_boxed_3202_; uint8_t v_res_3203_; lean_object* v_r_3204_; 
v_b_boxed_3202_ = lean_unbox(v_b_3200_);
v_res_3203_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3196_, v_inst_3197_, v_R_3198_, v_a_3199_, v_b_boxed_3202_, v_c_3201_);
lean_dec_ref(v_s_3196_);
v_r_3204_ = lean_box(v_res_3203_);
return v_r_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3205_, lean_object* v_eval_3206_, uint8_t v_logExceptions_3207_, lean_object* v_onErr_3208_, lean_object* v_as_3209_, size_t v_i_3210_, size_t v_stop_3211_, lean_object* v_b_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3206_, v_logExceptions_3207_, v_onErr_3208_, v_as_3209_, v_i_3210_, v_stop_3211_, v_b_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3221_, lean_object* v_eval_3222_, lean_object* v_logExceptions_3223_, lean_object* v_onErr_3224_, lean_object* v_as_3225_, lean_object* v_i_3226_, lean_object* v_stop_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
uint8_t v_logExceptions_boxed_3236_; size_t v_i_boxed_3237_; size_t v_stop_boxed_3238_; lean_object* v_res_3239_; 
v_logExceptions_boxed_3236_ = lean_unbox(v_logExceptions_3223_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3226_);
lean_dec(v_i_3226_);
v_stop_boxed_3238_ = lean_unbox_usize(v_stop_3227_);
lean_dec(v_stop_3227_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_3221_, v_eval_3222_, v_logExceptions_boxed_3236_, v_onErr_3224_, v_as_3225_, v_i_boxed_3237_, v_stop_boxed_3238_, v_b_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v_as_3225_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object* v_eval_3240_, lean_object* v_init_3241_, lean_object* v_cfgs_3242_, lean_object* v_onErr_3243_, uint8_t v_logExceptions_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3240_, v_logExceptions_3244_, v_onErr_3243_, v_init_3241_, v_cfgs_3242_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object* v_eval_3253_, lean_object* v_init_3254_, lean_object* v_cfgs_3255_, lean_object* v_onErr_3256_, lean_object* v_logExceptions_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
uint8_t v_logExceptions_boxed_3265_; lean_object* v_res_3266_; 
v_logExceptions_boxed_3265_ = lean_unbox(v_logExceptions_3257_);
v_res_3266_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3253_, v_init_3254_, v_cfgs_3255_, v_onErr_3256_, v_logExceptions_boxed_3265_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec_ref(v_cfgs_3255_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object* v_00_u03b1_3267_, lean_object* v_eval_3268_, lean_object* v_init_3269_, lean_object* v_cfgs_3270_, lean_object* v_onErr_3271_, uint8_t v_logExceptions_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3268_, v_logExceptions_3272_, v_onErr_3271_, v_init_3269_, v_cfgs_3270_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_eval_3282_, lean_object* v_init_3283_, lean_object* v_cfgs_3284_, lean_object* v_onErr_3285_, lean_object* v_logExceptions_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
uint8_t v_logExceptions_boxed_3294_; lean_object* v_res_3295_; 
v_logExceptions_boxed_3294_ = lean_unbox(v_logExceptions_3286_);
v_res_3295_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(v_00_u03b1_3281_, v_eval_3282_, v_init_3283_, v_cfgs_3284_, v_onErr_3285_, v_logExceptions_boxed_3294_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec_ref(v_cfgs_3284_);
return v_res_3295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object* v_x_3296_){
_start:
{
uint8_t v___x_3297_; 
v___x_3297_ = 0;
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object* v_x_3298_){
_start:
{
uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_res_3299_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3298_);
lean_dec(v_x_3298_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(lean_object* v___x_3301_, lean_object* v_ctx_x3f_3302_, size_t v_sz_3303_, size_t v_i_3304_, lean_object* v_bs_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
uint8_t v___x_3313_; 
v___x_3313_ = lean_usize_dec_lt(v_i_3304_, v_sz_3303_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_dec_ref(v_ctx_x3f_3302_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_bs_3305_);
return v___x_3314_;
}
else
{
lean_object* v_assignment_3315_; lean_object* v_v_3316_; lean_object* v___x_3317_; lean_object* v_bs_x27_3318_; lean_object* v_a_3320_; lean_object* v_tree_3325_; lean_object* v___x_3326_; 
v_assignment_3315_ = lean_ctor_get(v___x_3301_, 0);
v_v_3316_ = lean_array_uget(v_bs_3305_, v_i_3304_);
v___x_3317_ = lean_unsigned_to_nat(0u);
v_bs_x27_3318_ = lean_array_uset(v_bs_3305_, v_i_3304_, v___x_3317_);
v_tree_3325_ = l_Lean_Elab_InfoTree_substitute(v_v_3316_, v_assignment_3315_);
lean_inc_ref(v_ctx_x3f_3302_);
lean_inc(v___y_3311_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3309_);
lean_inc_ref(v___y_3308_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
v___x_3326_ = lean_apply_7(v_ctx_x3f_3302_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, lean_box(0));
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
if (lean_obj_tag(v_a_3327_) == 0)
{
v_a_3320_ = v_tree_3325_;
goto v___jp_3319_;
}
else
{
lean_object* v_val_3328_; lean_object* v___x_3329_; 
v_val_3328_ = lean_ctor_get(v_a_3327_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v_a_3327_, 1);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v_val_3328_);
lean_ctor_set(v___x_3329_, 1, v_tree_3325_);
v_a_3320_ = v___x_3329_;
goto v___jp_3319_;
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v_tree_3325_);
lean_dec_ref(v_bs_x27_3318_);
lean_dec_ref(v_ctx_x3f_3302_);
v_a_3330_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3326_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3326_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
v___jp_3319_:
{
size_t v___x_3321_; size_t v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = ((size_t)1ULL);
v___x_3322_ = lean_usize_add(v_i_3304_, v___x_3321_);
v___x_3323_ = lean_array_uset(v_bs_x27_3318_, v_i_3304_, v_a_3320_);
v_i_3304_ = v___x_3322_;
v_bs_3305_ = v___x_3323_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v___x_3338_, lean_object* v_ctx_x3f_3339_, lean_object* v_sz_3340_, lean_object* v_i_3341_, lean_object* v_bs_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
size_t v_sz_boxed_3350_; size_t v_i_boxed_3351_; lean_object* v_res_3352_; 
v_sz_boxed_3350_ = lean_unbox_usize(v_sz_3340_);
lean_dec(v_sz_3340_);
v_i_boxed_3351_ = lean_unbox_usize(v_i_3341_);
lean_dec(v_i_3341_);
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3338_, v_ctx_x3f_3339_, v_sz_boxed_3350_, v_i_boxed_3351_, v_bs_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec_ref(v___x_3338_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(lean_object* v___x_3353_, lean_object* v_ctx_x3f_3354_, lean_object* v_x_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
if (lean_obj_tag(v_x_3355_) == 0)
{
lean_object* v_cs_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3389_; 
v_cs_3363_ = lean_ctor_get(v_x_3355_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_x_3355_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3365_ = v_x_3355_;
v_isShared_3366_ = v_isSharedCheck_3389_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_cs_3363_);
lean_dec(v_x_3355_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3389_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
size_t v_sz_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
v_sz_3367_ = lean_array_size(v_cs_3363_);
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3353_, v_ctx_x3f_3354_, v_sz_3367_, v___x_3368_, v_cs_3363_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3380_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v_a_3370_);
v___x_3375_ = v___x_3365_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3375_);
v___x_3377_ = v___x_3372_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_del_object(v___x_3365_);
v_a_3381_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3369_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3369_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
else
{
lean_object* v_vs_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3416_; 
v_vs_3390_ = lean_ctor_get(v_x_3355_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_x_3355_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3392_ = v_x_3355_;
v_isShared_3393_ = v_isSharedCheck_3416_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_vs_3390_);
lean_dec(v_x_3355_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3416_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
size_t v_sz_3394_; size_t v___x_3395_; lean_object* v___x_3396_; 
v_sz_3394_ = lean_array_size(v_vs_3390_);
v___x_3395_ = ((size_t)0ULL);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3353_, v_ctx_x3f_3354_, v_sz_3394_, v___x_3395_, v_vs_3390_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3407_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3407_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3407_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v_a_3397_);
v___x_3402_ = v___x_3392_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3404_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v___x_3402_);
v___x_3404_ = v___x_3399_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_del_object(v___x_3392_);
v_a_3408_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3396_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3396_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v___x_3417_, lean_object* v_ctx_x3f_3418_, size_t v_sz_3419_, size_t v_i_3420_, lean_object* v_bs_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v___x_3429_; 
v___x_3429_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec_ref(v_ctx_x3f_3418_);
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_bs_3421_);
return v___x_3430_;
}
else
{
lean_object* v_v_3431_; lean_object* v___x_3432_; lean_object* v_bs_x27_3433_; lean_object* v___x_3434_; 
v_v_3431_ = lean_array_uget(v_bs_3421_, v_i_3420_);
v___x_3432_ = lean_unsigned_to_nat(0u);
v_bs_x27_3433_ = lean_array_uset(v_bs_3421_, v_i_3420_, v___x_3432_);
lean_inc_ref(v_ctx_x3f_3418_);
v___x_3434_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3417_, v_ctx_x3f_3418_, v_v_3431_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = ((size_t)1ULL);
v___x_3437_ = lean_usize_add(v_i_3420_, v___x_3436_);
v___x_3438_ = lean_array_uset(v_bs_x27_3433_, v_i_3420_, v_a_3435_);
v_i_3420_ = v___x_3437_;
v_bs_3421_ = v___x_3438_;
goto _start;
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec_ref(v_bs_x27_3433_);
lean_dec_ref(v_ctx_x3f_3418_);
v_a_3440_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3434_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3434_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v___x_3448_, lean_object* v_ctx_x3f_3449_, lean_object* v_sz_3450_, lean_object* v_i_3451_, lean_object* v_bs_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
size_t v_sz_boxed_3460_; size_t v_i_boxed_3461_; lean_object* v_res_3462_; 
v_sz_boxed_3460_ = lean_unbox_usize(v_sz_3450_);
lean_dec(v_sz_3450_);
v_i_boxed_3461_ = lean_unbox_usize(v_i_3451_);
lean_dec(v_i_3451_);
v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3448_, v_ctx_x3f_3449_, v_sz_boxed_3460_, v_i_boxed_3461_, v_bs_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___x_3448_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v___x_3463_, lean_object* v_ctx_x3f_3464_, lean_object* v_x_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3463_, v_ctx_x3f_3464_, v_x_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___x_3463_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object* v___x_3474_, lean_object* v_ctx_x3f_3475_, lean_object* v_t_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_root_3484_; lean_object* v_tail_3485_; lean_object* v_size_3486_; size_t v_shift_3487_; lean_object* v_tailOff_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3524_; 
v_root_3484_ = lean_ctor_get(v_t_3476_, 0);
v_tail_3485_ = lean_ctor_get(v_t_3476_, 1);
v_size_3486_ = lean_ctor_get(v_t_3476_, 2);
v_shift_3487_ = lean_ctor_get_usize(v_t_3476_, 4);
v_tailOff_3488_ = lean_ctor_get(v_t_3476_, 3);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_t_3476_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3490_ = v_t_3476_;
v_isShared_3491_ = v_isSharedCheck_3524_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_tailOff_3488_);
lean_inc(v_size_3486_);
lean_inc(v_tail_3485_);
lean_inc(v_root_3484_);
lean_dec(v_t_3476_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3524_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; 
lean_inc_ref(v_ctx_x3f_3475_);
v___x_3492_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3474_, v_ctx_x3f_3475_, v_root_3484_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; size_t v_sz_3494_; size_t v___x_3495_; lean_object* v___x_3496_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v_sz_3494_ = lean_array_size(v_tail_3485_);
v___x_3495_ = ((size_t)0ULL);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3474_, v_ctx_x3f_3475_, v_sz_3494_, v___x_3495_, v_tail_3485_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3507_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3507_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3507_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 1, v_a_3497_);
lean_ctor_set(v___x_3490_, 0, v_a_3493_);
v___x_3502_ = v___x_3490_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3493_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_a_3497_);
lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_size_3486_);
lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_tailOff_3488_);
lean_ctor_set_usize(v_reuseFailAlloc_3506_, 4, v_shift_3487_);
v___x_3502_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3502_);
v___x_3504_ = v___x_3499_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_a_3493_);
lean_del_object(v___x_3490_);
lean_dec(v_tailOff_3488_);
lean_dec(v_size_3486_);
v_a_3508_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3496_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3496_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_del_object(v___x_3490_);
lean_dec(v_tailOff_3488_);
lean_dec(v_size_3486_);
lean_dec_ref(v_tail_3485_);
lean_dec_ref(v_ctx_x3f_3475_);
v_a_3516_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3492_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3492_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object* v___x_3525_, lean_object* v_ctx_x3f_3526_, lean_object* v_t_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3525_, v_ctx_x3f_3526_, v_t_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___x_3525_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3536_, lean_object* v_ctx_x3f_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v_a_3543_, lean_object* v_a_x3f_3544_){
_start:
{
lean_object* v___x_3546_; lean_object* v_infoState_3547_; lean_object* v_trees_3548_; lean_object* v___x_3549_; 
v___x_3546_ = lean_st_ref_get(v___y_3536_);
v_infoState_3547_ = lean_ctor_get(v___x_3546_, 8);
lean_inc_ref(v_infoState_3547_);
lean_dec(v___x_3546_);
v_trees_3548_ = lean_ctor_get(v_infoState_3547_, 2);
lean_inc_ref(v_trees_3548_);
v___x_3549_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_3547_, v_ctx_x3f_3537_, v_trees_3548_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3536_);
lean_dec_ref(v_infoState_3547_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3589_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3589_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3589_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v_infoState_3555_; lean_object* v_env_3556_; lean_object* v_nextMacroScope_3557_; lean_object* v_ngen_3558_; lean_object* v_auxDeclNGen_3559_; lean_object* v_traceState_3560_; lean_object* v_cache_3561_; lean_object* v_recordedDeps_3562_; lean_object* v_messages_3563_; lean_object* v_snapshotTasks_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3588_; 
v___x_3554_ = lean_st_ref_take(v___y_3536_);
v_infoState_3555_ = lean_ctor_get(v___x_3554_, 8);
v_env_3556_ = lean_ctor_get(v___x_3554_, 0);
v_nextMacroScope_3557_ = lean_ctor_get(v___x_3554_, 1);
v_ngen_3558_ = lean_ctor_get(v___x_3554_, 2);
v_auxDeclNGen_3559_ = lean_ctor_get(v___x_3554_, 3);
v_traceState_3560_ = lean_ctor_get(v___x_3554_, 4);
v_cache_3561_ = lean_ctor_get(v___x_3554_, 5);
v_recordedDeps_3562_ = lean_ctor_get(v___x_3554_, 6);
v_messages_3563_ = lean_ctor_get(v___x_3554_, 7);
v_snapshotTasks_3564_ = lean_ctor_get(v___x_3554_, 9);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3566_ = v___x_3554_;
v_isShared_3567_ = v_isSharedCheck_3588_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_snapshotTasks_3564_);
lean_inc(v_infoState_3555_);
lean_inc(v_messages_3563_);
lean_inc(v_recordedDeps_3562_);
lean_inc(v_cache_3561_);
lean_inc(v_traceState_3560_);
lean_inc(v_auxDeclNGen_3559_);
lean_inc(v_ngen_3558_);
lean_inc(v_nextMacroScope_3557_);
lean_inc(v_env_3556_);
lean_dec(v___x_3554_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3588_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
uint8_t v_enabled_3568_; lean_object* v_assignment_3569_; lean_object* v_lazyAssignment_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3586_; 
v_enabled_3568_ = lean_ctor_get_uint8(v_infoState_3555_, sizeof(void*)*3);
v_assignment_3569_ = lean_ctor_get(v_infoState_3555_, 0);
v_lazyAssignment_3570_ = lean_ctor_get(v_infoState_3555_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_infoState_3555_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v_infoState_3555_, 2);
lean_dec(v_unused_3587_);
v___x_3572_ = v_infoState_3555_;
v_isShared_3573_ = v_isSharedCheck_3586_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_lazyAssignment_3570_);
lean_inc(v_assignment_3569_);
lean_dec(v_infoState_3555_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3586_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3574_ = lean_box(0);
v___x_3575_ = l_Lean_PersistentArray_append___redArg(v_a_3543_, v_a_3550_);
lean_dec(v_a_3550_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 2, v___x_3575_);
v___x_3577_ = v___x_3572_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_assignment_3569_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_lazyAssignment_3570_);
lean_ctor_set(v_reuseFailAlloc_3585_, 2, v___x_3575_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*3, v_enabled_3568_);
v___x_3577_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3579_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 8, v___x_3577_);
v___x_3579_ = v___x_3566_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_env_3556_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_nextMacroScope_3557_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_ngen_3558_);
lean_ctor_set(v_reuseFailAlloc_3584_, 3, v_auxDeclNGen_3559_);
lean_ctor_set(v_reuseFailAlloc_3584_, 4, v_traceState_3560_);
lean_ctor_set(v_reuseFailAlloc_3584_, 5, v_cache_3561_);
lean_ctor_set(v_reuseFailAlloc_3584_, 6, v_recordedDeps_3562_);
lean_ctor_set(v_reuseFailAlloc_3584_, 7, v_messages_3563_);
lean_ctor_set(v_reuseFailAlloc_3584_, 8, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3584_, 9, v_snapshotTasks_3564_);
v___x_3579_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3580_ = lean_st_ref_put(v___y_3536_, v___x_3579_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3574_);
v___x_3582_ = v___x_3552_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3574_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_a_3543_);
v_a_3590_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3549_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3549_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3598_, lean_object* v_ctx_x3f_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v_a_3605_, lean_object* v_a_x3f_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3598_, v_ctx_x3f_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v_a_3605_, v_a_x3f_3606_);
lean_dec(v_a_x3f_3606_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3598_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; lean_object* v_infoState_3612_; lean_object* v_trees_3613_; lean_object* v___x_3614_; lean_object* v_infoState_3615_; lean_object* v_env_3616_; lean_object* v_nextMacroScope_3617_; lean_object* v_ngen_3618_; lean_object* v_auxDeclNGen_3619_; lean_object* v_traceState_3620_; lean_object* v_cache_3621_; lean_object* v_recordedDeps_3622_; lean_object* v_messages_3623_; lean_object* v_snapshotTasks_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3647_; 
v___x_3611_ = lean_st_ref_get(v___y_3609_);
v_infoState_3612_ = lean_ctor_get(v___x_3611_, 8);
lean_inc_ref(v_infoState_3612_);
lean_dec(v___x_3611_);
v_trees_3613_ = lean_ctor_get(v_infoState_3612_, 2);
lean_inc_ref(v_trees_3613_);
lean_dec_ref(v_infoState_3612_);
v___x_3614_ = lean_st_ref_take(v___y_3609_);
v_infoState_3615_ = lean_ctor_get(v___x_3614_, 8);
v_env_3616_ = lean_ctor_get(v___x_3614_, 0);
v_nextMacroScope_3617_ = lean_ctor_get(v___x_3614_, 1);
v_ngen_3618_ = lean_ctor_get(v___x_3614_, 2);
v_auxDeclNGen_3619_ = lean_ctor_get(v___x_3614_, 3);
v_traceState_3620_ = lean_ctor_get(v___x_3614_, 4);
v_cache_3621_ = lean_ctor_get(v___x_3614_, 5);
v_recordedDeps_3622_ = lean_ctor_get(v___x_3614_, 6);
v_messages_3623_ = lean_ctor_get(v___x_3614_, 7);
v_snapshotTasks_3624_ = lean_ctor_get(v___x_3614_, 9);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3626_ = v___x_3614_;
v_isShared_3627_ = v_isSharedCheck_3647_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_snapshotTasks_3624_);
lean_inc(v_infoState_3615_);
lean_inc(v_messages_3623_);
lean_inc(v_recordedDeps_3622_);
lean_inc(v_cache_3621_);
lean_inc(v_traceState_3620_);
lean_inc(v_auxDeclNGen_3619_);
lean_inc(v_ngen_3618_);
lean_inc(v_nextMacroScope_3617_);
lean_inc(v_env_3616_);
lean_dec(v___x_3614_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3647_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
uint8_t v_enabled_3628_; lean_object* v_assignment_3629_; lean_object* v_lazyAssignment_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3645_; 
v_enabled_3628_ = lean_ctor_get_uint8(v_infoState_3615_, sizeof(void*)*3);
v_assignment_3629_ = lean_ctor_get(v_infoState_3615_, 0);
v_lazyAssignment_3630_ = lean_ctor_get(v_infoState_3615_, 1);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_infoState_3615_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; 
v_unused_3646_ = lean_ctor_get(v_infoState_3615_, 2);
lean_dec(v_unused_3646_);
v___x_3632_ = v_infoState_3615_;
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_lazyAssignment_3630_);
lean_inc(v_assignment_3629_);
lean_dec(v_infoState_3615_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3634_ = lean_unsigned_to_nat(32u);
v___x_3635_ = lean_mk_empty_array_with_capacity(v___x_3634_);
lean_dec_ref(v___x_3635_);
v___x_3636_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 2, v___x_3636_);
v___x_3638_ = v___x_3632_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_assignment_3629_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_lazyAssignment_3630_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v___x_3636_);
lean_ctor_set_uint8(v_reuseFailAlloc_3644_, sizeof(void*)*3, v_enabled_3628_);
v___x_3638_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 8, v___x_3638_);
v___x_3640_ = v___x_3626_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_env_3616_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_nextMacroScope_3617_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_ngen_3618_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_auxDeclNGen_3619_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_traceState_3620_);
lean_ctor_set(v_reuseFailAlloc_3643_, 5, v_cache_3621_);
lean_ctor_set(v_reuseFailAlloc_3643_, 6, v_recordedDeps_3622_);
lean_ctor_set(v_reuseFailAlloc_3643_, 7, v_messages_3623_);
lean_ctor_set(v_reuseFailAlloc_3643_, 8, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3643_, 9, v_snapshotTasks_3624_);
v___x_3640_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_st_ref_put(v___y_3609_, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_trees_3613_);
return v___x_3642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3648_);
lean_dec(v___y_3648_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object* v_x_3651_, lean_object* v_ctx_x3f_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; lean_object* v_infoState_3661_; uint8_t v_enabled_3662_; 
v___x_3660_ = lean_st_ref_get(v___y_3658_);
v_infoState_3661_ = lean_ctor_get(v___x_3660_, 8);
lean_inc_ref(v_infoState_3661_);
lean_dec(v___x_3660_);
v_enabled_3662_ = lean_ctor_get_uint8(v_infoState_3661_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3661_);
if (v_enabled_3662_ == 0)
{
lean_object* v___x_3663_; 
lean_dec_ref(v_ctx_x3f_3652_);
lean_inc(v___y_3658_);
lean_inc_ref(v___y_3657_);
lean_inc(v___y_3656_);
lean_inc_ref(v___y_3655_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
v___x_3663_ = lean_apply_7(v_x_3651_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, lean_box(0));
return v___x_3663_;
}
else
{
lean_object* v___x_3664_; lean_object* v_a_3665_; lean_object* v_r_3666_; 
v___x_3664_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3658_);
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___x_3664_);
lean_inc(v___y_3658_);
lean_inc_ref(v___y_3657_);
lean_inc(v___y_3656_);
lean_inc_ref(v___y_3655_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
v_r_3666_ = lean_apply_7(v_x_3651_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, lean_box(0));
if (lean_obj_tag(v_r_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3691_; 
v_a_3667_ = lean_ctor_get(v_r_3666_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_r_3666_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3669_ = v_r_3666_;
v_isShared_3670_ = v_isSharedCheck_3691_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v_r_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3691_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
lean_inc(v_a_3667_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set_tag(v___x_3669_, 1);
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; 
v___x_3673_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3658_, v_ctx_x3f_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v_a_3665_, v___x_3672_);
lean_dec_ref(v___x_3672_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; 
v_unused_3681_ = lean_ctor_get(v___x_3673_, 0);
lean_dec(v_unused_3681_);
v___x_3675_ = v___x_3673_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_dec(v___x_3673_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v_a_3667_);
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3667_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v_a_3667_);
v_a_3682_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3673_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3673_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_a_3692_ = lean_ctor_get(v_r_3666_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v_r_3666_, 1);
v___x_3693_ = lean_box(0);
v___x_3694_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3658_, v_ctx_x3f_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v_a_3665_, v___x_3693_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v___x_3694_, 0);
lean_dec(v_unused_3702_);
v___x_3696_ = v___x_3694_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v___x_3694_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 1);
lean_ctor_set(v___x_3696_, 0, v_a_3692_);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3692_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_a_3692_);
v_a_3703_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3694_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3694_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_3711_, lean_object* v_ctx_x3f_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3711_, v_ctx_x3f_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; lean_object* v_env_3726_; lean_object* v___x_3727_; lean_object* v_toCold_3728_; lean_object* v_mctx_3729_; lean_object* v_currNamespace_3730_; lean_object* v_openDecls_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v_ngen_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3725_ = lean_st_ref_get(v___y_3723_);
v_env_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc_ref(v_env_3726_);
lean_dec(v___x_3725_);
v___x_3727_ = lean_st_ref_get(v___y_3721_);
v_toCold_3728_ = lean_ctor_get(v___y_3722_, 0);
v_mctx_3729_ = lean_ctor_get(v___x_3727_, 0);
lean_inc_ref(v_mctx_3729_);
lean_dec(v___x_3727_);
v_currNamespace_3730_ = lean_ctor_get(v_toCold_3728_, 4);
v_openDecls_3731_ = lean_ctor_get(v_toCold_3728_, 5);
v___x_3732_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3722_);
v___x_3733_ = lean_st_ref_get(v___y_3723_);
v_ngen_3734_ = lean_ctor_get(v___x_3733_, 2);
lean_inc_ref(v_ngen_3734_);
lean_dec(v___x_3733_);
v___x_3735_ = lean_box(0);
v___x_3736_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_3731_);
lean_inc(v_currNamespace_3730_);
v___x_3737_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3737_, 0, v_env_3726_);
lean_ctor_set(v___x_3737_, 1, v___x_3735_);
lean_ctor_set(v___x_3737_, 2, v___x_3736_);
lean_ctor_set(v___x_3737_, 3, v_mctx_3729_);
lean_ctor_set(v___x_3737_, 4, v___x_3732_);
lean_ctor_set(v___x_3737_, 5, v_currNamespace_3730_);
lean_ctor_set(v___x_3737_, 6, v_openDecls_3731_);
lean_ctor_set(v___x_3737_, 7, v_ngen_3734_);
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; lean_object* v_toCold_3752_; lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3777_; 
v___x_3751_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3747_, v___y_3748_, v___y_3749_);
v_toCold_3752_ = lean_ctor_get(v___y_3748_, 0);
v_a_3753_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3755_ = v___x_3751_;
v_isShared_3756_ = v_isSharedCheck_3777_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3751_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3777_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v_fileMap_3757_; lean_object* v_env_3758_; lean_object* v_mctx_3759_; lean_object* v_options_3760_; lean_object* v_currNamespace_3761_; lean_object* v_openDecls_3762_; lean_object* v_ngen_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3774_; 
v_fileMap_3757_ = lean_ctor_get(v_toCold_3752_, 1);
v_env_3758_ = lean_ctor_get(v_a_3753_, 0);
v_mctx_3759_ = lean_ctor_get(v_a_3753_, 3);
v_options_3760_ = lean_ctor_get(v_a_3753_, 4);
v_currNamespace_3761_ = lean_ctor_get(v_a_3753_, 5);
v_openDecls_3762_ = lean_ctor_get(v_a_3753_, 6);
v_ngen_3763_ = lean_ctor_get(v_a_3753_, 7);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_a_3753_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; lean_object* v_unused_3776_; 
v_unused_3775_ = lean_ctor_get(v_a_3753_, 2);
lean_dec(v_unused_3775_);
v_unused_3776_ = lean_ctor_get(v_a_3753_, 1);
lean_dec(v_unused_3776_);
v___x_3765_ = v_a_3753_;
v_isShared_3766_ = v_isSharedCheck_3774_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_ngen_3763_);
lean_inc(v_openDecls_3762_);
lean_inc(v_currNamespace_3761_);
lean_inc(v_options_3760_);
lean_inc(v_mctx_3759_);
lean_inc(v_env_3758_);
lean_dec(v_a_3753_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3774_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = lean_box(0);
lean_inc_ref(v_fileMap_3757_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 2, v_fileMap_3757_);
lean_ctor_set(v___x_3765_, 1, v___x_3767_);
v___x_3769_ = v___x_3765_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_env_3758_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_fileMap_3757_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_mctx_3759_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v_options_3760_);
lean_ctor_set(v_reuseFailAlloc_3773_, 5, v_currNamespace_3761_);
lean_ctor_set(v_reuseFailAlloc_3773_, 6, v_openDecls_3762_);
lean_ctor_set(v_reuseFailAlloc_3773_, 7, v_ngen_3763_);
v___x_3769_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3771_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3769_);
v___x_3771_ = v___x_3755_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3803_; 
v___x_3793_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3803_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3803_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v_a_3794_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3799_);
v___x_3801_ = v___x_3796_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object* v_x_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___f_3821_; lean_object* v___x_3822_; 
v___f_3821_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0));
v___x_3822_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3813_, v___f_3821_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object* v_x_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object* v_00_u03b1_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object* v_00_u03b1_3842_, lean_object* v_x_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(v_00_u03b1_3842_, v_x_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3851_;
}
}
static uint64_t _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_3872_; uint64_t v___x_3873_; 
v___x_3872_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3873_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3872_);
return v___x_3873_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6(void){
_start:
{
uint64_t v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = lean_uint64_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5);
v___x_3875_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3876_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set_uint64(v___x_3876_, sizeof(void*)*1, v___x_3874_);
return v___x_3876_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7(void){
_start:
{
uint8_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3877_ = 1;
v___x_3878_ = lean_unsigned_to_nat(0u);
v___x_3879_ = lean_box(0);
v___x_3880_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1));
v___x_3881_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_3882_ = lean_box(1);
v___x_3883_ = 0;
v___x_3884_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6);
v___x_3885_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
lean_ctor_set(v___x_3885_, 1, v___x_3882_);
lean_ctor_set(v___x_3885_, 2, v___x_3881_);
lean_ctor_set(v___x_3885_, 3, v___x_3880_);
lean_ctor_set(v___x_3885_, 4, v___x_3879_);
lean_ctor_set(v___x_3885_, 5, v___x_3878_);
lean_ctor_set(v___x_3885_, 6, v___x_3879_);
lean_ctor_set_uint8(v___x_3885_, sizeof(void*)*7, v___x_3883_);
lean_ctor_set_uint8(v___x_3885_, sizeof(void*)*7 + 1, v___x_3883_);
lean_ctor_set_uint8(v___x_3885_, sizeof(void*)*7 + 2, v___x_3883_);
lean_ctor_set_uint8(v___x_3885_, sizeof(void*)*7 + 3, v___x_3877_);
return v___x_3885_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3886_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3887_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3888_ = lean_unsigned_to_nat(0u);
v___x_3889_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
lean_ctor_set(v___x_3889_, 2, v___x_3888_);
lean_ctor_set(v___x_3889_, 3, v___x_3888_);
lean_ctor_set(v___x_3889_, 4, v___x_3887_);
lean_ctor_set(v___x_3889_, 5, v___x_3887_);
lean_ctor_set(v___x_3889_, 6, v___x_3887_);
lean_ctor_set(v___x_3889_, 7, v___x_3887_);
lean_ctor_set(v___x_3889_, 8, v___x_3887_);
lean_ctor_set(v___x_3889_, 9, v___x_3887_);
lean_ctor_set(v___x_3889_, 10, v___x_3887_);
lean_ctor_set(v___x_3889_, 11, v___x_3886_);
return v___x_3889_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3891_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
lean_ctor_set(v___x_3891_, 2, v___x_3890_);
lean_ctor_set(v___x_3891_, 3, v___x_3890_);
lean_ctor_set(v___x_3891_, 4, v___x_3890_);
lean_ctor_set(v___x_3891_, 5, v___x_3890_);
lean_ctor_set(v___x_3891_, 6, v___x_3890_);
return v___x_3891_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
lean_ctor_set(v___x_3893_, 2, v___x_3892_);
lean_ctor_set(v___x_3893_, 3, v___x_3892_);
lean_ctor_set(v___x_3893_, 4, v___x_3892_);
return v___x_3893_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3894_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10);
v___x_3895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_3896_ = lean_box(1);
v___x_3897_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
v___x_3898_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8);
v___x_3899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
lean_ctor_set(v___x_3899_, 1, v___x_3897_);
lean_ctor_set(v___x_3899_, 2, v___x_3896_);
lean_ctor_set(v___x_3899_, 3, v___x_3895_);
lean_ctor_set(v___x_3899_, 4, v___x_3894_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object* v_mx_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3904_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed), 9, 2);
lean_closure_set(v___x_3904_, 0, lean_box(0));
lean_closure_set(v___x_3904_, 1, v_mx_3900_);
v___x_3905_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2));
v___x_3906_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3907_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7);
v___x_3908_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11);
v___x_3909_ = lean_st_mk_ref(v___x_3908_);
v___x_3910_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3904_, v___x_3905_, v___x_3906_, v___x_3907_, v___x_3909_, v_a_3901_, v_a_3902_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3920_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3920_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3920_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_fst_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v_fst_3915_ = lean_ctor_get(v_a_3911_, 0);
lean_inc(v_fst_3915_);
lean_dec(v_a_3911_);
v___x_3916_ = lean_st_ref_get(v___x_3909_);
lean_dec(v___x_3909_);
lean_dec(v___x_3916_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v_fst_3915_);
v___x_3918_ = v___x_3913_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_fst_3915_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v___x_3909_);
v_a_3921_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3910_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3910_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object* v_mx_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3929_, v_a_3930_, v_a_3931_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object* v_00_u03b1_3934_, lean_object* v_mx_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3935_, v_a_3936_, v_a_3937_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object* v_00_u03b1_3940_, lean_object* v_mx_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_3940_, v_mx_3941_, v_a_3942_, v_a_3943_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3949_, v___y_3950_, v___y_3951_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; 
v___x_3969_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3967_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object* v_00_u03b1_3978_, lean_object* v_x_3979_, lean_object* v_ctx_x3f_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3979_, v_ctx_x3f_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3989_, lean_object* v_x_3990_, lean_object* v_ctx_x3f_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_3989_, v_x_3990_, v_ctx_x3f_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object* v_eval_4000_, uint8_t v_logExceptions_4001_, lean_object* v_onErr_4002_, lean_object* v_init_4003_, lean_object* v_cfg_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_4000_, v_logExceptions_4001_, v_onErr_4002_, v_init_4003_, v_cfg_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object* v_eval_4013_, lean_object* v_logExceptions_4014_, lean_object* v_onErr_4015_, lean_object* v_init_4016_, lean_object* v_cfg_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
uint8_t v_logExceptions_boxed_4025_; lean_object* v_res_4026_; 
v_logExceptions_boxed_4025_ = lean_unbox(v_logExceptions_4014_);
v_res_4026_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4013_, v_logExceptions_boxed_4025_, v_onErr_4015_, v_init_4016_, v_cfg_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object* v_eval_4027_, lean_object* v_init_4028_, lean_object* v_cfg_4029_, lean_object* v_onErr_4030_, uint8_t v_logExceptions_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4035_ = lean_unsigned_to_nat(0u);
lean_inc(v_cfg_4029_);
v___x_4036_ = l_Lean_Syntax_matchesNull(v_cfg_4029_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___f_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4037_ = lean_box(v_logExceptions_4031_);
lean_inc(v_cfg_4029_);
lean_inc(v_init_4028_);
v___f_4038_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4038_, 0, v_eval_4027_);
lean_closure_set(v___f_4038_, 1, v___x_4037_);
lean_closure_set(v___f_4038_, 2, v_onErr_4030_);
lean_closure_set(v___f_4038_, 3, v_init_4028_);
lean_closure_set(v___f_4038_, 4, v_cfg_4029_);
v___x_4039_ = l_Lean_Syntax_getNumArgs(v_cfg_4029_);
v___x_4040_ = lean_unsigned_to_nat(1u);
v___x_4041_ = lean_nat_dec_eq(v___x_4039_, v___x_4040_);
lean_dec(v___x_4039_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; 
lean_dec(v_cfg_4029_);
lean_dec(v_init_4028_);
v___x_4042_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4038_, v_a_4032_, v_a_4033_);
return v___x_4042_;
}
else
{
lean_object* v___x_4043_; uint8_t v___x_4044_; 
v___x_4043_ = l_Lean_Syntax_getArg(v_cfg_4029_, v___x_4035_);
lean_dec(v_cfg_4029_);
v___x_4044_ = l_Lean_Syntax_matchesNull(v___x_4043_, v___x_4035_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; 
lean_dec(v_init_4028_);
v___x_4045_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4038_, v_a_4032_, v_a_4033_);
return v___x_4045_;
}
else
{
lean_object* v___x_4046_; 
lean_dec_ref(v___f_4038_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v_init_4028_);
return v___x_4046_;
}
}
}
else
{
lean_object* v___x_4047_; 
lean_dec_ref(v_onErr_4030_);
lean_dec(v_cfg_4029_);
lean_dec_ref(v_eval_4027_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v_init_4028_);
return v___x_4047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object* v_eval_4048_, lean_object* v_init_4049_, lean_object* v_cfg_4050_, lean_object* v_onErr_4051_, lean_object* v_logExceptions_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
uint8_t v_logExceptions_boxed_4056_; lean_object* v_res_4057_; 
v_logExceptions_boxed_4056_ = lean_unbox(v_logExceptions_4052_);
v_res_4057_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4048_, v_init_4049_, v_cfg_4050_, v_onErr_4051_, v_logExceptions_boxed_4056_, v_a_4053_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object* v_00_u03b1_4058_, lean_object* v_eval_4059_, lean_object* v_init_4060_, lean_object* v_cfg_4061_, lean_object* v_onErr_4062_, uint8_t v_logExceptions_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4059_, v_init_4060_, v_cfg_4061_, v_onErr_4062_, v_logExceptions_4063_, v_a_4064_, v_a_4065_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object* v_00_u03b1_4068_, lean_object* v_eval_4069_, lean_object* v_init_4070_, lean_object* v_cfg_4071_, lean_object* v_onErr_4072_, lean_object* v_logExceptions_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_){
_start:
{
uint8_t v_logExceptions_boxed_4077_; lean_object* v_res_4078_; 
v_logExceptions_boxed_4077_ = lean_unbox(v_logExceptions_4073_);
v_res_4078_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(v_00_u03b1_4068_, v_eval_4069_, v_init_4070_, v_cfg_4071_, v_onErr_4072_, v_logExceptions_boxed_4077_, v_a_4074_, v_a_4075_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object* v_eval_4079_, uint8_t v_logExceptions_4080_, lean_object* v_onErr_4081_, lean_object* v_init_4082_, lean_object* v_cfgs_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_4079_, v_logExceptions_4080_, v_onErr_4081_, v_init_4082_, v_cfgs_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object* v_eval_4092_, lean_object* v_logExceptions_4093_, lean_object* v_onErr_4094_, lean_object* v_init_4095_, lean_object* v_cfgs_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
uint8_t v_logExceptions_boxed_4104_; lean_object* v_res_4105_; 
v_logExceptions_boxed_4104_ = lean_unbox(v_logExceptions_4093_);
v_res_4105_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4092_, v_logExceptions_boxed_4104_, v_onErr_4094_, v_init_4095_, v_cfgs_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec_ref(v_cfgs_4096_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object* v_eval_4106_, lean_object* v_init_4107_, lean_object* v_cfgs_4108_, lean_object* v_onErr_4109_, uint8_t v_logExceptions_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4114_ = lean_array_get_size(v_cfgs_4108_);
v___x_4115_ = lean_unsigned_to_nat(0u);
v___x_4116_ = lean_nat_dec_eq(v___x_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___f_4118_; lean_object* v___x_4119_; 
v___x_4117_ = lean_box(v_logExceptions_4110_);
v___f_4118_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4118_, 0, v_eval_4106_);
lean_closure_set(v___f_4118_, 1, v___x_4117_);
lean_closure_set(v___f_4118_, 2, v_onErr_4109_);
lean_closure_set(v___f_4118_, 3, v_init_4107_);
lean_closure_set(v___f_4118_, 4, v_cfgs_4108_);
v___x_4119_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4118_, v_a_4111_, v_a_4112_);
return v___x_4119_;
}
else
{
lean_object* v___x_4120_; 
lean_dec_ref(v_onErr_4109_);
lean_dec_ref(v_cfgs_4108_);
lean_dec_ref(v_eval_4106_);
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v_init_4107_);
return v___x_4120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object* v_eval_4121_, lean_object* v_init_4122_, lean_object* v_cfgs_4123_, lean_object* v_onErr_4124_, lean_object* v_logExceptions_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
uint8_t v_logExceptions_boxed_4129_; lean_object* v_res_4130_; 
v_logExceptions_boxed_4129_ = lean_unbox(v_logExceptions_4125_);
v_res_4130_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4121_, v_init_4122_, v_cfgs_4123_, v_onErr_4124_, v_logExceptions_boxed_4129_, v_a_4126_, v_a_4127_);
lean_dec(v_a_4127_);
lean_dec_ref(v_a_4126_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object* v_00_u03b1_4131_, lean_object* v_eval_4132_, lean_object* v_init_4133_, lean_object* v_cfgs_4134_, lean_object* v_onErr_4135_, uint8_t v_logExceptions_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4132_, v_init_4133_, v_cfgs_4134_, v_onErr_4135_, v_logExceptions_4136_, v_a_4137_, v_a_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object* v_00_u03b1_4141_, lean_object* v_eval_4142_, lean_object* v_init_4143_, lean_object* v_cfgs_4144_, lean_object* v_onErr_4145_, lean_object* v_logExceptions_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
uint8_t v_logExceptions_boxed_4150_; lean_object* v_res_4151_; 
v_logExceptions_boxed_4150_ = lean_unbox(v_logExceptions_4146_);
v_res_4151_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(v_00_u03b1_4141_, v_eval_4142_, v_init_4143_, v_cfgs_4144_, v_onErr_4145_, v_logExceptions_boxed_4150_, v_a_4147_, v_a_4148_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
return v_res_4151_;
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

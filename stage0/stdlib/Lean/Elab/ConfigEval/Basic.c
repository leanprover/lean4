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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
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
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
lean_object* v_evalTerm_10_; lean_object* v_toCold_11_; lean_object* v_currRecDepth_12_; lean_object* v_ref_13_; uint16_t v_optionFlags_14_; uint8_t v_suppressElabErrors_15_; uint8_t v_isRecordingDeps_16_; lean_object* v_ref_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_evalTerm_10_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_evalTerm_10_);
lean_dec_ref(v_inst_1_);
v_toCold_11_ = lean_ctor_get(v_a_7_, 0);
v_currRecDepth_12_ = lean_ctor_get(v_a_7_, 1);
v_ref_13_ = lean_ctor_get(v_a_7_, 2);
v_optionFlags_14_ = lean_ctor_get_uint16(v_a_7_, sizeof(void*)*3);
v_suppressElabErrors_15_ = lean_ctor_get_uint8(v_a_7_, sizeof(void*)*3 + 2);
v_isRecordingDeps_16_ = lean_ctor_get_uint8(v_a_7_, sizeof(void*)*3 + 3);
v_ref_17_ = l_Lean_replaceRef(v_stx_2_, v_ref_13_);
lean_inc(v_currRecDepth_12_);
lean_inc_ref(v_toCold_11_);
v___x_18_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_18_, 0, v_toCold_11_);
lean_ctor_set(v___x_18_, 1, v_currRecDepth_12_);
lean_ctor_set(v___x_18_, 2, v_ref_17_);
lean_ctor_set_uint16(v___x_18_, sizeof(void*)*3, v_optionFlags_14_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*3 + 2, v_suppressElabErrors_15_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*3 + 3, v_isRecordingDeps_16_);
lean_inc(v_a_8_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_19_ = lean_apply_8(v_evalTerm_10_, v_stx_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v___x_18_, v_a_8_, lean_box(0));
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_28_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_fst_24_; lean_object* v___x_26_; 
v_fst_24_ = lean_ctor_get(v_a_20_, 0);
lean_inc(v_fst_24_);
lean_dec(v_a_20_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v_fst_24_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_fst_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
else
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
v_a_29_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_19_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_19_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___redArg___boxed(lean_object* v_inst_37_, lean_object* v_stx_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_37_, v_stx_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_stx_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_48_, v_stx_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___boxed(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_stx_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Elab_ConfigEval_evalTermWithRef(v_00_u03b1_58_, v_inst_59_, v_stx_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_68_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_instMonadEIO___redArg();
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0);
v___x_71_ = l_StateRefT_x27_instMonad___redArg(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_80_; lean_object* v___f_81_; 
v___x_80_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_81_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_81_, 0, v___x_80_);
return v___f_81_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_82_; lean_object* v___f_83_; 
v___x_82_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_83_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_83_, 0, v___x_82_);
return v___f_83_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12(void){
_start:
{
lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; 
v___f_84_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11);
v___f_85_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___f_85_);
lean_ctor_set(v___x_86_, 1, v___f_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13(void){
_start:
{
lean_object* v___x_87_; lean_object* v___f_88_; 
v___x_87_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_88_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_88_, 0, v___x_87_);
return v___f_88_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14(void){
_start:
{
lean_object* v___x_89_; lean_object* v___f_90_; 
v___x_89_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_90_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_90_, 0, v___x_89_);
return v___f_90_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15(void){
_start:
{
lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; 
v___f_91_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14);
v___f_92_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___f_92_);
lean_ctor_set(v___x_93_, 1, v___f_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16(void){
_start:
{
lean_object* v___x_94_; lean_object* v___f_95_; 
v___x_94_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_95_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_95_, 0, v___x_94_);
return v___f_95_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; 
v___x_96_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_97_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
return v___f_97_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18(void){
_start:
{
lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_100_; 
v___f_98_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17);
v___f_99_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___f_99_);
lean_ctor_set(v___x_100_, 1, v___f_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19(void){
_start:
{
lean_object* v___x_101_; lean_object* v___f_102_; 
v___x_101_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_102_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_102_, 0, v___x_101_);
return v___f_102_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20(void){
_start:
{
lean_object* v___x_103_; lean_object* v___f_104_; 
v___x_103_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_104_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_104_, 0, v___x_103_);
return v___f_104_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21(void){
_start:
{
lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v___f_105_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20);
v___f_106_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___f_106_);
lean_ctor_set(v___x_107_, 1, v___f_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_109_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23));
v___x_112_ = l_Lean_stringToMessageData(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25));
v___x_115_ = l_Lean_stringToMessageData(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27));
v___x_118_ = l_Lean_stringToMessageData(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
v___x_121_ = l_Lean_stringToMessageData(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31));
v___x_124_ = l_Lean_stringToMessageData(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(lean_object* v_inst_125_, lean_object* v_stx_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_toApplicative_135_; lean_object* v_toFunctor_136_; lean_object* v_toSeq_137_; lean_object* v_toSeqLeft_138_; lean_object* v_toSeqRight_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_toApplicative_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_391_; 
v___x_134_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1);
v_toApplicative_135_ = lean_ctor_get(v___x_134_, 0);
v_toFunctor_136_ = lean_ctor_get(v_toApplicative_135_, 0);
v_toSeq_137_ = lean_ctor_get(v_toApplicative_135_, 2);
v_toSeqLeft_138_ = lean_ctor_get(v_toApplicative_135_, 3);
v_toSeqRight_139_ = lean_ctor_get(v_toApplicative_135_, 4);
v___f_140_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2));
v___f_141_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_136_, 2);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_142_, 0, v_toFunctor_136_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_143_, 0, v_toFunctor_136_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___f_142_);
lean_ctor_set(v___x_144_, 1, v___f_143_);
lean_inc(v_toSeqRight_139_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_145_, 0, v_toSeqRight_139_);
lean_inc(v_toSeqLeft_138_);
v___f_146_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_146_, 0, v_toSeqLeft_138_);
lean_inc(v_toSeq_137_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeq_137_);
v___x_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_148_, 0, v___x_144_);
lean_ctor_set(v___x_148_, 1, v___f_140_);
lean_ctor_set(v___x_148_, 2, v___f_147_);
lean_ctor_set(v___x_148_, 3, v___f_146_);
lean_ctor_set(v___x_148_, 4, v___f_145_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___f_141_);
v___x_150_ = l_StateRefT_x27_instMonad___redArg(v___x_149_);
v_toApplicative_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_150_, 1);
lean_dec(v_unused_392_);
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_391_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_toApplicative_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_391_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v_toFunctor_155_; lean_object* v_toSeq_156_; lean_object* v_toSeqLeft_157_; lean_object* v_toSeqRight_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_389_; 
v_toFunctor_155_ = lean_ctor_get(v_toApplicative_151_, 0);
v_toSeq_156_ = lean_ctor_get(v_toApplicative_151_, 2);
v_toSeqLeft_157_ = lean_ctor_get(v_toApplicative_151_, 3);
v_toSeqRight_158_ = lean_ctor_get(v_toApplicative_151_, 4);
v_isSharedCheck_389_ = !lean_is_exclusive(v_toApplicative_151_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_dec(v_unused_390_);
v___x_160_ = v_toApplicative_151_;
v_isShared_161_ = v_isSharedCheck_389_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_toSeqRight_158_);
lean_inc(v_toSeqLeft_157_);
lean_inc(v_toSeq_156_);
lean_inc(v_toFunctor_155_);
lean_dec(v_toApplicative_151_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_389_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___x_171_; 
v___f_162_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4));
v___f_163_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5));
lean_inc_ref(v_toFunctor_155_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_164_, 0, v_toFunctor_155_);
v___f_165_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_165_, 0, v_toFunctor_155_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___f_164_);
lean_ctor_set(v___x_166_, 1, v___f_165_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_167_, 0, v_toSeqRight_158_);
v___f_168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_168_, 0, v_toSeqLeft_157_);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_169_, 0, v_toSeq_156_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 4, v___f_167_);
lean_ctor_set(v___x_160_, 3, v___f_168_);
lean_ctor_set(v___x_160_, 2, v___f_169_);
lean_ctor_set(v___x_160_, 1, v___f_162_);
lean_ctor_set(v___x_160_, 0, v___x_166_);
v___x_171_ = v___x_160_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___f_162_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v___f_169_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v___f_168_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v___f_167_);
v___x_171_ = v_reuseFailAlloc_388_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___f_163_);
lean_ctor_set(v___x_153_, 0, v___x_171_);
v___x_173_ = v___x_153_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___f_163_);
v___x_173_ = v_reuseFailAlloc_387_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v_toApplicative_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_385_; 
v___x_174_ = l_StateRefT_x27_instMonad___redArg(v___x_173_);
v_toApplicative_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v___x_174_, 1);
lean_dec(v_unused_386_);
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_385_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_toApplicative_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_385_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_toFunctor_179_; lean_object* v_toSeq_180_; lean_object* v_toSeqLeft_181_; lean_object* v_toSeqRight_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_383_; 
v_toFunctor_179_ = lean_ctor_get(v_toApplicative_175_, 0);
v_toSeq_180_ = lean_ctor_get(v_toApplicative_175_, 2);
v_toSeqLeft_181_ = lean_ctor_get(v_toApplicative_175_, 3);
v_toSeqRight_182_ = lean_ctor_get(v_toApplicative_175_, 4);
v_isSharedCheck_383_ = !lean_is_exclusive(v_toApplicative_175_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_dec(v_unused_384_);
v___x_184_ = v_toApplicative_175_;
v_isShared_185_ = v_isSharedCheck_383_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_toSeqRight_182_);
lean_inc(v_toSeqLeft_181_);
lean_inc(v_toSeq_180_);
lean_inc(v_toFunctor_179_);
lean_dec(v_toApplicative_175_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_383_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___x_195_; 
v___f_186_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6));
v___f_187_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7));
lean_inc_ref(v_toFunctor_179_);
v___f_188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_188_, 0, v_toFunctor_179_);
v___f_189_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_189_, 0, v_toFunctor_179_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___f_188_);
lean_ctor_set(v___x_190_, 1, v___f_189_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_191_, 0, v_toSeqRight_182_);
v___f_192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_192_, 0, v_toSeqLeft_181_);
v___f_193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_193_, 0, v_toSeq_180_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 4, v___f_191_);
lean_ctor_set(v___x_184_, 3, v___f_192_);
lean_ctor_set(v___x_184_, 2, v___f_193_);
lean_ctor_set(v___x_184_, 1, v___f_186_);
lean_ctor_set(v___x_184_, 0, v___x_190_);
v___x_195_ = v___x_184_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___f_186_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v___f_193_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v___f_192_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v___f_191_);
v___x_195_ = v_reuseFailAlloc_382_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___f_187_);
lean_ctor_set(v___x_177_, 0, v___x_195_);
v___x_197_ = v___x_177_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___f_187_);
v___x_197_ = v_reuseFailAlloc_381_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v_toMonadQuotation_199_; lean_object* v_toMonadRef_200_; lean_object* v___x_201_; lean_object* v_getMCtx_202_; lean_object* v_modifyMCtx_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_evalExpr_215_; lean_object* v_expectedType_x3f_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_380_; 
v___x_198_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_199_ = lean_ctor_get(v___x_198_, 0);
v_toMonadRef_200_ = lean_ctor_get(v_toMonadQuotation_199_, 0);
v___x_201_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_202_ = lean_ctor_get(v___x_201_, 0);
v_modifyMCtx_203_ = lean_ctor_get(v___x_201_, 1);
v___f_204_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8));
v___x_205_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9));
lean_inc(v_modifyMCtx_203_);
v___f_206_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_206_, 0, v_modifyMCtx_203_);
lean_closure_set(v___f_206_, 1, v___x_205_);
lean_inc(v_getMCtx_202_);
v___x_207_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_207_, 0, lean_box(0));
lean_closure_set(v___x_207_, 1, lean_box(0));
lean_closure_set(v___x_207_, 2, lean_box(0));
lean_closure_set(v___x_207_, 3, lean_box(0));
lean_closure_set(v___x_207_, 4, v_getMCtx_202_);
v___f_208_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_208_, 0, v___f_206_);
lean_closure_set(v___f_208_, 1, v___f_204_);
v___x_209_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, v___x_207_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___f_208_);
v___x_211_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_212_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_200_);
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v_toMonadRef_200_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
v___x_214_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22);
v_evalExpr_215_ = lean_ctor_get(v_inst_125_, 0);
v_expectedType_x3f_216_ = lean_ctor_get(v_inst_125_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_inst_125_);
if (v_isSharedCheck_380_ == 0)
{
v___x_218_ = v_inst_125_;
v_isShared_219_ = v_isSharedCheck_380_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_expectedType_x3f_216_);
lean_inc(v_evalExpr_215_);
lean_dec(v_inst_125_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_380_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_toCold_225_; lean_object* v_currRecDepth_226_; lean_object* v_ref_227_; uint16_t v_optionFlags_228_; uint8_t v_suppressElabErrors_229_; uint8_t v_isRecordingDeps_230_; uint8_t v___x_231_; lean_object* v_ref_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_220_ = 1;
v___x_221_ = lean_box(0);
v___x_222_ = lean_box(v___x_220_);
v___x_223_ = lean_box(v___x_220_);
lean_inc(v_expectedType_x3f_216_);
lean_inc(v_stx_126_);
v___x_224_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_224_, 0, v_stx_126_);
lean_closure_set(v___x_224_, 1, v_expectedType_x3f_216_);
lean_closure_set(v___x_224_, 2, v___x_222_);
lean_closure_set(v___x_224_, 3, v___x_223_);
lean_closure_set(v___x_224_, 4, v___x_221_);
v_toCold_225_ = lean_ctor_get(v_a_131_, 0);
v_currRecDepth_226_ = lean_ctor_get(v_a_131_, 1);
v_ref_227_ = lean_ctor_get(v_a_131_, 2);
v_optionFlags_228_ = lean_ctor_get_uint16(v_a_131_, sizeof(void*)*3);
v_suppressElabErrors_229_ = lean_ctor_get_uint8(v_a_131_, sizeof(void*)*3 + 2);
v_isRecordingDeps_230_ = lean_ctor_get_uint8(v_a_131_, sizeof(void*)*3 + 3);
v___x_231_ = 1;
v_ref_232_ = l_Lean_replaceRef(v_stx_126_, v_ref_227_);
lean_dec(v_stx_126_);
lean_inc(v_currRecDepth_226_);
lean_inc_ref(v_toCold_225_);
v___x_233_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_233_, 0, v_toCold_225_);
lean_ctor_set(v___x_233_, 1, v_currRecDepth_226_);
lean_ctor_set(v___x_233_, 2, v_ref_232_);
lean_ctor_set_uint16(v___x_233_, sizeof(void*)*3, v_optionFlags_228_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*3 + 2, v_suppressElabErrors_229_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*3 + 3, v_isRecordingDeps_230_);
v___x_234_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_224_, v___x_231_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v___x_233_, v_a_132_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_3629__overap_236_; lean_object* v___x_237_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
lean_inc_ref(v___x_197_);
v___x_3629__overap_236_ = l_Lean_instantiateMVars___redArg(v___x_197_, v___x_210_, v_a_235_);
lean_inc(v_a_132_);
lean_inc_ref(v___x_233_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v_a_127_);
v___x_237_ = lean_apply_7(v___x_3629__overap_236_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v___x_233_, v_a_132_, lean_box(0));
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; uint8_t v___y_265_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; uint8_t v___x_352_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_352_ = l_Lean_Expr_hasSorry(v_a_238_);
if (v___x_352_ == 0)
{
v___y_295_ = v_a_127_;
v___y_296_ = v_a_128_;
v___y_297_ = v_a_129_;
v___y_298_ = v_a_130_;
v___y_299_ = v___x_233_;
v___y_300_ = v_a_132_;
goto v___jp_294_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_Expr_hasSyntheticSorry(v_a_238_);
if (v___x_353_ == 0)
{
v___y_333_ = v_a_127_;
v___y_334_ = v_a_128_;
v___y_335_ = v_a_129_;
v___y_336_ = v_a_130_;
v___y_337_ = v___x_233_;
v___y_338_ = v_a_132_;
goto v___jp_332_;
}
else
{
lean_object* v___x_3637__overap_354_; lean_object* v___x_355_; 
v___x_3637__overap_354_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_214_);
lean_inc(v_a_132_);
lean_inc_ref(v___x_233_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v_a_127_);
v___x_355_ = lean_apply_7(v___x_3637__overap_354_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v___x_233_, v_a_132_, lean_box(0));
if (lean_obj_tag(v___x_355_) == 0)
{
lean_dec_ref_known(v___x_355_, 1);
v___y_333_ = v_a_127_;
v___y_334_ = v_a_128_;
v___y_335_ = v_a_129_;
v___y_336_ = v_a_130_;
v___y_337_ = v___x_233_;
v___y_338_ = v_a_132_;
goto v___jp_332_;
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_a_238_);
lean_dec_ref_known(v___x_233_, 3);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref(v_evalExpr_215_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
v___jp_239_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24);
v___x_248_ = l_Lean_indentExpr(v_a_238_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 7);
lean_ctor_set(v___x_218_, 1, v___x_248_);
lean_ctor_set(v___x_218_, 0, v___x_247_);
v___x_250_ = v___x_218_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_254_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_3631__overap_252_; lean_object* v___x_253_; 
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___y_246_);
v___x_3631__overap_252_ = l_Lean_throwError___redArg(v___x_197_, v___x_213_, v___x_251_);
lean_inc(v___y_241_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_240_);
v___x_253_ = lean_apply_7(v___x_3631__overap_252_, v___y_240_, v___y_245_, v___y_242_, v___y_243_, v___y_244_, v___y_241_, lean_box(0));
return v___x_253_;
}
}
v___jp_255_:
{
if (v___y_265_ == 0)
{
if (lean_obj_tag(v___y_261_) == 0)
{
lean_dec_ref_known(v___y_261_, 2);
lean_dec_ref(v___y_263_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
return v___y_264_;
}
else
{
lean_object* v_id_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_280_; 
v_id_266_ = lean_ctor_get(v___y_261_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___y_261_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___y_261_, 1);
lean_dec(v_unused_281_);
v___x_268_ = v___y_261_;
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_id_266_);
lean_dec(v___y_261_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
uint8_t v___x_270_; 
v___x_270_ = l_Lean_instBEqInternalExceptionId_beq(v___y_260_, v_id_266_);
lean_dec(v_id_266_);
if (v___x_270_ == 0)
{
lean_del_object(v___x_268_);
lean_dec_ref(v___y_263_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
return v___y_264_;
}
else
{
lean_dec_ref(v___y_264_);
if (lean_obj_tag(v_expectedType_x3f_216_) == 1)
{
lean_object* v_val_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v_val_271_ = lean_ctor_get(v_expectedType_x3f_216_, 0);
lean_inc(v_val_271_);
lean_dec_ref_known(v_expectedType_x3f_216_, 1);
v___x_272_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26);
v___x_273_ = l_Lean_MessageData_ofExpr(v_val_271_);
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 7);
lean_ctor_set(v___x_268_, 1, v___x_273_);
lean_ctor_set(v___x_268_, 0, v___x_272_);
v___x_275_ = v___x_268_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___y_240_ = v___y_256_;
v___y_241_ = v___y_257_;
v___y_242_ = v___y_258_;
v___y_243_ = v___y_259_;
v___y_244_ = v___y_263_;
v___y_245_ = v___y_262_;
v___y_246_ = v___x_277_;
goto v___jp_239_;
}
}
else
{
lean_object* v___x_279_; 
lean_del_object(v___x_268_);
lean_dec(v_expectedType_x3f_216_);
v___x_279_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_240_ = v___y_256_;
v___y_241_ = v___y_257_;
v___y_242_ = v___y_258_;
v___y_243_ = v___y_259_;
v___y_244_ = v___y_263_;
v___y_245_ = v___y_262_;
v___y_246_ = v___x_279_;
goto v___jp_239_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_263_);
lean_dec_ref(v___y_261_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
return v___y_264_;
}
}
v___jp_282_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v___y_288_);
lean_inc_ref(v___y_287_);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
lean_inc(v_a_238_);
v___x_290_ = lean_apply_6(v_evalExpr_215_, v_a_238_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, lean_box(0));
if (lean_obj_tag(v___x_290_) == 0)
{
lean_dec_ref(v___y_287_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
return v___x_290_;
}
else
{
lean_object* v_a_291_; uint8_t v___x_292_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
v___x_292_ = l_Lean_Exception_isInterrupt(v_a_291_);
if (v___x_292_ == 0)
{
uint8_t v___x_293_; 
lean_inc(v_a_291_);
v___x_293_ = l_Lean_Exception_isRuntime(v_a_291_);
v___y_256_ = v___y_283_;
v___y_257_ = v___y_288_;
v___y_258_ = v___y_285_;
v___y_259_ = v___y_286_;
v___y_260_ = v___x_289_;
v___y_261_ = v_a_291_;
v___y_262_ = v___y_284_;
v___y_263_ = v___y_287_;
v___y_264_ = v___x_290_;
v___y_265_ = v___x_293_;
goto v___jp_255_;
}
else
{
v___y_256_ = v___y_283_;
v___y_257_ = v___y_288_;
v___y_258_ = v___y_285_;
v___y_259_ = v___y_286_;
v___y_260_ = v___x_289_;
v___y_261_ = v_a_291_;
v___y_262_ = v___y_284_;
v___y_263_ = v___y_287_;
v___y_264_ = v___x_290_;
v___y_265_ = v___x_292_;
goto v___jp_255_;
}
}
}
v___jp_294_:
{
lean_object* v___x_301_; 
lean_inc(v_a_238_);
v___x_301_ = l_Lean_Meta_getMVars(v_a_238_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_303_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v___x_303_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_302_, v___x_221_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v_a_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; uint8_t v___x_305_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
v___x_305_ = lean_unbox(v_a_304_);
lean_dec(v_a_304_);
if (v___x_305_ == 0)
{
v___y_283_ = v___y_295_;
v___y_284_ = v___y_296_;
v___y_285_ = v___y_297_;
v___y_286_ = v___y_298_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_300_;
goto v___jp_282_;
}
else
{
lean_object* v___x_3633__overap_306_; lean_object* v___x_307_; 
v___x_3633__overap_306_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_214_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc(v___y_298_);
lean_inc_ref(v___y_297_);
lean_inc(v___y_296_);
lean_inc_ref(v___y_295_);
v___x_307_ = lean_apply_7(v___x_3633__overap_306_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, lean_box(0));
if (lean_obj_tag(v___x_307_) == 0)
{
lean_dec_ref_known(v___x_307_, 1);
v___y_283_ = v___y_295_;
v___y_284_ = v___y_296_;
v___y_285_ = v___y_297_;
v___y_286_ = v___y_298_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_300_;
goto v___jp_282_;
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v___y_299_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref(v_evalExpr_215_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v___y_299_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref(v_evalExpr_215_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
v_a_316_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_303_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_303_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v___y_299_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref(v_evalExpr_215_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
v_a_324_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_301_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_301_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
v___jp_332_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_3635__overap_342_; lean_object* v___x_343_; 
v___x_339_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32);
lean_inc(v_a_238_);
v___x_340_ = l_Lean_indentExpr(v_a_238_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref(v___x_213_);
lean_inc_ref(v___x_197_);
v___x_3635__overap_342_ = l_Lean_throwError___redArg(v___x_197_, v___x_213_, v___x_341_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
lean_inc(v___y_334_);
lean_inc_ref(v___y_333_);
v___x_343_ = lean_apply_7(v___x_3635__overap_342_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, lean_box(0));
if (lean_obj_tag(v___x_343_) == 0)
{
lean_dec_ref_known(v___x_343_, 1);
v___y_295_ = v___y_333_;
v___y_296_ = v___y_334_;
v___y_297_ = v___y_335_;
v___y_298_ = v___y_336_;
v___y_299_ = v___y_337_;
v___y_300_ = v___y_338_;
goto v___jp_294_;
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v___y_337_);
lean_dec(v_a_238_);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref(v_evalExpr_215_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref_known(v___x_233_, 3);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref(v_evalExpr_215_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref(v___x_197_);
v_a_364_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_237_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_237_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref_known(v___x_233_, 3);
lean_del_object(v___x_218_);
lean_dec(v_expectedType_x3f_216_);
lean_dec_ref(v_evalExpr_215_);
lean_dec_ref_known(v___x_213_, 3);
lean_dec_ref_known(v___x_210_, 2);
lean_dec_ref(v___x_197_);
v_a_372_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_234_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_234_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___boxed(lean_object* v_inst_393_, lean_object* v_stx_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_393_, v_stx_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_stx_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_404_, v_stx_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___boxed(lean_object* v_00_u03b1_414_, lean_object* v_inst_415_, lean_object* v_stx_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Elab_ConfigEval_evalExprWithElab(v_00_u03b1_414_, v_inst_415_, v_stx_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_stx_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_evalTerm_435_; lean_object* v_toCold_436_; lean_object* v_currRecDepth_437_; lean_object* v_ref_438_; uint16_t v_optionFlags_439_; uint8_t v_suppressElabErrors_440_; uint8_t v_isRecordingDeps_441_; lean_object* v___x_442_; lean_object* v_ref_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_evalTerm_435_ = lean_ctor_get(v_inst_425_, 0);
lean_inc_ref(v_evalTerm_435_);
lean_dec_ref(v_inst_425_);
v_toCold_436_ = lean_ctor_get(v_a_432_, 0);
v_currRecDepth_437_ = lean_ctor_get(v_a_432_, 1);
v_ref_438_ = lean_ctor_get(v_a_432_, 2);
v_optionFlags_439_ = lean_ctor_get_uint16(v_a_432_, sizeof(void*)*3);
v_suppressElabErrors_440_ = lean_ctor_get_uint8(v_a_432_, sizeof(void*)*3 + 2);
v_isRecordingDeps_441_ = lean_ctor_get_uint8(v_a_432_, sizeof(void*)*3 + 3);
v___x_442_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_443_ = l_Lean_replaceRef(v_stx_427_, v_ref_438_);
lean_inc(v_currRecDepth_437_);
lean_inc_ref(v_toCold_436_);
v___x_444_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_444_, 0, v_toCold_436_);
lean_ctor_set(v___x_444_, 1, v_currRecDepth_437_);
lean_ctor_set(v___x_444_, 2, v_ref_443_);
lean_ctor_set_uint16(v___x_444_, sizeof(void*)*3, v_optionFlags_439_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*3 + 2, v_suppressElabErrors_440_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*3 + 3, v_isRecordingDeps_441_);
lean_inc(v_a_433_);
lean_inc_ref(v___x_444_);
lean_inc(v_a_431_);
lean_inc_ref(v_a_430_);
lean_inc(v_a_429_);
lean_inc_ref(v_a_428_);
lean_inc(v_stx_427_);
v___x_445_ = lean_apply_8(v_evalTerm_435_, v_stx_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v___x_444_, v_a_433_, lean_box(0));
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref_known(v___x_444_, 3);
lean_dec(v_stx_427_);
lean_dec_ref(v_inst_426_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_fst_450_; lean_object* v___x_452_; 
v_fst_450_ = lean_ctor_get(v_a_446_, 0);
lean_inc(v_fst_450_);
lean_dec(v_a_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_fst_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_fst_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_469_; 
v_a_455_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_469_ == 0)
{
v___x_457_ = v___x_445_;
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_445_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
lean_inc(v_a_455_);
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_468_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
uint8_t v___y_462_; uint8_t v___x_466_; 
v___x_466_ = l_Lean_Exception_isInterrupt(v_a_455_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
lean_inc(v_a_455_);
v___x_467_ = l_Lean_Exception_isRuntime(v_a_455_);
v___y_462_ = v___x_467_;
goto v___jp_461_;
}
else
{
v___y_462_ = v___x_466_;
goto v___jp_461_;
}
v___jp_461_:
{
if (v___y_462_ == 0)
{
if (lean_obj_tag(v_a_455_) == 0)
{
lean_dec_ref_known(v_a_455_, 2);
lean_dec_ref_known(v___x_444_, 3);
lean_dec(v_stx_427_);
lean_dec_ref(v_inst_426_);
return v___x_460_;
}
else
{
lean_object* v_id_463_; uint8_t v___x_464_; 
v_id_463_ = lean_ctor_get(v_a_455_, 0);
lean_inc(v_id_463_);
lean_dec_ref_known(v_a_455_, 2);
v___x_464_ = l_Lean_instBEqInternalExceptionId_beq(v___x_442_, v_id_463_);
lean_dec(v_id_463_);
if (v___x_464_ == 0)
{
lean_dec_ref_known(v___x_444_, 3);
lean_dec(v_stx_427_);
lean_dec_ref(v_inst_426_);
return v___x_460_;
}
else
{
lean_object* v___x_465_; 
lean_dec_ref(v___x_460_);
v___x_465_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_426_, v_stx_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v___x_444_, v_a_433_);
lean_dec_ref_known(v___x_444_, 3);
return v___x_465_;
}
}
}
else
{
lean_dec(v_a_455_);
lean_dec_ref_known(v___x_444_, 3);
lean_dec(v_stx_427_);
lean_dec_ref(v_inst_426_);
return v___x_460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_stx_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_470_, v_inst_471_, v_stx_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(lean_object* v_00_u03b1_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_stx_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_482_, v_inst_483_, v_stx_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___boxed(lean_object* v_00_u03b1_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_stx_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(v_00_u03b1_493_, v_inst_494_, v_inst_495_, v_stx_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4));
lean_inc(v_x_523_);
v___x_525_ = l_Lean_Syntax_isOfKind(v_x_523_, v___x_524_);
if (v___x_525_ == 0)
{
return v_x_523_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = l_Lean_Syntax_getArg(v_x_523_, v___x_526_);
v___x_528_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6));
lean_inc(v___x_527_);
v___x_529_ = l_Lean_Syntax_isOfKind(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v___x_527_);
return v_x_523_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = l_Lean_Syntax_getArg(v___x_527_, v___x_530_);
lean_dec(v___x_527_);
v___x_532_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8));
lean_inc(v___x_531_);
v___x_533_ = l_Lean_Syntax_isOfKind(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v___x_531_);
return v_x_523_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = l_Lean_Syntax_getArg(v___x_531_, v___x_526_);
lean_dec(v___x_531_);
v___x_535_ = lean_box(0);
v___x_536_ = l_Lean_Syntax_matchesIdent(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
if (v___x_536_ == 0)
{
return v_x_523_;
}
else
{
lean_object* v_t_537_; 
v_t_537_ = l_Lean_Syntax_getArg(v_x_523_, v___x_530_);
lean_dec(v_x_523_);
v_x_523_ = v_t_537_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(lean_object* v_expectedType_x3f_539_, lean_object* v_f_540_, lean_object* v_stx_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_toCold_549_; lean_object* v_currRecDepth_550_; lean_object* v_ref_551_; uint16_t v_optionFlags_552_; uint8_t v_suppressElabErrors_553_; uint8_t v_isRecordingDeps_554_; lean_object* v___x_555_; lean_object* v_ref_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_toCold_549_ = lean_ctor_get(v_a_546_, 0);
v_currRecDepth_550_ = lean_ctor_get(v_a_546_, 1);
v_ref_551_ = lean_ctor_get(v_a_546_, 2);
v_optionFlags_552_ = lean_ctor_get_uint16(v_a_546_, sizeof(void*)*3);
v_suppressElabErrors_553_ = lean_ctor_get_uint8(v_a_546_, sizeof(void*)*3 + 2);
v_isRecordingDeps_554_ = lean_ctor_get_uint8(v_a_546_, sizeof(void*)*3 + 3);
lean_inc(v_stx_541_);
v___x_555_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_541_);
v_ref_556_ = l_Lean_replaceRef(v_stx_541_, v_ref_551_);
lean_inc(v_currRecDepth_550_);
lean_inc_ref(v_toCold_549_);
v___x_557_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_557_, 0, v_toCold_549_);
lean_ctor_set(v___x_557_, 1, v_currRecDepth_550_);
lean_ctor_set(v___x_557_, 2, v_ref_556_);
lean_ctor_set_uint16(v___x_557_, sizeof(void*)*3, v_optionFlags_552_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*3 + 2, v_suppressElabErrors_553_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*3 + 3, v_isRecordingDeps_554_);
lean_inc(v_a_547_);
lean_inc(v_a_545_);
lean_inc_ref(v_a_544_);
lean_inc(v_a_543_);
lean_inc_ref(v_a_542_);
v___x_558_ = lean_apply_8(v_f_540_, v___x_555_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v___x_557_, v_a_547_, lean_box(0));
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_590_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_590_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_590_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_590_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_snd_563_; lean_object* v___x_564_; lean_object* v_infoState_565_; uint8_t v_enabled_566_; 
v_snd_563_ = lean_ctor_get(v_a_559_, 1);
v___x_564_ = lean_st_ref_get(v_a_547_);
v_infoState_565_ = lean_ctor_get(v___x_564_, 8);
lean_inc_ref(v_infoState_565_);
lean_dec(v___x_564_);
v_enabled_566_ = lean_ctor_get_uint8(v_infoState_565_, sizeof(void*)*3);
lean_dec_ref(v_infoState_565_);
if (v_enabled_566_ == 0)
{
lean_object* v___x_568_; 
lean_dec(v_stx_541_);
lean_dec(v_expectedType_x3f_539_);
if (v_isShared_562_ == 0)
{
v___x_568_ = v___x_561_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_559_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; 
lean_del_object(v___x_561_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_box(0);
v___x_572_ = 0;
lean_inc(v_snd_563_);
v___x_573_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_541_, v_snd_563_, v_expectedType_x3f_539_, v___x_570_, v___x_571_, v___x_572_, v___x_572_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v___x_573_, 0);
lean_dec(v_unused_581_);
v___x_575_ = v___x_573_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_dec(v___x_573_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_a_559_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_559_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_a_559_);
v_a_582_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_573_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_541_);
lean_dec(v_expectedType_x3f_539_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg___boxed(lean_object* v_expectedType_x3f_591_, lean_object* v_f_592_, lean_object* v_stx_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(v_expectedType_x3f_591_, v_f_592_, v_stx_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(lean_object* v_00_u03b1_602_, lean_object* v_expectedType_x3f_603_, lean_object* v_f_604_, lean_object* v_stx_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_toCold_613_; lean_object* v_currRecDepth_614_; lean_object* v_ref_615_; uint16_t v_optionFlags_616_; uint8_t v_suppressElabErrors_617_; uint8_t v_isRecordingDeps_618_; lean_object* v___x_619_; lean_object* v_ref_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_toCold_613_ = lean_ctor_get(v_a_610_, 0);
v_currRecDepth_614_ = lean_ctor_get(v_a_610_, 1);
v_ref_615_ = lean_ctor_get(v_a_610_, 2);
v_optionFlags_616_ = lean_ctor_get_uint16(v_a_610_, sizeof(void*)*3);
v_suppressElabErrors_617_ = lean_ctor_get_uint8(v_a_610_, sizeof(void*)*3 + 2);
v_isRecordingDeps_618_ = lean_ctor_get_uint8(v_a_610_, sizeof(void*)*3 + 3);
lean_inc(v_stx_605_);
v___x_619_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_605_);
v_ref_620_ = l_Lean_replaceRef(v_stx_605_, v_ref_615_);
lean_inc(v_currRecDepth_614_);
lean_inc_ref(v_toCold_613_);
v___x_621_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_621_, 0, v_toCold_613_);
lean_ctor_set(v___x_621_, 1, v_currRecDepth_614_);
lean_ctor_set(v___x_621_, 2, v_ref_620_);
lean_ctor_set_uint16(v___x_621_, sizeof(void*)*3, v_optionFlags_616_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*3 + 2, v_suppressElabErrors_617_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*3 + 3, v_isRecordingDeps_618_);
lean_inc(v_a_611_);
lean_inc(v_a_609_);
lean_inc_ref(v_a_608_);
lean_inc(v_a_607_);
lean_inc_ref(v_a_606_);
v___x_622_ = lean_apply_8(v_f_604_, v___x_619_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v___x_621_, v_a_611_, lean_box(0));
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_654_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_654_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_654_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_654_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_snd_627_; lean_object* v___x_628_; lean_object* v_infoState_629_; uint8_t v_enabled_630_; 
v_snd_627_ = lean_ctor_get(v_a_623_, 1);
v___x_628_ = lean_st_ref_get(v_a_611_);
v_infoState_629_ = lean_ctor_get(v___x_628_, 8);
lean_inc_ref(v_infoState_629_);
lean_dec(v___x_628_);
v_enabled_630_ = lean_ctor_get_uint8(v_infoState_629_, sizeof(void*)*3);
lean_dec_ref(v_infoState_629_);
if (v_enabled_630_ == 0)
{
lean_object* v___x_632_; 
lean_dec(v_stx_605_);
lean_dec(v_expectedType_x3f_603_);
if (v_isShared_626_ == 0)
{
v___x_632_ = v___x_625_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_623_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
lean_del_object(v___x_625_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_box(0);
v___x_636_ = 0;
lean_inc(v_snd_627_);
v___x_637_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_605_, v_snd_627_, v_expectedType_x3f_603_, v___x_634_, v___x_635_, v___x_636_, v___x_636_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v___x_637_, 0);
lean_dec(v_unused_645_);
v___x_639_ = v___x_637_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_dec(v___x_637_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_a_623_);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_623_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_623_);
v_a_646_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_637_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_637_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_605_);
lean_dec(v_expectedType_x3f_603_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___boxed(lean_object* v_00_u03b1_655_, lean_object* v_expectedType_x3f_656_, lean_object* v_f_657_, lean_object* v_stx_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(v_00_u03b1_655_, v_expectedType_x3f_656_, v_f_657_, v_stx_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(lean_object* v_inst_667_, lean_object* v_f_668_, lean_object* v_stx_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_toExpr_677_; lean_object* v_toTypeExpr_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_736_; 
v_toExpr_677_ = lean_ctor_get(v_inst_667_, 0);
v_toTypeExpr_678_ = lean_ctor_get(v_inst_667_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_inst_667_);
if (v_isSharedCheck_736_ == 0)
{
v___x_680_ = v_inst_667_;
v_isShared_681_ = v_isSharedCheck_736_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_toTypeExpr_678_);
lean_inc(v_toExpr_677_);
lean_dec(v_inst_667_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_736_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_toCold_682_; lean_object* v_currRecDepth_683_; lean_object* v_ref_684_; uint16_t v_optionFlags_685_; uint8_t v_suppressElabErrors_686_; uint8_t v_isRecordingDeps_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_ref_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_toCold_682_ = lean_ctor_get(v_a_674_, 0);
v_currRecDepth_683_ = lean_ctor_get(v_a_674_, 1);
v_ref_684_ = lean_ctor_get(v_a_674_, 2);
v_optionFlags_685_ = lean_ctor_get_uint16(v_a_674_, sizeof(void*)*3);
v_suppressElabErrors_686_ = lean_ctor_get_uint8(v_a_674_, sizeof(void*)*3 + 2);
v_isRecordingDeps_687_ = lean_ctor_get_uint8(v_a_674_, sizeof(void*)*3 + 3);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_toTypeExpr_678_);
lean_inc(v_stx_669_);
v___x_689_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_669_);
v_ref_690_ = l_Lean_replaceRef(v_stx_669_, v_ref_684_);
lean_inc(v_currRecDepth_683_);
lean_inc_ref(v_toCold_682_);
v___x_691_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_691_, 0, v_toCold_682_);
lean_ctor_set(v___x_691_, 1, v_currRecDepth_683_);
lean_ctor_set(v___x_691_, 2, v_ref_690_);
lean_ctor_set_uint16(v___x_691_, sizeof(void*)*3, v_optionFlags_685_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3 + 2, v_suppressElabErrors_686_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*3 + 3, v_isRecordingDeps_687_);
lean_inc(v_a_675_);
lean_inc(v_a_673_);
lean_inc_ref(v_a_672_);
lean_inc(v_a_671_);
lean_inc_ref(v_a_670_);
v___x_692_ = lean_apply_8(v_f_668_, v___x_689_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v___x_691_, v_a_675_, lean_box(0));
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_727_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_727_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_727_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_727_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
lean_inc(v_a_693_);
v___x_697_ = lean_apply_1(v_toExpr_677_, v_a_693_);
lean_inc_ref(v___x_697_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_697_);
lean_ctor_set(v___x_680_, 0, v_a_693_);
v___x_699_ = v___x_680_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_693_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_726_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v_infoState_701_; uint8_t v_enabled_702_; 
v___x_700_ = lean_st_ref_get(v_a_675_);
v_infoState_701_ = lean_ctor_get(v___x_700_, 8);
lean_inc_ref(v_infoState_701_);
lean_dec(v___x_700_);
v_enabled_702_ = lean_ctor_get_uint8(v_infoState_701_, sizeof(void*)*3);
lean_dec_ref(v_infoState_701_);
if (v_enabled_702_ == 0)
{
lean_object* v___x_704_; 
lean_dec_ref(v___x_697_);
lean_dec_ref_known(v___x_688_, 1);
lean_dec(v_stx_669_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_699_);
v___x_704_ = v___x_695_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; 
lean_del_object(v___x_695_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_box(0);
v___x_708_ = 0;
v___x_709_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_669_, v___x_697_, v___x_688_, v___x_706_, v___x_707_, v___x_708_, v___x_708_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_709_, 0);
lean_dec(v_unused_717_);
v___x_711_ = v___x_709_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___x_709_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_699_);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_699_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v___x_699_);
v_a_718_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_709_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_709_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref_known(v___x_688_, 1);
lean_del_object(v___x_680_);
lean_dec_ref(v_toExpr_677_);
lean_dec(v_stx_669_);
v_a_728_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_692_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_692_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg___boxed(lean_object* v_inst_737_, lean_object* v_f_738_, lean_object* v_stx_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(v_inst_737_, v_f_738_, v_stx_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(lean_object* v_00_u03b1_748_, lean_object* v_inst_749_, lean_object* v_f_750_, lean_object* v_stx_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_toExpr_759_; lean_object* v_toTypeExpr_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_818_; 
v_toExpr_759_ = lean_ctor_get(v_inst_749_, 0);
v_toTypeExpr_760_ = lean_ctor_get(v_inst_749_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_inst_749_);
if (v_isSharedCheck_818_ == 0)
{
v___x_762_ = v_inst_749_;
v_isShared_763_ = v_isSharedCheck_818_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_toTypeExpr_760_);
lean_inc(v_toExpr_759_);
lean_dec(v_inst_749_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_818_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_toCold_764_; lean_object* v_currRecDepth_765_; lean_object* v_ref_766_; uint16_t v_optionFlags_767_; uint8_t v_suppressElabErrors_768_; uint8_t v_isRecordingDeps_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_ref_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_toCold_764_ = lean_ctor_get(v_a_756_, 0);
v_currRecDepth_765_ = lean_ctor_get(v_a_756_, 1);
v_ref_766_ = lean_ctor_get(v_a_756_, 2);
v_optionFlags_767_ = lean_ctor_get_uint16(v_a_756_, sizeof(void*)*3);
v_suppressElabErrors_768_ = lean_ctor_get_uint8(v_a_756_, sizeof(void*)*3 + 2);
v_isRecordingDeps_769_ = lean_ctor_get_uint8(v_a_756_, sizeof(void*)*3 + 3);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v_toTypeExpr_760_);
lean_inc(v_stx_751_);
v___x_771_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_751_);
v_ref_772_ = l_Lean_replaceRef(v_stx_751_, v_ref_766_);
lean_inc(v_currRecDepth_765_);
lean_inc_ref(v_toCold_764_);
v___x_773_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_773_, 0, v_toCold_764_);
lean_ctor_set(v___x_773_, 1, v_currRecDepth_765_);
lean_ctor_set(v___x_773_, 2, v_ref_772_);
lean_ctor_set_uint16(v___x_773_, sizeof(void*)*3, v_optionFlags_767_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*3 + 2, v_suppressElabErrors_768_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*3 + 3, v_isRecordingDeps_769_);
lean_inc(v_a_757_);
lean_inc(v_a_755_);
lean_inc_ref(v_a_754_);
lean_inc(v_a_753_);
lean_inc_ref(v_a_752_);
v___x_774_ = lean_apply_8(v_f_750_, v___x_771_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v___x_773_, v_a_757_, lean_box(0));
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_809_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_809_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_809_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_809_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
lean_inc(v_a_775_);
v___x_779_ = lean_apply_1(v_toExpr_759_, v_a_775_);
lean_inc_ref(v___x_779_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___x_779_);
lean_ctor_set(v___x_762_, 0, v_a_775_);
v___x_781_ = v___x_762_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_775_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_808_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v_infoState_783_; uint8_t v_enabled_784_; 
v___x_782_ = lean_st_ref_get(v_a_757_);
v_infoState_783_ = lean_ctor_get(v___x_782_, 8);
lean_inc_ref(v_infoState_783_);
lean_dec(v___x_782_);
v_enabled_784_ = lean_ctor_get_uint8(v_infoState_783_, sizeof(void*)*3);
lean_dec_ref(v_infoState_783_);
if (v_enabled_784_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v___x_779_);
lean_dec_ref_known(v___x_770_, 1);
lean_dec(v_stx_751_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_781_);
v___x_786_ = v___x_777_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
lean_del_object(v___x_777_);
v___x_788_ = lean_box(0);
v___x_789_ = lean_box(0);
v___x_790_ = 0;
v___x_791_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_751_, v___x_779_, v___x_770_, v___x_788_, v___x_789_, v___x_790_, v___x_790_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_799_);
v___x_793_ = v___x_791_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_dec(v___x_791_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_781_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_781_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___x_781_);
v_a_800_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_791_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_791_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref_known(v___x_770_, 1);
lean_del_object(v___x_762_);
lean_dec_ref(v_toExpr_759_);
lean_dec(v_stx_751_);
v_a_810_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_774_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_774_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___boxed(lean_object* v_00_u03b1_819_, lean_object* v_inst_820_, lean_object* v_f_821_, lean_object* v_stx_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(v_00_u03b1_819_, v_inst_820_, v_f_821_, v_stx_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(lean_object* v_msgData_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_env_838_; uint8_t v___x_839_; lean_object* v_env_840_; lean_object* v___x_841_; lean_object* v_toCold_842_; lean_object* v_mctx_843_; lean_object* v_lctx_844_; lean_object* v_options_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_837_ = lean_st_ref_get(v___y_835_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_837_);
v___x_839_ = 0;
v_env_840_ = l_Lean_Environment_setRecordingDeps(v_env_838_, v___x_839_);
v___x_841_ = lean_st_ref_get(v___y_833_);
v_toCold_842_ = lean_ctor_get(v___y_834_, 0);
v_mctx_843_ = lean_ctor_get(v___x_841_, 0);
lean_inc_ref(v_mctx_843_);
lean_dec(v___x_841_);
v_lctx_844_ = lean_ctor_get(v___y_832_, 2);
v_options_845_ = lean_ctor_get(v_toCold_842_, 2);
lean_inc_ref(v_options_845_);
lean_inc_ref(v_lctx_844_);
v___x_846_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_846_, 0, v_env_840_);
lean_ctor_set(v___x_846_, 1, v_mctx_843_);
lean_ctor_set(v___x_846_, 2, v_lctx_844_);
lean_ctor_set(v___x_846_, 3, v_options_845_);
v___x_847_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_msgData_831_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(lean_object* v_msgData_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(lean_object* v_msg_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_ref_862_; lean_object* v___x_863_; lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
v_ref_862_ = lean_ctor_get(v___y_859_, 2);
v___x_863_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
lean_inc(v_ref_862_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_ref_862_);
lean_ctor_set(v___x_868_, 1, v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 1);
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg___boxed(lean_object* v_msg_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_879_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(lean_object* v_f_883_, lean_object* v_e_884_, lean_object* v_errMsg_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; lean_object* v___y_893_; lean_object* v___y_894_; uint8_t v___y_895_; lean_object* v___y_911_; lean_object* v_a_912_; lean_object* v___x_915_; 
v___x_891_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_inc_ref(v_f_883_);
lean_inc(v_a_889_);
lean_inc_ref(v_a_888_);
lean_inc(v_a_887_);
lean_inc_ref(v_a_886_);
lean_inc_ref(v_e_884_);
v___x_915_ = lean_apply_6(v_f_883_, v_e_884_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, lean_box(0));
if (lean_obj_tag(v___x_915_) == 0)
{
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
lean_dec_ref(v_f_883_);
return v___x_915_;
}
else
{
lean_object* v_a_916_; uint8_t v___y_918_; uint8_t v___x_933_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
v___x_933_ = l_Lean_Exception_isInterrupt(v_a_916_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; 
lean_inc(v_a_916_);
v___x_934_ = l_Lean_Exception_isRuntime(v_a_916_);
v___y_918_ = v___x_934_;
goto v___jp_917_;
}
else
{
v___y_918_ = v___x_933_;
goto v___jp_917_;
}
v___jp_917_:
{
if (v___y_918_ == 0)
{
if (lean_obj_tag(v_a_916_) == 0)
{
lean_dec_ref_known(v_a_916_, 2);
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
lean_dec_ref(v_f_883_);
return v___x_915_;
}
else
{
lean_object* v_id_919_; uint8_t v___x_920_; 
v_id_919_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_id_919_);
lean_dec_ref_known(v_a_916_, 2);
v___x_920_ = l_Lean_instBEqInternalExceptionId_beq(v___x_891_, v_id_919_);
lean_dec(v_id_919_);
if (v___x_920_ == 0)
{
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
lean_dec_ref(v_f_883_);
return v___x_915_;
}
else
{
lean_object* v___x_921_; 
lean_dec_ref_known(v___x_915_, 1);
lean_inc(v_a_889_);
lean_inc_ref(v_a_888_);
lean_inc(v_a_887_);
lean_inc_ref(v_a_886_);
lean_inc_ref(v_e_884_);
v___x_921_ = lean_whnf(v_e_884_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
lean_inc(v_a_889_);
lean_inc_ref(v_a_888_);
lean_inc(v_a_887_);
lean_inc_ref(v_a_886_);
v___x_923_ = lean_apply_6(v_f_883_, v_a_922_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, lean_box(0));
if (lean_obj_tag(v___x_923_) == 0)
{
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
return v___x_923_;
}
else
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
v___y_911_ = v___x_923_;
v_a_912_ = v_a_924_;
goto v___jp_910_;
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_f_883_);
v_a_925_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_921_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_921_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
lean_inc(v_a_925_);
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
v___y_911_ = v___x_930_;
v_a_912_ = v_a_925_;
goto v___jp_910_;
}
}
}
}
}
}
else
{
lean_dec(v_a_916_);
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
lean_dec_ref(v_f_883_);
return v___x_915_;
}
}
}
v___jp_892_:
{
if (v___y_895_ == 0)
{
if (lean_obj_tag(v___y_894_) == 0)
{
lean_dec_ref_known(v___y_894_, 2);
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
return v___y_893_;
}
else
{
lean_object* v_id_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_908_; 
v_id_896_ = lean_ctor_get(v___y_894_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___y_894_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v___y_894_, 1);
lean_dec(v_unused_909_);
v___x_898_ = v___y_894_;
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_id_896_);
lean_dec(v___y_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
uint8_t v___x_900_; 
v___x_900_ = l_Lean_instBEqInternalExceptionId_beq(v___x_891_, v_id_896_);
lean_dec(v_id_896_);
if (v___x_900_ == 0)
{
lean_del_object(v___x_898_);
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
return v___y_893_;
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec_ref(v___y_893_);
v___x_901_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1);
v___x_902_ = l_Lean_indentExpr(v_e_884_);
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 7);
lean_ctor_set(v___x_898_, 1, v___x_902_);
lean_ctor_set(v___x_898_, 0, v___x_901_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_907_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_errMsg_885_);
v___x_906_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v___x_905_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
return v___x_906_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_894_);
lean_dec_ref(v_errMsg_885_);
lean_dec_ref(v_e_884_);
return v___y_893_;
}
}
v___jp_910_:
{
uint8_t v___x_913_; 
v___x_913_ = l_Lean_Exception_isInterrupt(v_a_912_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
lean_inc_ref(v_a_912_);
v___x_914_ = l_Lean_Exception_isRuntime(v_a_912_);
v___y_893_ = v___y_911_;
v___y_894_ = v_a_912_;
v___y_895_ = v___x_914_;
goto v___jp_892_;
}
else
{
v___y_893_ = v___y_911_;
v___y_894_ = v_a_912_;
v___y_895_ = v___x_913_;
goto v___jp_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___boxed(lean_object* v_f_935_, lean_object* v_e_936_, lean_object* v_errMsg_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_935_, v_e_936_, v_errMsg_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(lean_object* v_00_u03b1_944_, lean_object* v_f_945_, lean_object* v_e_946_, lean_object* v_errMsg_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_945_, v_e_946_, v_errMsg_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___boxed(lean_object* v_00_u03b1_954_, lean_object* v_f_955_, lean_object* v_e_956_, lean_object* v_errMsg_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(v_00_u03b1_954_, v_f_955_, v_e_956_, v_errMsg_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(lean_object* v_00_u03b1_964_, lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___boxed(lean_object* v_00_u03b1_972_, lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(v_00_u03b1_972_, v_msg_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object* v_item_980_){
_start:
{
lean_object* v_optionComps_981_; uint8_t v___x_982_; 
v_optionComps_981_ = lean_ctor_get(v_item_980_, 5);
v___x_982_ = l_List_isEmpty___redArg(v_optionComps_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(lean_object* v_item_983_){
_start:
{
uint8_t v_res_984_; lean_object* v_r_985_; 
v_res_984_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_983_);
lean_dec_ref(v_item_983_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root(lean_object* v_item_986_){
_start:
{
lean_object* v_optionComps_987_; 
v_optionComps_987_ = lean_ctor_get(v_item_986_, 5);
if (lean_obj_tag(v_optionComps_987_) == 1)
{
lean_object* v_head_988_; 
v_head_988_ = lean_ctor_get(v_optionComps_987_, 0);
lean_inc(v_head_988_);
return v_head_988_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_box(0);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(lean_object* v_item_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_990_);
lean_dec_ref(v_item_990_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object* v_item_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_992_);
v___x_994_ = l_Lean_Syntax_getId(v___x_993_);
lean_dec(v___x_993_);
if (lean_obj_tag(v___x_994_) == 1)
{
lean_object* v_str_995_; 
v_str_995_ = lean_ctor_get(v___x_994_, 1);
lean_inc_ref(v_str_995_);
lean_dec_ref_known(v___x_994_, 2);
return v_str_995_;
}
else
{
lean_object* v___x_996_; 
lean_dec(v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(lean_object* v_item_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_997_);
lean_dec_ref(v_item_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(lean_object* v_item_999_){
_start:
{
lean_object* v_prevOptionComps_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_prevOptionComps_1000_ = lean_ctor_get(v_item_999_, 6);
v___x_1001_ = lean_unsigned_to_nat(0u);
v___x_1002_ = l_List_get_x3fInternal___redArg(v_prevOptionComps_1000_, v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(lean_object* v_item_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(v_item_1003_);
lean_dec_ref(v_item_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(lean_object* v_item_1005_){
_start:
{
lean_object* v_prevOptionComps_1006_; 
v_prevOptionComps_1006_ = lean_ctor_get(v_item_1005_, 6);
if (lean_obj_tag(v_prevOptionComps_1006_) == 1)
{
lean_object* v_head_1007_; 
v_head_1007_ = lean_ctor_get(v_prevOptionComps_1006_, 0);
lean_inc(v_head_1007_);
return v_head_1007_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_box(0);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(lean_object* v_item_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_1009_);
lean_dec_ref(v_item_1009_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
if (lean_obj_tag(v_x_1012_) == 0)
{
return v_x_1011_;
}
else
{
lean_object* v_head_1013_; lean_object* v_tail_1014_; lean_object* v___x_1015_; 
v_head_1013_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_head_1013_);
v_tail_1014_ = lean_ctor_get(v_x_1012_, 1);
lean_inc(v_tail_1014_);
lean_dec_ref_known(v_x_1012_, 2);
v___x_1015_ = l_Lean_Name_appendCore(v_x_1011_, v_head_1013_);
lean_dec(v_x_1011_);
v_x_1011_ = v___x_1015_;
v_x_1012_ = v_tail_1014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
if (lean_obj_tag(v_a_1017_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = l_List_reverse___redArg(v_a_1018_);
return v___x_1019_;
}
else
{
lean_object* v_head_1020_; lean_object* v_tail_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1030_; 
v_head_1020_ = lean_ctor_get(v_a_1017_, 0);
v_tail_1021_ = lean_ctor_get(v_a_1017_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_1017_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1023_ = v_a_1017_;
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_tail_1021_);
lean_inc(v_head_1020_);
lean_dec(v_a_1017_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = l_Lean_Syntax_getId(v_head_1020_);
lean_dec(v_head_1020_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v_a_1018_);
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_1018_);
v___x_1027_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
v_a_1017_ = v_tail_1021_;
v_a_1018_ = v___x_1027_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(lean_object* v_item_1031_){
_start:
{
lean_object* v_optionComps_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_optionComps_1032_ = lean_ctor_get(v_item_1031_, 5);
lean_inc(v_optionComps_1032_);
lean_dec_ref(v_item_1031_);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_box(0);
v___x_1035_ = l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(v_optionComps_1032_, v___x_1034_);
v___x_1036_ = l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(v___x_1033_, v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object* v_item_1037_){
_start:
{
lean_object* v_ref_1038_; lean_object* v_option_1039_; lean_object* v_value_1040_; lean_object* v_bool_x3f_1041_; lean_object* v_origOptionName_1042_; lean_object* v_optionComps_1043_; lean_object* v_prevOptionComps_1044_; lean_object* v___y_1046_; 
v_ref_1038_ = lean_ctor_get(v_item_1037_, 0);
lean_inc(v_ref_1038_);
v_option_1039_ = lean_ctor_get(v_item_1037_, 1);
lean_inc(v_option_1039_);
v_value_1040_ = lean_ctor_get(v_item_1037_, 2);
lean_inc(v_value_1040_);
v_bool_x3f_1041_ = lean_ctor_get(v_item_1037_, 3);
lean_inc(v_bool_x3f_1041_);
v_origOptionName_1042_ = lean_ctor_get(v_item_1037_, 4);
lean_inc(v_origOptionName_1042_);
v_optionComps_1043_ = lean_ctor_get(v_item_1037_, 5);
v_prevOptionComps_1044_ = lean_ctor_get(v_item_1037_, 6);
lean_inc(v_prevOptionComps_1044_);
if (lean_obj_tag(v_optionComps_1043_) == 0)
{
v___y_1046_ = v_optionComps_1043_;
goto v___jp_1045_;
}
else
{
lean_object* v_tail_1063_; 
v_tail_1063_ = lean_ctor_get(v_optionComps_1043_, 1);
lean_inc(v_tail_1063_);
v___y_1046_ = v_tail_1063_;
goto v___jp_1045_;
}
v___jp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v___x_1047_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1037_);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_item_1037_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; lean_object* v_unused_1057_; lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; 
v_unused_1056_ = lean_ctor_get(v_item_1037_, 6);
lean_dec(v_unused_1056_);
v_unused_1057_ = lean_ctor_get(v_item_1037_, 5);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_item_1037_, 4);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_item_1037_, 3);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_item_1037_, 2);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_item_1037_, 1);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v_item_1037_, 0);
lean_dec(v_unused_1062_);
v___x_1049_ = v_item_1037_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v_item_1037_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1047_);
lean_ctor_set(v___x_1051_, 1, v_prevOptionComps_1044_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 6, v___x_1051_);
lean_ctor_set(v___x_1049_, 5, v___y_1046_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_ref_1038_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_option_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_value_1040_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_bool_x3f_1041_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_origOptionName_1042_);
lean_ctor_set(v_reuseFailAlloc_1054_, 5, v___y_1046_);
lean_ctor_set(v_reuseFailAlloc_1054_, 6, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(1);
v___x_1065_ = l_Lean_MessageData_ofFormat(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2));
v___x_1070_ = l_Lean_MessageData_ofFormat(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
return v_x_1071_;
}
else
{
lean_object* v_head_1073_; lean_object* v_tail_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1096_; 
v_head_1073_ = lean_ctor_get(v_x_1072_, 0);
v_tail_1074_ = lean_ctor_get(v_x_1072_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1076_ = v_x_1072_;
v_isShared_1077_ = v_isSharedCheck_1096_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_tail_1074_);
lean_inc(v_head_1073_);
lean_dec(v_x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1096_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_before_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1094_; 
v_before_1078_ = lean_ctor_get(v_head_1073_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_head_1073_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_head_1073_, 1);
lean_dec(v_unused_1095_);
v___x_1080_ = v_head_1073_;
v_isShared_1081_ = v_isSharedCheck_1094_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_before_1078_);
lean_dec(v_head_1073_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1094_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 7);
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
lean_ctor_set(v___x_1080_, 0, v_x_1071_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_x_1071_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 7);
lean_ctor_set(v___x_1076_, 1, v___x_1085_);
lean_ctor_set(v___x_1076_, 0, v___x_1084_);
v___x_1087_ = v___x_1076_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = l_Lean_MessageData_ofSyntax(v_before_1078_);
v___x_1089_ = l_Lean_indentD(v___x_1088_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1087_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v_x_1071_ = v___x_1090_;
v_x_1072_ = v_tail_1074_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(lean_object* v_opts_1097_, lean_object* v_opt_1098_){
_start:
{
lean_object* v_name_1099_; lean_object* v_defValue_1100_; lean_object* v_map_1101_; lean_object* v___x_1102_; 
v_name_1099_ = lean_ctor_get(v_opt_1098_, 0);
v_defValue_1100_ = lean_ctor_get(v_opt_1098_, 1);
v_map_1101_ = lean_ctor_get(v_opts_1097_, 0);
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1101_, v_name_1099_);
if (lean_obj_tag(v___x_1102_) == 0)
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_unbox(v_defValue_1100_);
return v___x_1103_;
}
else
{
lean_object* v_val_1104_; 
v_val_1104_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v___x_1102_, 1);
if (lean_obj_tag(v_val_1104_) == 1)
{
uint8_t v_v_1105_; 
v_v_1105_ = lean_ctor_get_uint8(v_val_1104_, 0);
lean_dec_ref_known(v_val_1104_, 0);
return v_v_1105_;
}
else
{
uint8_t v___x_1106_; 
lean_dec(v_val_1104_);
v___x_1106_ = lean_unbox(v_defValue_1100_);
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_1107_, lean_object* v_opt_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_1107_, v_opt_1108_);
lean_dec_ref(v_opt_1108_);
lean_dec_ref(v_opts_1107_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_1115_ = l_Lean_MessageData_ofFormat(v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_1116_, lean_object* v_macroStack_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1118_);
v___x_1121_ = l_Lean_Elab_pp_macroStack;
v___x_1122_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_1120_, v___x_1121_);
lean_dec_ref(v___x_1120_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec(v_macroStack_1117_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_msgData_1116_);
return v___x_1123_;
}
else
{
if (lean_obj_tag(v_macroStack_1117_) == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_msgData_1116_);
return v___x_1124_;
}
else
{
lean_object* v_head_1125_; lean_object* v_after_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1141_; 
v_head_1125_ = lean_ctor_get(v_macroStack_1117_, 0);
lean_inc(v_head_1125_);
v_after_1126_ = lean_ctor_get(v_head_1125_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_head_1125_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v_head_1125_, 0);
lean_dec(v_unused_1142_);
v___x_1128_ = v_head_1125_;
v_isShared_1129_ = v_isSharedCheck_1141_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_after_1126_);
lean_dec(v_head_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1141_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 7);
lean_ctor_set(v___x_1128_, 1, v___x_1130_);
lean_ctor_set(v___x_1128_, 0, v_msgData_1116_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_msgData_1116_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_msgData_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1133_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofSyntax(v_after_1126_);
v___x_1136_ = l_Lean_indentD(v___x_1135_);
v_msgData_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1137_, 0, v___x_1134_);
lean_ctor_set(v_msgData_1137_, 1, v___x_1136_);
v___x_1138_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(v_msgData_1137_, v_macroStack_1117_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_1143_, lean_object* v_macroStack_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1143_, v_macroStack_1144_, v___y_1145_);
lean_dec_ref(v___y_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(lean_object* v_msg_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_ref_1156_; lean_object* v_macroStack_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
v_ref_1156_ = lean_ctor_get(v___y_1153_, 2);
v_macroStack_1157_ = lean_ctor_get(v___y_1149_, 1);
v___x_1158_ = l_Lean_Elab_getBetterRef(v_ref_1156_, v_macroStack_1157_);
v___x_1159_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_1148_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v___x_1159_);
lean_inc(v_macroStack_1157_);
v___x_1161_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_1160_, v_macroStack_1157_, v___y_1153_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1158_);
lean_ctor_set(v___x_1166_, 1, v_a_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 1);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(lean_object* v_ref_1180_, lean_object* v_msg_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_toCold_1189_; lean_object* v_currRecDepth_1190_; lean_object* v_ref_1191_; uint16_t v_optionFlags_1192_; uint8_t v_suppressElabErrors_1193_; uint8_t v_isRecordingDeps_1194_; lean_object* v_ref_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_toCold_1189_ = lean_ctor_get(v___y_1186_, 0);
v_currRecDepth_1190_ = lean_ctor_get(v___y_1186_, 1);
v_ref_1191_ = lean_ctor_get(v___y_1186_, 2);
v_optionFlags_1192_ = lean_ctor_get_uint16(v___y_1186_, sizeof(void*)*3);
v_suppressElabErrors_1193_ = lean_ctor_get_uint8(v___y_1186_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1194_ = lean_ctor_get_uint8(v___y_1186_, sizeof(void*)*3 + 3);
v_ref_1195_ = l_Lean_replaceRef(v_ref_1180_, v_ref_1191_);
lean_inc(v_currRecDepth_1190_);
lean_inc_ref(v_toCold_1189_);
v___x_1196_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1196_, 0, v_toCold_1189_);
lean_ctor_set(v___x_1196_, 1, v_currRecDepth_1190_);
lean_ctor_set(v___x_1196_, 2, v_ref_1195_);
lean_ctor_set_uint16(v___x_1196_, sizeof(void*)*3, v_optionFlags_1192_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*3 + 2, v_suppressElabErrors_1193_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*3 + 3, v_isRecordingDeps_1194_);
v___x_1197_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___x_1196_, v___y_1187_);
lean_dec_ref_known(v___x_1196_, 3);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(lean_object* v_ref_1198_, lean_object* v_msg_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1198_, v_msg_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v_ref_1198_);
return v_res_1207_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2));
v___x_1213_ = l_Lean_stringToMessageData(v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object* v_item_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_bool_x3f_1222_; 
v_bool_x3f_1222_ = lean_ctor_get(v_item_1214_, 3);
if (lean_obj_tag(v_bool_x3f_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_item_1214_);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v_option_1225_; lean_object* v_origOptionName_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_option_1225_ = lean_ctor_get(v_item_1214_, 1);
lean_inc(v_option_1225_);
v_origOptionName_1226_ = lean_ctor_get(v_item_1214_, 4);
lean_inc(v_origOptionName_1226_);
lean_dec_ref(v_item_1214_);
v___x_1227_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1);
v___x_1228_ = l_Lean_MessageData_ofName(v_origOptionName_1226_);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1225_, v___x_1231_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_option_1225_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(lean_object* v_item_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(lean_object* v_00_u03b1_1242_, lean_object* v_ref_1243_, lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1243_, v_msg_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_ref_1254_, lean_object* v_msg_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(v_00_u03b1_1253_, v_ref_1254_, v_msg_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v_ref_1254_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(lean_object* v_00_u03b1_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_msg_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_1274_, v_msg_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(lean_object* v_msgData_1284_, lean_object* v_macroStack_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1284_, v_macroStack_1285_, v___y_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1294_, lean_object* v_macroStack_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_1294_, v_macroStack_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1303_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object* v_item_1313_, lean_object* v_structName_x3f_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_option_1322_; lean_object* v_origOptionName_1323_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1332_; uint8_t v___x_1341_; 
v_option_1322_ = lean_ctor_get(v_item_1313_, 1);
lean_inc(v_option_1322_);
v_origOptionName_1323_ = lean_ctor_get(v_item_1313_, 4);
lean_inc(v_origOptionName_1323_);
lean_dec_ref(v_item_1313_);
v___x_1341_ = l_Lean_Name_isAnonymous(v_origOptionName_1323_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1342_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1343_ = l_Lean_MessageData_ofName(v_origOptionName_1323_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___y_1332_ = v___x_1346_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v_origOptionName_1323_);
v___x_1347_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1332_ = v___x_1347_;
goto v___jp_1331_;
}
v___jp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___y_1325_);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___y_1326_);
v___x_1330_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1322_, v___x_1329_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_option_1322_);
return v___x_1330_;
}
v___jp_1331_:
{
if (lean_obj_tag(v_structName_x3f_1314_) == 1)
{
lean_object* v_val_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_val_1333_ = lean_ctor_get(v_structName_x3f_1314_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_structName_x3f_1314_, 1);
v___x_1334_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1335_ = 0;
v___x_1336_ = l_Lean_MessageData_ofConstName(v_val_1333_, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1334_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___y_1325_ = v___y_1332_;
v___y_1326_ = v___x_1339_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1340_; 
lean_dec(v_structName_x3f_1314_);
v___x_1340_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1325_ = v___y_1332_;
v___y_1326_ = v___x_1340_;
goto v___jp_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___boxed(lean_object* v_item_1348_, lean_object* v_structName_x3f_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1348_, v_structName_x3f_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(lean_object* v_00_u03b1_1358_, lean_object* v_item_1359_, lean_object* v_structName_x3f_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1359_, v_structName_x3f_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_item_1370_, lean_object* v_structName_x3f_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(v_00_u03b1_1369_, v_item_1370_, v_structName_x3f_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(lean_object* v_item_1386_, lean_object* v_structName_x3f_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_option_1395_; lean_object* v_origOptionName_1396_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1407_; uint8_t v___x_1416_; 
v_option_1395_ = lean_ctor_get(v_item_1386_, 1);
lean_inc(v_option_1395_);
v_origOptionName_1396_ = lean_ctor_get(v_item_1386_, 4);
lean_inc(v_origOptionName_1396_);
lean_dec_ref(v_item_1386_);
v___x_1416_ = l_Lean_Name_isAnonymous(v_origOptionName_1396_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1417_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1418_ = l_Lean_MessageData_ofName(v_origOptionName_1396_);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___y_1407_ = v___x_1421_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1422_; 
lean_dec(v_origOptionName_1396_);
v___x_1422_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1407_ = v___x_1422_;
goto v___jp_1406_;
}
v___jp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v___y_1398_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v___y_1399_);
v___x_1403_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
v___x_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1402_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1395_, v___x_1404_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_option_1395_);
return v___x_1405_;
}
v___jp_1406_:
{
if (lean_obj_tag(v_structName_x3f_1387_) == 1)
{
lean_object* v_val_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_val_1408_ = lean_ctor_get(v_structName_x3f_1387_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v_structName_x3f_1387_, 1);
v___x_1409_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1410_ = 0;
v___x_1411_ = l_Lean_MessageData_ofConstName(v_val_1408_, v___x_1410_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1409_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___x_1414_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1415_; 
lean_dec(v_structName_x3f_1387_);
v___x_1415_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___x_1415_;
goto v___jp_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___boxed(lean_object* v_item_1423_, lean_object* v_structName_x3f_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1423_, v_structName_x3f_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(lean_object* v_00_u03b1_1433_, lean_object* v_item_1434_, lean_object* v_structName_x3f_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1434_, v_structName_x3f_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_item_1445_, lean_object* v_structName_x3f_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(v_00_u03b1_1444_, v_item_1445_, v_structName_x3f_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
return v_res_1454_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
lean_ctor_set(v___x_1461_, 2, v___x_1460_);
lean_ctor_set(v___x_1461_, 3, v___x_1460_);
lean_ctor_set(v___x_1461_, 4, v___x_1459_);
lean_ctor_set(v___x_1461_, 5, v___x_1459_);
lean_ctor_set(v___x_1461_, 6, v___x_1459_);
lean_ctor_set(v___x_1461_, 7, v___x_1459_);
lean_ctor_set(v___x_1461_, 8, v___x_1459_);
lean_ctor_set(v___x_1461_, 9, v___x_1459_);
lean_ctor_set(v___x_1461_, 10, v___x_1459_);
lean_ctor_set(v___x_1461_, 11, v___x_1458_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_unsigned_to_nat(32u);
v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1465_ = ((size_t)5ULL);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_unsigned_to_nat(32u);
v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
v___x_1469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1470_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v___x_1468_);
lean_ctor_set(v___x_1470_, 2, v___x_1466_);
lean_ctor_set(v___x_1470_, 3, v___x_1466_);
lean_ctor_set_usize(v___x_1470_, 4, v___x_1465_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_box(1);
v___x_1472_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
lean_ctor_set(v___x_1474_, 2, v___x_1471_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1496_, lean_object* v_declHint_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_env_1502_; uint8_t v___x_1503_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_st_ref_get(v___y_1498_);
v_env_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_env_1502_);
lean_dec(v___x_1501_);
v___x_1503_ = l_Lean_Name_isAnonymous(v_declHint_1497_);
if (v___x_1503_ == 0)
{
uint8_t v_isExporting_1504_; 
v_isExporting_1504_ = lean_ctor_get_uint8(v_env_1502_, sizeof(void*)*13);
if (v_isExporting_1504_ == 0)
{
lean_object* v___x_1505_; 
lean_dec_ref(v_env_1502_);
lean_dec(v_declHint_1497_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_msg_1496_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
lean_inc_ref(v_env_1502_);
v___x_1506_ = l_Lean_Environment_setExporting(v_env_1502_, v___x_1503_);
lean_inc(v_declHint_1497_);
lean_inc_ref(v___x_1506_);
v___x_1507_ = l_Lean_Environment_contains(v___x_1506_, v_declHint_1497_, v_isExporting_1504_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_dec_ref(v___x_1506_);
lean_dec_ref(v_env_1502_);
lean_dec(v_declHint_1497_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_msg_1496_);
return v___x_1508_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_c_1514_; lean_object* v___x_1515_; 
v___x_1509_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1510_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1511_ = l_Lean_Options_empty;
v___x_1512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1506_);
lean_ctor_set(v___x_1512_, 1, v___x_1509_);
lean_ctor_set(v___x_1512_, 2, v___x_1510_);
lean_ctor_set(v___x_1512_, 3, v___x_1511_);
lean_inc(v_declHint_1497_);
v___x_1513_ = l_Lean_MessageData_ofConstName(v_declHint_1497_, v___x_1503_);
v_c_1514_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1514_, 0, v___x_1512_);
lean_ctor_set(v_c_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1502_, v_declHint_1497_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v_env_1502_);
lean_dec(v_declHint_1497_);
v___x_1516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v_c_1514_);
v___x_1518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_MessageData_note(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_msg_1496_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
else
{
lean_object* v_val_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1557_; 
v_val_1523_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1525_ = v___x_1515_;
v_isShared_1526_ = v_isSharedCheck_1557_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_val_1523_);
lean_dec(v___x_1515_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1557_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v_moduleNames_1528_; lean_object* v_mod_1529_; uint8_t v___x_1530_; 
v___x_1527_ = l_Lean_Environment_header(v_env_1502_);
lean_dec_ref(v_env_1502_);
v_moduleNames_1528_ = lean_ctor_get(v___x_1527_, 4);
lean_inc_ref(v_moduleNames_1528_);
lean_dec_ref(v___x_1527_);
v_mod_1529_ = lean_array_get(v___x_1500_, v_moduleNames_1528_, v_val_1523_);
lean_dec(v_val_1523_);
lean_dec_ref(v_moduleNames_1528_);
v___x_1530_ = l_Lean_isPrivateName(v_declHint_1497_);
lean_dec(v_declHint_1497_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_c_1514_);
v___x_1533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = l_Lean_MessageData_ofName(v_mod_1529_);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_MessageData_note(v___x_1538_);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_msg_1496_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1540_);
v___x_1542_ = v___x_1525_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1544_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v_c_1514_);
v___x_1546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_MessageData_ofName(v_mod_1529_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_MessageData_note(v___x_1551_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_msg_1496_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1553_);
v___x_1555_ = v___x_1525_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1558_; 
lean_dec_ref(v_env_1502_);
lean_dec(v_declHint_1497_);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_msg_1496_);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1559_, lean_object* v_declHint_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1559_, v_declHint_1560_, v___y_1561_);
lean_dec(v___y_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_1564_, lean_object* v_declHint_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1583_; 
v___x_1573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1564_, v_declHint_1565_, v___y_1571_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1583_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1583_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1578_ = l_Lean_unknownIdentifierMessageTag;
v___x_1579_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_a_1574_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1579_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_1584_, lean_object* v_declHint_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1584_, v_declHint_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1594_, lean_object* v_msg_1595_, lean_object* v_declHint_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; lean_object* v_a_1605_; lean_object* v___x_1606_; 
v___x_1604_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1595_, v_declHint_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1594_, v_a_1605_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1607_, lean_object* v_msg_1608_, lean_object* v_declHint_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1607_, v_msg_1608_, v_declHint_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v_ref_1607_);
return v_res_1617_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_1621_, lean_object* v_constName_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1630_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1631_ = 0;
lean_inc(v_constName_1622_);
v___x_1632_ = l_Lean_MessageData_ofConstName(v_constName_1622_, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1630_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1621_, v___x_1635_, v_constName_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1637_, lean_object* v_constName_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1637_, v_constName_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v_ref_1637_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_ref_1655_; lean_object* v___x_1656_; 
v_ref_1655_ = lean_ctor_get(v___y_1652_, 2);
v___x_1656_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1655_, v_constName_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object* v_constName_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v_env_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; 
v___x_1674_ = lean_st_ref_get(v___y_1672_);
v_env_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc_ref(v_env_1675_);
lean_dec(v___x_1674_);
v___x_1676_ = 0;
lean_inc(v_constName_1666_);
v___x_1677_ = l_Lean_Environment_findConstVal_x3f(v_env_1675_, v_constName_1666_, v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1678_;
}
else
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_constName_1666_);
v_val_1679_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1677_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v___x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_val_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
if (lean_obj_tag(v_a_1696_) == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = l_List_reverse___redArg(v_a_1697_);
return v___x_1698_;
}
else
{
lean_object* v_head_1699_; lean_object* v_tail_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1709_; 
v_head_1699_ = lean_ctor_get(v_a_1696_, 0);
v_tail_1700_ = lean_ctor_get(v_a_1696_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_a_1696_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1702_ = v_a_1696_;
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_tail_1700_);
lean_inc(v_head_1699_);
lean_dec(v_a_1696_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = l_Lean_mkLevelParam(v_head_1699_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_a_1697_);
lean_ctor_set(v___x_1702_, 0, v___x_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_a_1697_);
v___x_1706_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
v_a_1696_ = v_tail_1700_;
v_a_1697_ = v___x_1706_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object* v_constName_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
lean_inc(v_constName_1710_);
v___x_1718_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1730_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_levelParams_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v_levelParams_1723_ = lean_ctor_get(v_a_1719_, 1);
lean_inc(v_levelParams_1723_);
lean_dec(v_a_1719_);
v___x_1724_ = lean_box(0);
v___x_1725_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_1723_, v___x_1724_);
v___x_1726_ = l_Lean_mkConst(v_constName_1710_, v___x_1725_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1726_);
v___x_1728_ = v___x_1721_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_constName_1710_);
v_a_1731_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1718_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1718_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object* v_constName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v_infoState_1752_; uint8_t v_enabled_1753_; 
v___x_1751_ = lean_st_ref_get(v___y_1749_);
v_infoState_1752_ = lean_ctor_get(v___x_1751_, 8);
lean_inc_ref(v_infoState_1752_);
lean_dec(v___x_1751_);
v_enabled_1753_ = lean_ctor_get_uint8(v_infoState_1752_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1752_);
if (v_enabled_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec_ref(v_t_1748_);
v___x_1754_ = lean_box(0);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v_infoState_1757_; lean_object* v_env_1758_; lean_object* v_nextMacroScope_1759_; lean_object* v_ngen_1760_; lean_object* v_auxDeclNGen_1761_; lean_object* v_traceState_1762_; lean_object* v_cache_1763_; lean_object* v_recordedDeps_1764_; lean_object* v_messages_1765_; lean_object* v_snapshotTasks_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1788_; 
v___x_1756_ = lean_st_ref_take(v___y_1749_);
v_infoState_1757_ = lean_ctor_get(v___x_1756_, 8);
v_env_1758_ = lean_ctor_get(v___x_1756_, 0);
v_nextMacroScope_1759_ = lean_ctor_get(v___x_1756_, 1);
v_ngen_1760_ = lean_ctor_get(v___x_1756_, 2);
v_auxDeclNGen_1761_ = lean_ctor_get(v___x_1756_, 3);
v_traceState_1762_ = lean_ctor_get(v___x_1756_, 4);
v_cache_1763_ = lean_ctor_get(v___x_1756_, 5);
v_recordedDeps_1764_ = lean_ctor_get(v___x_1756_, 6);
v_messages_1765_ = lean_ctor_get(v___x_1756_, 7);
v_snapshotTasks_1766_ = lean_ctor_get(v___x_1756_, 9);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1768_ = v___x_1756_;
v_isShared_1769_ = v_isSharedCheck_1788_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snapshotTasks_1766_);
lean_inc(v_infoState_1757_);
lean_inc(v_messages_1765_);
lean_inc(v_recordedDeps_1764_);
lean_inc(v_cache_1763_);
lean_inc(v_traceState_1762_);
lean_inc(v_auxDeclNGen_1761_);
lean_inc(v_ngen_1760_);
lean_inc(v_nextMacroScope_1759_);
lean_inc(v_env_1758_);
lean_dec(v___x_1756_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1788_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
uint8_t v_enabled_1770_; lean_object* v_assignment_1771_; lean_object* v_lazyAssignment_1772_; lean_object* v_trees_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1787_; 
v_enabled_1770_ = lean_ctor_get_uint8(v_infoState_1757_, sizeof(void*)*3);
v_assignment_1771_ = lean_ctor_get(v_infoState_1757_, 0);
v_lazyAssignment_1772_ = lean_ctor_get(v_infoState_1757_, 1);
v_trees_1773_ = lean_ctor_get(v_infoState_1757_, 2);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_infoState_1757_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1775_ = v_infoState_1757_;
v_isShared_1776_ = v_isSharedCheck_1787_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_trees_1773_);
lean_inc(v_lazyAssignment_1772_);
lean_inc(v_assignment_1771_);
lean_dec(v_infoState_1757_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1787_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_PersistentArray_push___redArg(v_trees_1773_, v_t_1748_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 2, v___x_1778_);
v___x_1780_ = v___x_1775_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_assignment_1771_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_lazyAssignment_1772_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v___x_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3, v_enabled_1770_);
v___x_1780_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 8, v___x_1780_);
v___x_1782_ = v___x_1768_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_env_1758_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_nextMacroScope_1759_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_ngen_1760_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_auxDeclNGen_1761_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_traceState_1762_);
lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_cache_1763_);
lean_ctor_set(v_reuseFailAlloc_1785_, 6, v_recordedDeps_1764_);
lean_ctor_set(v_reuseFailAlloc_1785_, 7, v_messages_1765_);
lean_ctor_set(v_reuseFailAlloc_1785_, 8, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1785_, 9, v_snapshotTasks_1766_);
v___x_1782_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_st_ref_put(v___y_1749_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1777_);
return v___x_1784_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1789_, v___y_1790_);
lean_dec(v___y_1790_);
return v_res_1792_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_unsigned_to_nat(32u);
v___x_1794_ = lean_mk_empty_array_with_capacity(v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1796_ = ((size_t)5ULL);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_unsigned_to_nat(32u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
v___x_1800_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
v___x_1801_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
lean_ctor_set(v___x_1801_, 2, v___x_1797_);
lean_ctor_set(v___x_1801_, 3, v___x_1797_);
lean_ctor_set_usize(v___x_1801_, 4, v___x_1796_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object* v_t_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v_infoState_1811_; uint8_t v_enabled_1812_; 
v___x_1810_ = lean_st_ref_get(v___y_1808_);
v_infoState_1811_ = lean_ctor_get(v___x_1810_, 8);
lean_inc_ref(v_infoState_1811_);
lean_dec(v___x_1810_);
v_enabled_1812_ = lean_ctor_get_uint8(v_infoState_1811_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1811_);
if (v_enabled_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec_ref(v_t_1802_);
v___x_1813_ = lean_box(0);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
v___x_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_t_1802_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_1816_, v___y_1808_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object* v_t_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object* v_stx_1827_, lean_object* v_n_1828_, lean_object* v_expectedType_x3f_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_1828_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v_stx_1827_);
v___x_1841_ = l_Lean_LocalContext_empty;
v___x_1842_ = 0;
v___x_1843_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1843_, 0, v___x_1840_);
lean_ctor_set(v___x_1843_, 1, v___x_1841_);
lean_ctor_set(v___x_1843_, 2, v_expectedType_x3f_1829_);
lean_ctor_set(v___x_1843_, 3, v_a_1838_);
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*4, v___x_1842_);
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*4 + 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
v___x_1845_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1844_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
return v___x_1845_;
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_expectedType_x3f_1829_);
lean_dec(v_stx_1827_);
v_a_1846_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1837_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1837_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object* v_stx_1854_, lean_object* v_n_1855_, lean_object* v_expectedType_x3f_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1854_, v_n_1855_, v_expectedType_x3f_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object* v_item_1865_, lean_object* v_projFn_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v_infoState_1875_; uint8_t v_enabled_1876_; 
v___x_1874_ = lean_st_ref_get(v_a_1872_);
v_infoState_1875_ = lean_ctor_get(v___x_1874_, 8);
lean_inc_ref(v_infoState_1875_);
lean_dec(v___x_1874_);
v_enabled_1876_ = lean_ctor_get_uint8(v_infoState_1875_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1875_);
if (v_enabled_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v_projFn_1866_);
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; lean_object* v_env_1880_; uint8_t v___x_1881_; 
v___x_1879_ = lean_st_ref_get(v_a_1872_);
v_env_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc_ref(v_env_1880_);
lean_dec(v___x_1879_);
lean_inc(v_projFn_1866_);
v___x_1881_ = l_Lean_Environment_contains(v_env_1880_, v_projFn_1866_, v_enabled_1876_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v_projFn_1866_);
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1865_);
v___x_1885_ = lean_box(0);
v___x_1886_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_1884_, v_projFn_1866_, v___x_1885_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object* v_item_1887_, lean_object* v_projFn_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1887_, v_projFn_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec_ref(v_item_1887_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object* v_t_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1897_, v___y_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1915_, lean_object* v_constName_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_constName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1925_, v_constName_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_1935_, lean_object* v_ref_1936_, lean_object* v_constName_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1936_, v_constName_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_ref_1947_, lean_object* v_constName_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_1946_, v_ref_1947_, v_constName_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v_ref_1947_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1957_, lean_object* v_ref_1958_, lean_object* v_msg_1959_, lean_object* v_declHint_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1958_, v_msg_1959_, v_declHint_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1969_, lean_object* v_ref_1970_, lean_object* v_msg_1971_, lean_object* v_declHint_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1969_, v_ref_1970_, v_msg_1971_, v_declHint_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v_ref_1970_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_1981_, lean_object* v_declHint_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1981_, v_declHint_1982_, v___y_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1991_, lean_object* v_declHint_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_1991_, v_declHint_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object* v_info_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_info_2001_);
v___x_2010_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_2009_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(lean_object* v_info_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2019_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2022_ = lean_box(1);
v___x_2023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2024_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_2025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v___x_2023_);
lean_ctor_set(v___x_2025_, 2, v___x_2022_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object* v_item_2026_, lean_object* v_structName_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v_infoState_2036_; uint8_t v_enabled_2037_; 
v___x_2035_ = lean_st_ref_get(v_a_2033_);
v_infoState_2036_ = lean_ctor_get(v___x_2035_, 8);
lean_inc_ref(v_infoState_2036_);
lean_dec(v___x_2035_);
v_enabled_2037_ = lean_ctor_get_uint8(v_infoState_2036_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2036_);
if (v_enabled_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_structName_2027_);
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v_env_2041_; uint8_t v___x_2042_; 
v___x_2040_ = lean_st_ref_get(v_a_2033_);
v_env_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc_ref(v_env_2041_);
lean_dec(v___x_2040_);
lean_inc(v_structName_2027_);
v___x_2042_ = l_Lean_Environment_contains(v_env_2041_, v_structName_2027_, v_enabled_2037_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec(v_structName_2027_);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2045_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_2026_);
v___x_2046_ = l_Lean_Syntax_getId(v___x_2045_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2045_);
lean_ctor_set(v___x_2049_, 1, v___x_2047_);
lean_ctor_set(v___x_2049_, 2, v___x_2048_);
lean_ctor_set(v___x_2049_, 3, v_structName_2027_);
v___x_2050_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2049_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object* v_item_2051_, lean_object* v_structName_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2051_, v_structName_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec_ref(v_item_2051_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object* v_cfg_2061_, lean_object* v_withRef_2062_, lean_object* v___x_2063_, lean_object* v_oldRef_2064_){
_start:
{
lean_object* v_ref_2065_; lean_object* v___x_2066_; 
v_ref_2065_ = l_Lean_replaceRef(v_cfg_2061_, v_oldRef_2064_);
v___x_2066_ = lean_apply_3(v_withRef_2062_, lean_box(0), v_ref_2065_, v___x_2063_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object* v_cfg_2067_, lean_object* v_withRef_2068_, lean_object* v___x_2069_, lean_object* v_oldRef_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(v_cfg_2067_, v_withRef_2068_, v___x_2069_, v_oldRef_2070_);
lean_dec(v_oldRef_2070_);
lean_dec(v_cfg_2067_);
return v_res_2071_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t v_x_2072_){
_start:
{
uint32_t v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = 46;
v___x_2074_ = lean_uint32_dec_eq(v_x_2072_, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object* v_x_2075_){
_start:
{
uint32_t v_x_877__boxed_2076_; uint8_t v_res_2077_; lean_object* v_r_2078_; 
v_x_877__boxed_2076_ = lean_unbox_uint32(v_x_2075_);
lean_dec(v_x_2075_);
v_res_2077_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_877__boxed_2076_);
v_r_2078_ = lean_box(v_res_2077_);
return v_r_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object* v___f_2079_, lean_object* v_s_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2079_);
v___x_2088_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2080_, v___x_2087_, v___y_2081_, lean_box(0), lean_box(0), v___y_2084_, v___y_2085_, v___y_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object* v___f_2090_, lean_object* v_si_2091_, lean_object* v_val_2092_){
_start:
{
lean_object* v___y_2094_; lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___f_2100_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0));
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_string_utf8_byte_size(v_val_2092_);
lean_inc_ref(v_val_2092_);
v___x_2103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2103_, 0, v_val_2092_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2102_);
v___x_2104_ = l_String_Slice_contains___redArg(v___f_2090_, v___x_2103_, v___f_2100_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
lean_inc_ref(v_val_2092_);
v___x_2106_ = l_Lean_Name_str___override(v___x_2105_, v_val_2092_);
v___y_2094_ = v___x_2106_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2107_; 
lean_inc_ref(v_val_2092_);
v___x_2107_ = l_String_toName(v_val_2092_);
v___y_2094_ = v___x_2107_;
goto v___jp_2093_;
}
v___jp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_string_utf8_byte_size(v_val_2092_);
v___x_2097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2097_, 0, v_val_2092_);
lean_ctor_set(v___x_2097_, 1, v___x_2095_);
lean_ctor_set(v___x_2097_, 2, v___x_2096_);
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2099_, 0, v_si_2091_);
lean_ctor_set(v___x_2099_, 1, v___x_2097_);
lean_ctor_set(v___x_2099_, 2, v___y_2094_);
lean_ctor_set(v___x_2099_, 3, v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object* v_atomAsIdent_2108_, lean_object* v_stx_2109_){
_start:
{
switch(lean_obj_tag(v_stx_2109_))
{
case 3:
{
lean_object* v___x_2110_; 
lean_dec_ref(v_atomAsIdent_2108_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_stx_2109_);
return v___x_2110_;
}
case 2:
{
lean_object* v_info_2111_; lean_object* v_val_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_info_2111_ = lean_ctor_get(v_stx_2109_, 0);
lean_inc(v_info_2111_);
v_val_2112_ = lean_ctor_get(v_stx_2109_, 1);
lean_inc_ref(v_val_2112_);
lean_dec_ref_known(v_stx_2109_, 2);
v___x_2113_ = lean_apply_2(v_atomAsIdent_2108_, v_info_2111_, v_val_2112_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
default: 
{
lean_object* v___x_2115_; 
lean_dec(v_stx_2109_);
lean_dec_ref(v_atomAsIdent_2108_);
v___x_2115_ = lean_box(0);
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_init_2141_, lean_object* v_cfgs_2142_, lean_object* v_k_2143_, lean_object* v_onErr_2144_){
_start:
{
lean_object* v_toApplicative_2145_; lean_object* v_toPure_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v_toApplicative_2145_ = lean_ctor_get(v_inst_2139_, 0);
v_toPure_2146_ = lean_ctor_get(v_toApplicative_2145_, 1);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_array_get_size(v_cfgs_2142_);
v___x_2149_ = lean_nat_dec_lt(v___x_2147_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_inc(v_toPure_2146_);
lean_dec(v_onErr_2144_);
lean_dec(v_k_2143_);
lean_dec_ref(v_cfgs_2142_);
lean_dec_ref(v_inst_2140_);
lean_dec_ref(v_inst_2139_);
v___x_2150_ = lean_apply_2(v_toPure_2146_, lean_box(0), v_init_2141_);
return v___x_2150_;
}
else
{
lean_object* v___f_2151_; uint8_t v___x_2152_; 
lean_inc_ref(v_inst_2139_);
v___f_2151_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_2151_, 0, v_inst_2139_);
lean_closure_set(v___f_2151_, 1, v_inst_2140_);
lean_closure_set(v___f_2151_, 2, v_k_2143_);
lean_closure_set(v___f_2151_, 3, v_onErr_2144_);
v___x_2152_ = lean_nat_dec_le(v___x_2148_, v___x_2148_);
if (v___x_2152_ == 0)
{
if (v___x_2149_ == 0)
{
lean_object* v___x_2153_; 
lean_inc(v_toPure_2146_);
lean_dec_ref(v___f_2151_);
lean_dec_ref(v_cfgs_2142_);
lean_dec_ref(v_inst_2139_);
v___x_2153_ = lean_apply_2(v_toPure_2146_, lean_box(0), v_init_2141_);
return v___x_2153_;
}
else
{
size_t v___x_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = ((size_t)0ULL);
v___x_2155_ = lean_usize_of_nat(v___x_2148_);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2139_, v___f_2151_, v_cfgs_2142_, v___x_2154_, v___x_2155_, v_init_2141_);
return v___x_2156_;
}
}
else
{
size_t v___x_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = ((size_t)0ULL);
v___x_2158_ = lean_usize_of_nat(v___x_2148_);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2139_, v___f_2151_, v_cfgs_2142_, v___x_2157_, v___x_2158_, v_init_2141_);
return v___x_2159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_init_2162_, lean_object* v_cfg_2163_, lean_object* v_k_2164_, lean_object* v_onErr_2165_){
_start:
{
lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2163_);
v___x_2185_ = l_Lean_Syntax_isOfKind(v_cfg_2163_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = l_Lean_Syntax_getNumArgs(v_cfg_2163_);
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = lean_nat_dec_eq(v___x_2186_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___f_2189_; lean_object* v_atomAsIdent_2190_; uint8_t v___x_2191_; 
v___f_2189_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3));
v_atomAsIdent_2190_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4));
v___x_2191_ = lean_nat_dec_le(v___x_2187_, v___x_2186_);
if (v___x_2191_ == 0)
{
lean_dec(v___x_2186_);
if (lean_obj_tag(v_cfg_2163_) == 2)
{
lean_object* v_info_2192_; lean_object* v_val_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_onErr_2165_);
lean_dec_ref(v_inst_2161_);
lean_dec_ref(v_inst_2160_);
v_info_2192_ = lean_ctor_get(v_cfg_2163_, 0);
v_val_2193_ = lean_ctor_get(v_cfg_2163_, 1);
lean_inc_ref(v_val_2193_);
lean_inc(v_info_2192_);
v___x_2194_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(v___f_2189_, v_info_2192_, v_val_2193_);
v___x_2195_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2196_ = l_Lean_mkCIdentFrom(v_cfg_2163_, v___x_2195_, v___x_2191_);
v___x_2197_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2198_ = l_Lean_TSyntax_getId(v___x_2194_);
v___x_2199_ = l_Lean_Name_eraseMacroScopes(v___x_2198_);
lean_dec(v___x_2198_);
v___x_2200_ = lean_box(0);
lean_inc(v___x_2194_);
v___x_2201_ = l_Lean_Syntax_identComponents(v___x_2194_, v___x_2200_);
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2203_, 0, v_cfg_2163_);
lean_ctor_set(v___x_2203_, 1, v___x_2194_);
lean_ctor_set(v___x_2203_, 2, v___x_2196_);
lean_ctor_set(v___x_2203_, 3, v___x_2197_);
lean_ctor_set(v___x_2203_, 4, v___x_2199_);
lean_ctor_set(v___x_2203_, 5, v___x_2201_);
lean_ctor_set(v___x_2203_, 6, v___x_2202_);
v___x_2204_ = lean_apply_2(v_k_2164_, v_init_2162_, v___x_2203_);
return v___x_2204_;
}
else
{
lean_dec(v_k_2164_);
goto v___jp_2177_;
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = l_Lean_Syntax_getArg(v_cfg_2163_, v___x_2205_);
if (lean_obj_tag(v___x_2206_) == 2)
{
lean_object* v_val_2207_; lean_object* v___y_2209_; uint8_t v_val_2210_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_val_2207_ = lean_ctor_get(v___x_2206_, 1);
v___x_2221_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2222_ = lean_string_dec_eq(v_val_2207_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2224_ = lean_string_dec_eq(v_val_2207_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
lean_inc_ref(v_val_2207_);
lean_dec_ref_known(v___x_2206_, 2);
v___x_2225_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2226_ = lean_string_dec_eq(v_val_2207_, v___x_2225_);
lean_dec_ref(v_val_2207_);
if (v___x_2226_ == 0)
{
lean_dec(v___x_2186_);
lean_dec(v_k_2164_);
goto v___jp_2177_;
}
else
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = lean_unsigned_to_nat(5u);
v___x_2228_ = lean_nat_dec_le(v___x_2186_, v___x_2227_);
lean_dec(v___x_2186_);
if (v___x_2228_ == 0)
{
lean_dec(v_k_2164_);
goto v___jp_2177_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = l_Lean_Syntax_getArg(v_cfg_2163_, v___x_2187_);
v___x_2230_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2190_, v___x_2229_);
if (lean_obj_tag(v___x_2230_) == 1)
{
lean_object* v_val_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v_onErr_2165_);
lean_dec_ref(v_inst_2161_);
lean_dec_ref(v_inst_2160_);
v_val_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc_n(v_val_2231_, 2);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = lean_unsigned_to_nat(3u);
v___x_2233_ = l_Lean_Syntax_getArg(v_cfg_2163_, v___x_2232_);
v___x_2234_ = lean_box(0);
v___x_2235_ = l_Lean_TSyntax_getId(v_val_2231_);
v___x_2236_ = l_Lean_Name_eraseMacroScopes(v___x_2235_);
lean_dec(v___x_2235_);
v___x_2237_ = l_Lean_Syntax_identComponents(v_val_2231_, v___x_2234_);
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2239_, 0, v_cfg_2163_);
lean_ctor_set(v___x_2239_, 1, v_val_2231_);
lean_ctor_set(v___x_2239_, 2, v___x_2233_);
lean_ctor_set(v___x_2239_, 3, v___x_2234_);
lean_ctor_set(v___x_2239_, 4, v___x_2236_);
lean_ctor_set(v___x_2239_, 5, v___x_2237_);
lean_ctor_set(v___x_2239_, 6, v___x_2238_);
v___x_2240_ = lean_apply_2(v_k_2164_, v_init_2162_, v___x_2239_);
return v___x_2240_;
}
else
{
lean_dec(v___x_2230_);
lean_dec(v_k_2164_);
goto v___jp_2177_;
}
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_box(v___x_2222_);
v___x_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
v___y_2209_ = v___x_2242_;
v_val_2210_ = v___x_2222_;
goto v___jp_2208_;
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_box(v___x_2191_);
v___x_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
v___y_2209_ = v___x_2244_;
v_val_2210_ = v___x_2191_;
goto v___jp_2208_;
}
v___jp_2208_:
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = lean_unsigned_to_nat(2u);
v___x_2212_ = lean_nat_dec_eq(v___x_2186_, v___x_2211_);
lean_dec(v___x_2186_);
if (v___x_2212_ == 0)
{
lean_dec(v___y_2209_);
lean_dec_ref_known(v___x_2206_, 2);
lean_dec(v_k_2164_);
goto v___jp_2177_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = l_Lean_Syntax_getArg(v_cfg_2163_, v___x_2187_);
v___x_2214_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2190_, v___x_2213_);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_dec(v_onErr_2165_);
lean_dec_ref(v_inst_2161_);
lean_dec_ref(v_inst_2160_);
if (v_val_2210_ == 0)
{
lean_object* v_val_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2217_ = l_Lean_mkCIdentFrom(v___x_2206_, v___x_2216_, v_val_2210_);
lean_dec_ref_known(v___x_2206_, 2);
v___y_2167_ = v_val_2215_;
v___y_2168_ = v___y_2209_;
v___y_2169_ = v___x_2217_;
goto v___jp_2166_;
}
else
{
lean_object* v_val_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v_val_2218_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2218_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2219_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2220_ = l_Lean_mkCIdentFrom(v___x_2206_, v___x_2219_, v___x_2188_);
lean_dec_ref_known(v___x_2206_, 2);
v___y_2167_ = v_val_2218_;
v___y_2168_ = v___y_2209_;
v___y_2169_ = v___x_2220_;
goto v___jp_2166_;
}
}
else
{
lean_dec(v___x_2214_);
lean_dec(v___y_2209_);
lean_dec_ref_known(v___x_2206_, 2);
lean_dec(v_k_2164_);
goto v___jp_2177_;
}
}
}
}
else
{
lean_dec(v___x_2206_);
lean_dec(v___x_2186_);
lean_dec(v_k_2164_);
goto v___jp_2177_;
}
}
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v___x_2186_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = l_Lean_Syntax_getArg(v_cfg_2163_, v___x_2245_);
lean_dec(v_cfg_2163_);
v_cfg_2163_ = v___x_2246_;
goto _start;
}
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = l_Lean_Syntax_getArgs(v_cfg_2163_);
lean_dec(v_cfg_2163_);
v___x_2249_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2160_, v_inst_2161_, v_init_2162_, v___x_2248_, v_k_2164_, v_onErr_2165_);
return v___x_2249_;
}
v___jp_2166_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2170_ = l_Lean_TSyntax_getId(v___y_2167_);
v___x_2171_ = l_Lean_Name_eraseMacroScopes(v___x_2170_);
lean_dec(v___x_2170_);
v___x_2172_ = lean_box(0);
lean_inc(v___y_2167_);
v___x_2173_ = l_Lean_Syntax_identComponents(v___y_2167_, v___x_2172_);
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2175_, 0, v_cfg_2163_);
lean_ctor_set(v___x_2175_, 1, v___y_2167_);
lean_ctor_set(v___x_2175_, 2, v___y_2169_);
lean_ctor_set(v___x_2175_, 3, v___y_2168_);
lean_ctor_set(v___x_2175_, 4, v___x_2171_);
lean_ctor_set(v___x_2175_, 5, v___x_2173_);
lean_ctor_set(v___x_2175_, 6, v___x_2174_);
v___x_2176_ = lean_apply_2(v_k_2164_, v_init_2162_, v___x_2175_);
return v___x_2176_;
}
v___jp_2177_:
{
lean_object* v_toBind_2178_; lean_object* v_getRef_2179_; lean_object* v_withRef_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; 
v_toBind_2178_ = lean_ctor_get(v_inst_2160_, 1);
lean_inc(v_toBind_2178_);
lean_dec_ref(v_inst_2160_);
v_getRef_2179_ = lean_ctor_get(v_inst_2161_, 0);
lean_inc(v_getRef_2179_);
v_withRef_2180_ = lean_ctor_get(v_inst_2161_, 1);
lean_inc(v_withRef_2180_);
lean_dec_ref(v_inst_2161_);
lean_inc(v_cfg_2163_);
v___x_2181_ = lean_apply_2(v_onErr_2165_, v_init_2162_, v_cfg_2163_);
v___f_2182_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2182_, 0, v_cfg_2163_);
lean_closure_set(v___f_2182_, 1, v_withRef_2180_);
lean_closure_set(v___f_2182_, 2, v___x_2181_);
v___x_2183_ = lean_apply_4(v_toBind_2178_, lean_box(0), lean_box(0), v_getRef_2179_, v___f_2182_);
return v___x_2183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_k_2252_, lean_object* v_onErr_2253_, lean_object* v_x_2254_, lean_object* v_cfg_x27_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2250_, v_inst_2251_, v_x_2254_, v_cfg_x27_2255_, v_k_2252_, v_onErr_2253_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object* v_00_u03b1_2257_, lean_object* v_m_2258_, lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_init_2261_, lean_object* v_cfg_2262_, lean_object* v_k_2263_, lean_object* v_onErr_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2259_, v_inst_2260_, v_init_2261_, v_cfg_2262_, v_k_2263_, v_onErr_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object* v_00_u03b1_2266_, lean_object* v_m_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_init_2270_, lean_object* v_cfgs_2271_, lean_object* v_k_2272_, lean_object* v_onErr_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2268_, v_inst_2269_, v_init_2270_, v_cfgs_2271_, v_k_2272_, v_onErr_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_2283_, uint8_t v___y_2284_, lean_object* v_x_2285_){
_start:
{
if (lean_obj_tag(v_x_2285_) == 1)
{
lean_object* v_pre_2286_; 
v_pre_2286_ = lean_ctor_get(v_x_2285_, 0);
switch(lean_obj_tag(v_pre_2286_))
{
case 1:
{
lean_object* v_pre_2287_; 
v_pre_2287_ = lean_ctor_get(v_pre_2286_, 0);
switch(lean_obj_tag(v_pre_2287_))
{
case 0:
{
lean_object* v_str_2288_; lean_object* v_str_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_str_2288_ = lean_ctor_get(v_x_2285_, 1);
v_str_2289_ = lean_ctor_get(v_pre_2286_, 1);
v___x_2290_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_2291_ = lean_string_dec_eq(v_str_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_2293_ = lean_string_dec_eq(v_str_2289_, v___x_2292_);
if (v___x_2293_ == 0)
{
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_2295_ = lean_string_dec_eq(v_str_2288_, v___x_2294_);
if (v___x_2295_ == 0)
{
return v___x_2295_;
}
else
{
return v_suppressElabErrors_2283_;
}
}
}
else
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_2297_ = lean_string_dec_eq(v_str_2288_, v___x_2296_);
if (v___x_2297_ == 0)
{
return v___x_2297_;
}
else
{
return v_suppressElabErrors_2283_;
}
}
}
case 1:
{
lean_object* v_pre_2298_; 
v_pre_2298_ = lean_ctor_get(v_pre_2287_, 0);
if (lean_obj_tag(v_pre_2298_) == 0)
{
lean_object* v_str_2299_; lean_object* v_str_2300_; lean_object* v_str_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_str_2299_ = lean_ctor_get(v_x_2285_, 1);
v_str_2300_ = lean_ctor_get(v_pre_2286_, 1);
v_str_2301_ = lean_ctor_get(v_pre_2287_, 1);
v___x_2302_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_2303_ = lean_string_dec_eq(v_str_2301_, v___x_2302_);
if (v___x_2303_ == 0)
{
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_2305_ = lean_string_dec_eq(v_str_2300_, v___x_2304_);
if (v___x_2305_ == 0)
{
return v___x_2305_;
}
else
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_2307_ = lean_string_dec_eq(v_str_2299_, v___x_2306_);
if (v___x_2307_ == 0)
{
return v___x_2307_;
}
else
{
return v_suppressElabErrors_2283_;
}
}
}
}
else
{
return v___y_2284_;
}
}
default: 
{
return v___y_2284_;
}
}
}
case 0:
{
lean_object* v_str_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_str_2308_ = lean_ctor_get(v_x_2285_, 1);
v___x_2309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_2310_ = lean_string_dec_eq(v_str_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
return v___x_2310_;
}
else
{
return v_suppressElabErrors_2283_;
}
}
default: 
{
return v___y_2284_;
}
}
}
else
{
return v___y_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2311_, lean_object* v___y_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2314_; uint8_t v___y_6094__boxed_2315_; uint8_t v_res_2316_; lean_object* v_r_2317_; 
v_suppressElabErrors_boxed_2314_ = lean_unbox(v_suppressElabErrors_2311_);
v___y_6094__boxed_2315_ = lean_unbox(v___y_2312_);
v_res_2316_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_2314_, v___y_6094__boxed_2315_, v_x_2313_);
lean_dec(v_x_2313_);
v_r_2317_ = lean_box(v_res_2316_);
return v_r_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2318_, lean_object* v_msgData_2319_, uint8_t v_severity_2320_, uint8_t v_isSilent_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; uint8_t v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v_toCold_2335_; lean_object* v___y_2336_; lean_object* v___y_2365_; lean_object* v___y_2366_; uint8_t v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; uint8_t v___y_2397_; lean_object* v___y_2398_; uint8_t v___y_2402_; uint8_t v___y_2403_; uint8_t v___y_2404_; uint8_t v___x_2415_; uint8_t v___y_2417_; uint8_t v___y_2418_; uint8_t v___y_2419_; uint8_t v___y_2421_; uint8_t v___x_2429_; 
v___x_2415_ = 2;
v___x_2429_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2320_, v___x_2415_);
if (v___x_2429_ == 0)
{
v___y_2421_ = v___x_2429_;
goto v___jp_2420_;
}
else
{
uint8_t v___x_2430_; 
lean_inc_ref(v_msgData_2319_);
v___x_2430_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2319_);
v___y_2421_ = v___x_2430_;
goto v___jp_2420_;
}
v___jp_2327_:
{
lean_object* v_currNamespace_2337_; lean_object* v_openDecls_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v_env_2343_; lean_object* v_nextMacroScope_2344_; lean_object* v_ngen_2345_; lean_object* v_auxDeclNGen_2346_; lean_object* v_traceState_2347_; lean_object* v_cache_2348_; lean_object* v_recordedDeps_2349_; lean_object* v_messages_2350_; lean_object* v_infoState_2351_; lean_object* v_snapshotTasks_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2363_; 
v_currNamespace_2337_ = lean_ctor_get(v_toCold_2335_, 4);
v_openDecls_2338_ = lean_ctor_get(v_toCold_2335_, 5);
lean_inc(v_openDecls_2338_);
lean_inc(v_currNamespace_2337_);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_currNamespace_2337_);
lean_ctor_set(v___x_2339_, 1, v_openDecls_2338_);
v___x_2340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v___y_2329_);
lean_inc_ref(v___y_2333_);
lean_inc_ref(v___y_2334_);
v___x_2341_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2341_, 0, v___y_2334_);
lean_ctor_set(v___x_2341_, 1, v___y_2332_);
lean_ctor_set(v___x_2341_, 2, v___y_2330_);
lean_ctor_set(v___x_2341_, 3, v___y_2333_);
lean_ctor_set(v___x_2341_, 4, v___x_2340_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*5, v___y_2328_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*5 + 1, v___y_2331_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*5 + 2, v_isSilent_2321_);
v___x_2342_ = lean_st_ref_take(v___y_2336_);
v_env_2343_ = lean_ctor_get(v___x_2342_, 0);
v_nextMacroScope_2344_ = lean_ctor_get(v___x_2342_, 1);
v_ngen_2345_ = lean_ctor_get(v___x_2342_, 2);
v_auxDeclNGen_2346_ = lean_ctor_get(v___x_2342_, 3);
v_traceState_2347_ = lean_ctor_get(v___x_2342_, 4);
v_cache_2348_ = lean_ctor_get(v___x_2342_, 5);
v_recordedDeps_2349_ = lean_ctor_get(v___x_2342_, 6);
v_messages_2350_ = lean_ctor_get(v___x_2342_, 7);
v_infoState_2351_ = lean_ctor_get(v___x_2342_, 8);
v_snapshotTasks_2352_ = lean_ctor_get(v___x_2342_, 9);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2354_ = v___x_2342_;
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_snapshotTasks_2352_);
lean_inc(v_infoState_2351_);
lean_inc(v_messages_2350_);
lean_inc(v_recordedDeps_2349_);
lean_inc(v_cache_2348_);
lean_inc(v_traceState_2347_);
lean_inc(v_auxDeclNGen_2346_);
lean_inc(v_ngen_2345_);
lean_inc(v_nextMacroScope_2344_);
lean_inc(v_env_2343_);
lean_dec(v___x_2342_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2356_ = lean_box(0);
v___x_2357_ = l_Lean_MessageLog_add(v___x_2341_, v_messages_2350_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 7, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_env_2343_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_nextMacroScope_2344_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_ngen_2345_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_auxDeclNGen_2346_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v_traceState_2347_);
lean_ctor_set(v_reuseFailAlloc_2362_, 5, v_cache_2348_);
lean_ctor_set(v_reuseFailAlloc_2362_, 6, v_recordedDeps_2349_);
lean_ctor_set(v_reuseFailAlloc_2362_, 7, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2362_, 8, v_infoState_2351_);
lean_ctor_set(v_reuseFailAlloc_2362_, 9, v_snapshotTasks_2352_);
v___x_2359_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_st_ref_put(v___y_2336_, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2356_);
return v___x_2361_;
}
}
}
v___jp_2364_:
{
lean_object* v_fileName_2373_; lean_object* v_fileMap_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2390_; 
v_fileName_2373_ = lean_ctor_get(v___y_2368_, 0);
v_fileMap_2374_ = lean_ctor_get(v___y_2368_, 1);
v___x_2375_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2319_);
v___x_2376_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_2375_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2390_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2390_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_inc_ref_n(v_fileMap_2374_, 2);
v___x_2381_ = l_Lean_FileMap_toPosition(v_fileMap_2374_, v___y_2371_);
lean_dec(v___y_2371_);
v___x_2382_ = l_Lean_FileMap_toPosition(v_fileMap_2374_, v___y_2372_);
lean_dec(v___y_2372_);
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
v___x_2384_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
if (v___y_2370_ == 0)
{
lean_del_object(v___x_2379_);
lean_dec_ref(v___y_2366_);
v___y_2328_ = v___y_2367_;
v___y_2329_ = v_a_2377_;
v___y_2330_ = v___x_2383_;
v___y_2331_ = v___y_2369_;
v___y_2332_ = v___x_2381_;
v___y_2333_ = v___x_2384_;
v___y_2334_ = v_fileName_2373_;
v_toCold_2335_ = v___y_2365_;
v___y_2336_ = v___y_2325_;
goto v___jp_2327_;
}
else
{
uint8_t v___x_2385_; 
lean_inc(v_a_2377_);
v___x_2385_ = l_Lean_MessageData_hasTag(v___y_2366_, v_a_2377_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_dec_ref_known(v___x_2383_, 1);
lean_dec_ref(v___x_2381_);
lean_dec(v_a_2377_);
v___x_2386_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2386_);
v___x_2388_ = v___x_2379_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
else
{
lean_del_object(v___x_2379_);
v___y_2328_ = v___y_2367_;
v___y_2329_ = v_a_2377_;
v___y_2330_ = v___x_2383_;
v___y_2331_ = v___y_2369_;
v___y_2332_ = v___x_2381_;
v___y_2333_ = v___x_2384_;
v___y_2334_ = v_fileName_2373_;
v_toCold_2335_ = v___y_2365_;
v___y_2336_ = v___y_2325_;
goto v___jp_2327_;
}
}
}
}
v___jp_2391_:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Syntax_getTailPos_x3f(v___y_2395_, v___y_2396_);
lean_dec(v___y_2395_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_inc(v___y_2398_);
v___y_2365_ = v___y_2392_;
v___y_2366_ = v___y_2393_;
v___y_2367_ = v___y_2396_;
v___y_2368_ = v___y_2392_;
v___y_2369_ = v___y_2397_;
v___y_2370_ = v___y_2394_;
v___y_2371_ = v___y_2398_;
v___y_2372_ = v___y_2398_;
goto v___jp_2364_;
}
else
{
lean_object* v_val_2400_; 
v_val_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___y_2365_ = v___y_2392_;
v___y_2366_ = v___y_2393_;
v___y_2367_ = v___y_2396_;
v___y_2368_ = v___y_2392_;
v___y_2369_ = v___y_2397_;
v___y_2370_ = v___y_2394_;
v___y_2371_ = v___y_2398_;
v___y_2372_ = v_val_2400_;
goto v___jp_2364_;
}
}
v___jp_2401_:
{
lean_object* v_toCold_2405_; lean_object* v_ref_2406_; uint8_t v_suppressElabErrors_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___f_2410_; lean_object* v_ref_2411_; lean_object* v___x_2412_; 
v_toCold_2405_ = lean_ctor_get(v___y_2324_, 0);
v_ref_2406_ = lean_ctor_get(v___y_2324_, 2);
v_suppressElabErrors_2407_ = lean_ctor_get_uint8(v___y_2324_, sizeof(void*)*3 + 2);
v___x_2408_ = lean_box(v_suppressElabErrors_2407_);
v___x_2409_ = lean_box(v___y_2402_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2410_, 0, v___x_2408_);
lean_closure_set(v___f_2410_, 1, v___x_2409_);
v_ref_2411_ = l_Lean_replaceRef(v_ref_2318_, v_ref_2406_);
v___x_2412_ = l_Lean_Syntax_getPos_x3f(v_ref_2411_, v___y_2403_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_unsigned_to_nat(0u);
v___y_2392_ = v_toCold_2405_;
v___y_2393_ = v___f_2410_;
v___y_2394_ = v_suppressElabErrors_2407_;
v___y_2395_ = v_ref_2411_;
v___y_2396_ = v___y_2403_;
v___y_2397_ = v___y_2404_;
v___y_2398_ = v___x_2413_;
goto v___jp_2391_;
}
else
{
lean_object* v_val_2414_; 
v_val_2414_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_val_2414_);
lean_dec_ref_known(v___x_2412_, 1);
v___y_2392_ = v_toCold_2405_;
v___y_2393_ = v___f_2410_;
v___y_2394_ = v_suppressElabErrors_2407_;
v___y_2395_ = v_ref_2411_;
v___y_2396_ = v___y_2403_;
v___y_2397_ = v___y_2404_;
v___y_2398_ = v_val_2414_;
goto v___jp_2391_;
}
}
v___jp_2416_:
{
if (v___y_2419_ == 0)
{
v___y_2402_ = v___y_2417_;
v___y_2403_ = v___y_2418_;
v___y_2404_ = v_severity_2320_;
goto v___jp_2401_;
}
else
{
v___y_2402_ = v___y_2417_;
v___y_2403_ = v___y_2418_;
v___y_2404_ = v___x_2415_;
goto v___jp_2401_;
}
}
v___jp_2420_:
{
if (v___y_2421_ == 0)
{
uint8_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = 1;
v___x_2423_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2320_, v___x_2422_);
if (v___x_2423_ == 0)
{
v___y_2417_ = v___y_2421_;
v___y_2418_ = v___y_2421_;
v___y_2419_ = v___x_2423_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2424_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2324_);
v___x_2425_ = l_Lean_warningAsError;
v___x_2426_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_2424_, v___x_2425_);
lean_dec_ref(v___x_2424_);
v___y_2417_ = v___y_2421_;
v___y_2418_ = v___y_2421_;
v___y_2419_ = v___x_2426_;
goto v___jp_2416_;
}
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec_ref(v_msgData_2319_);
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2431_, lean_object* v_msgData_2432_, lean_object* v_severity_2433_, lean_object* v_isSilent_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
uint8_t v_severity_boxed_2440_; uint8_t v_isSilent_boxed_2441_; lean_object* v_res_2442_; 
v_severity_boxed_2440_ = lean_unbox(v_severity_2433_);
v_isSilent_boxed_2441_ = lean_unbox(v_isSilent_2434_);
v_res_2442_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2431_, v_msgData_2432_, v_severity_boxed_2440_, v_isSilent_boxed_2441_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v_ref_2431_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object* v_msgData_2443_, uint8_t v_severity_2444_, uint8_t v_isSilent_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_ref_2453_; lean_object* v___x_2454_; 
v_ref_2453_ = lean_ctor_get(v___y_2450_, 2);
v___x_2454_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2453_, v_msgData_2443_, v_severity_2444_, v_isSilent_2445_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2455_, lean_object* v_severity_2456_, lean_object* v_isSilent_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
uint8_t v_severity_boxed_2465_; uint8_t v_isSilent_boxed_2466_; lean_object* v_res_2467_; 
v_severity_boxed_2465_ = lean_unbox(v_severity_2456_);
v_isSilent_boxed_2466_ = lean_unbox(v_isSilent_2457_);
v_res_2467_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2455_, v_severity_boxed_2465_, v_isSilent_boxed_2466_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object* v_msgData_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
uint8_t v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = 2;
v___x_2477_ = 0;
v___x_2478_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2468_, v___x_2476_, v___x_2477_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(lean_object* v_msgData_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object* v_ref_2488_, lean_object* v_msgData_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
uint8_t v___x_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = 2;
v___x_2498_ = 0;
v___x_2499_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2488_, v_msgData_2489_, v___x_2497_, v___x_2498_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object* v_ref_2500_, lean_object* v_msgData_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2500_, v_msgData_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v_ref_2500_);
return v_res_2509_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object* v_ex_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
if (lean_obj_tag(v_ex_2513_) == 0)
{
lean_object* v_ref_2521_; lean_object* v_msg_2522_; lean_object* v___x_2523_; 
v_ref_2521_ = lean_ctor_get(v_ex_2513_, 0);
lean_inc(v_ref_2521_);
v_msg_2522_ = lean_ctor_get(v_ex_2513_, 1);
lean_inc_ref(v_msg_2522_);
lean_dec_ref_known(v_ex_2513_, 2);
v___x_2523_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2521_, v_msg_2522_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v_ref_2521_);
return v___x_2523_;
}
else
{
lean_object* v_id_2524_; uint8_t v___y_2526_; uint8_t v___x_2548_; 
v_id_2524_ = lean_ctor_get(v_ex_2513_, 0);
lean_inc(v_id_2524_);
v___x_2548_ = l_Lean_Elab_isAbortExceptionId(v_id_2524_);
if (v___x_2548_ == 0)
{
uint8_t v___x_2549_; 
v___x_2549_ = l_Lean_Exception_isInterrupt(v_ex_2513_);
lean_dec_ref_known(v_ex_2513_, 2);
v___y_2526_ = v___x_2549_;
goto v___jp_2525_;
}
else
{
lean_dec_ref_known(v_ex_2513_, 2);
v___y_2526_ = v___x_2548_;
goto v___jp_2525_;
}
v___jp_2525_:
{
if (v___y_2526_ == 0)
{
lean_object* v_ref_2527_; lean_object* v___x_2528_; 
v_ref_2527_ = lean_ctor_get(v___y_2518_, 2);
v___x_2528_ = l_Lean_InternalExceptionId_getName(v_id_2524_);
lean_dec(v_id_2524_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
v___x_2531_ = l_Lean_MessageData_ofName(v_a_2529_);
v___x_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_2532_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
return v___x_2533_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2545_; 
v_a_2534_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2536_ = v___x_2528_;
v_isShared_2537_ = v_isSharedCheck_2545_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2528_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2545_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2538_ = lean_io_error_to_string(v_a_2534_);
v___x_2539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
v___x_2540_ = l_Lean_MessageData_ofFormat(v___x_2539_);
lean_inc(v_ref_2527_);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v_ref_2527_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v___x_2541_);
v___x_2543_ = v___x_2536_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v_id_2524_);
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object* v_ex_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object* v_a_2559_, lean_object* v_config_2560_, lean_object* v_____r_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_2559_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2577_; 
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2569_, 0);
lean_dec(v_unused_2578_);
v___x_2571_ = v___x_2569_;
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
else
{
lean_dec(v___x_2569_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_config_2560_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2573_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_config_2560_);
v_a_2579_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2569_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2569_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object* v_a_2587_, lean_object* v_config_2588_, lean_object* v_____r_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2587_, v_config_2588_, v_____r_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object* v___f_2598_, lean_object* v_x_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_box(0);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
v___x_2608_ = lean_apply_8(v___f_2598_, v___x_2607_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, lean_box(0));
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(lean_object* v___f_2609_, lean_object* v_x_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2609_, v_x_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec_ref(v_x_2610_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object* v_eval_2619_, lean_object* v_config_2620_, lean_object* v_item_2621_, uint8_t v_logExceptions_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___y_2631_; lean_object* v___x_2649_; 
lean_inc(v_a_2628_);
lean_inc_ref(v_a_2627_);
lean_inc(v_a_2626_);
lean_inc_ref(v_a_2625_);
lean_inc(v_a_2624_);
lean_inc_ref(v_a_2623_);
lean_inc(v_config_2620_);
v___x_2649_ = lean_apply_9(v_eval_2619_, v_config_2620_, v_item_2621_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, lean_box(0));
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_dec(v_config_2620_);
return v___x_2649_;
}
else
{
lean_object* v_a_2650_; lean_object* v___f_2651_; uint8_t v___y_2653_; uint8_t v___x_2670_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_n(v_a_2650_, 2);
lean_inc(v_config_2620_);
v___f_2651_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2651_, 0, v_a_2650_);
lean_closure_set(v___f_2651_, 1, v_config_2620_);
v___x_2670_ = l_Lean_Exception_isInterrupt(v_a_2650_);
if (v___x_2670_ == 0)
{
uint8_t v___x_2671_; 
lean_inc(v_a_2650_);
v___x_2671_ = l_Lean_Exception_isRuntime(v_a_2650_);
v___y_2653_ = v___x_2671_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v___x_2670_;
goto v___jp_2652_;
}
v___jp_2652_:
{
if (v___y_2653_ == 0)
{
if (v_logExceptions_2622_ == 0)
{
lean_dec_ref(v___f_2651_);
lean_dec(v_a_2650_);
lean_dec(v_config_2620_);
return v___x_2649_;
}
else
{
lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2668_; 
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; 
v_unused_2669_ = lean_ctor_get(v___x_2649_, 0);
lean_dec(v_unused_2669_);
v___x_2655_ = v___x_2649_;
v_isShared_2656_ = v_isSharedCheck_2668_;
goto v_resetjp_2654_;
}
else
{
lean_dec(v___x_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2668_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
if (lean_obj_tag(v_a_2650_) == 1)
{
lean_object* v_extra_2657_; 
v_extra_2657_ = lean_ctor_get(v_a_2650_, 1);
if (lean_obj_tag(v_extra_2657_) == 0)
{
lean_object* v_id_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
lean_dec_ref(v___f_2651_);
v_id_2658_ = lean_ctor_get(v_a_2650_, 0);
v___x_2659_ = l_Lean_Elab_abortTermExceptionId;
v___x_2660_ = l_Lean_instBEqInternalExceptionId_beq(v_id_2658_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_del_object(v___x_2655_);
v___x_2661_ = lean_box(0);
v___x_2662_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2650_, v_config_2620_, v___x_2661_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
v___y_2631_ = v___x_2662_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2664_; 
lean_dec_ref_known(v_a_2650_, 2);
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 0);
lean_ctor_set(v___x_2655_, 0, v_config_2620_);
v___x_2664_ = v___x_2655_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_config_2620_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v___x_2666_; 
lean_del_object(v___x_2655_);
lean_dec(v_config_2620_);
v___x_2666_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2651_, v_a_2650_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
lean_dec_ref_known(v_a_2650_, 2);
v___y_2631_ = v___x_2666_;
goto v___jp_2630_;
}
}
else
{
lean_object* v___x_2667_; 
lean_del_object(v___x_2655_);
lean_dec(v_config_2620_);
v___x_2667_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2651_, v_a_2650_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
lean_dec(v_a_2650_);
v___y_2631_ = v___x_2667_;
goto v___jp_2630_;
}
}
}
}
else
{
lean_dec_ref(v___f_2651_);
lean_dec(v_a_2650_);
lean_dec(v_config_2620_);
return v___x_2649_;
}
}
}
v___jp_2630_:
{
if (lean_obj_tag(v___y_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2640_; 
v_a_2632_ = lean_ctor_get(v___y_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___y_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2634_ = v___y_2631_;
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___y_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_a_2636_; lean_object* v___x_2638_; 
v_a_2636_ = lean_ctor_get(v_a_2632_, 0);
lean_inc(v_a_2636_);
lean_dec(v_a_2632_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_a_2636_);
v___x_2638_ = v___x_2634_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___y_2631_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___y_2631_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___y_2631_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___y_2631_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object* v_eval_2672_, lean_object* v_config_2673_, lean_object* v_item_2674_, lean_object* v_logExceptions_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
uint8_t v_logExceptions_boxed_2683_; lean_object* v_res_2684_; 
v_logExceptions_boxed_2683_ = lean_unbox(v_logExceptions_2675_);
v_res_2684_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2672_, v_config_2673_, v_item_2674_, v_logExceptions_boxed_2683_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object* v_00_u03b1_2685_, lean_object* v_eval_2686_, lean_object* v_config_2687_, lean_object* v_item_2688_, uint8_t v_logExceptions_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2686_, v_config_2687_, v_item_2688_, v_logExceptions_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object* v_00_u03b1_2698_, lean_object* v_eval_2699_, lean_object* v_config_2700_, lean_object* v_item_2701_, lean_object* v_logExceptions_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
uint8_t v_logExceptions_boxed_2710_; lean_object* v_res_2711_; 
v_logExceptions_boxed_2710_ = lean_unbox(v_logExceptions_2702_);
v_res_2711_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(v_00_u03b1_2698_, v_eval_2699_, v_config_2700_, v_item_2701_, v_logExceptions_boxed_2710_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object* v_ref_2712_, lean_object* v_msgData_2713_, uint8_t v_severity_2714_, uint8_t v_isSilent_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2712_, v_msgData_2713_, v_severity_2714_, v_isSilent_2715_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2724_, lean_object* v_msgData_2725_, lean_object* v_severity_2726_, lean_object* v_isSilent_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
uint8_t v_severity_boxed_2735_; uint8_t v_isSilent_boxed_2736_; lean_object* v_res_2737_; 
v_severity_boxed_2735_ = lean_unbox(v_severity_2726_);
v_isSilent_boxed_2736_ = lean_unbox(v_isSilent_2727_);
v_res_2737_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2724_, v_msgData_2725_, v_severity_boxed_2735_, v_isSilent_boxed_2736_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v_ref_2724_);
return v_res_2737_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = lean_box(0);
v___x_2739_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v___x_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg(){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
v___x_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object* v_00_u03b1_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object* v_00_u03b1_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2763_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2768_ = l_Lean_Level_ofNat(v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2);
v___x_2771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set(v___x_2771_, 1, v___x_2769_);
return v___x_2771_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3);
v___x_2773_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1));
v___x_2774_ = l_Lean_Expr_const___override(v___x_2773_, v___x_2772_);
return v___x_2774_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_box(0);
v___x_2779_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6));
v___x_2780_ = l_Lean_Expr_const___override(v___x_2779_, v___x_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object* v_cfg_2784_, lean_object* v_cfgItem_2785_, lean_object* v_cfgType_x3f_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; 
if (lean_obj_tag(v_cfgType_x3f_2786_) == 1)
{
lean_object* v_val_2804_; lean_object* v___x_2805_; lean_object* v_infoState_2806_; uint8_t v_enabled_2807_; 
v_val_2804_ = lean_ctor_get(v_cfgType_x3f_2786_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v_cfgType_x3f_2786_, 1);
v___x_2805_ = lean_st_ref_get(v_a_2792_);
v_infoState_2806_ = lean_ctor_get(v___x_2805_, 8);
lean_inc_ref(v_infoState_2806_);
lean_dec(v___x_2805_);
v_enabled_2807_ = lean_ctor_get_uint8(v_infoState_2806_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2806_);
if (v_enabled_2807_ == 0)
{
lean_dec(v_val_2804_);
v___y_2795_ = v_a_2787_;
v___y_2796_ = v_a_2788_;
v___y_2797_ = v_a_2789_;
v___y_2798_ = v_a_2790_;
v___y_2799_ = v_a_2791_;
v___y_2800_ = v_a_2792_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___y_2811_; uint8_t v___x_2823_; 
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = l_Lean_Syntax_getArg(v_cfgItem_2785_, v___x_2808_);
v___x_2823_ = l_Lean_Syntax_isAtom(v___x_2809_);
if (v___x_2823_ == 0)
{
v___y_2811_ = v___x_2823_;
goto v___jp_2810_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = l_Lean_Syntax_getArg(v_cfgItem_2785_, v___x_2824_);
v___x_2826_ = l_Lean_Syntax_isMissing(v___x_2825_);
lean_dec(v___x_2825_);
v___y_2811_ = v___x_2826_;
goto v___jp_2810_;
}
v___jp_2810_:
{
if (v___y_2811_ == 0)
{
lean_dec(v___x_2809_);
lean_dec(v_val_2804_);
v___y_2795_ = v_a_2787_;
v___y_2796_ = v_a_2788_;
v___y_2797_ = v_a_2789_;
v___y_2798_ = v_a_2790_;
v___y_2799_ = v_a_2791_;
v___y_2800_ = v_a_2792_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2812_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
v___x_2813_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
v___x_2814_ = l_Lean_mkAppB(v___x_2812_, v_val_2804_, v___x_2813_);
v___x_2815_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9));
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v___x_2809_);
v___x_2817_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2818_ = lean_box(0);
v___x_2819_ = 0;
v___x_2820_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2820_, 0, v___x_2816_);
lean_ctor_set(v___x_2820_, 1, v___x_2817_);
lean_ctor_set(v___x_2820_, 2, v___x_2818_);
lean_ctor_set(v___x_2820_, 3, v___x_2814_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*4, v___x_2819_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*4 + 1, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v___x_2818_);
v___x_2822_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2821_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
lean_dec_ref(v___x_2822_);
v___y_2795_ = v_a_2787_;
v___y_2796_ = v_a_2788_;
v___y_2797_ = v_a_2789_;
v___y_2798_ = v_a_2790_;
v___y_2799_ = v_a_2791_;
v___y_2800_ = v_a_2792_;
goto v___jp_2794_;
}
}
}
}
else
{
lean_dec(v_cfgType_x3f_2786_);
v___y_2795_ = v_a_2787_;
v___y_2796_ = v_a_2788_;
v___y_2797_ = v_a_2789_;
v___y_2798_ = v_a_2790_;
v___y_2799_ = v_a_2791_;
v___y_2800_ = v_a_2792_;
goto v___jp_2794_;
}
v___jp_2794_:
{
uint8_t v___x_2801_; 
v___x_2801_ = l_Lean_Syntax_hasMissing(v_cfgItem_2785_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
lean_dec(v_cfg_2784_);
v___x_2802_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_cfg_2784_);
return v___x_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object* v_cfg_2827_, lean_object* v_cfgItem_2828_, lean_object* v_cfgType_x3f_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2827_, v_cfgItem_2828_, v_cfgType_x3f_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_cfgItem_2828_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object* v_00_u03b1_2838_, lean_object* v_cfg_2839_, lean_object* v_cfgItem_2840_, lean_object* v_cfgType_x3f_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2839_, v_cfgItem_2840_, v_cfgType_x3f_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object* v_00_u03b1_2850_, lean_object* v_cfg_2851_, lean_object* v_cfgItem_2852_, lean_object* v_cfgType_x3f_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(v_00_u03b1_2850_, v_cfg_2851_, v_cfgItem_2852_, v_cfgType_x3f_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_cfgItem_2852_);
return v_res_2861_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_s_2862_, lean_object* v_a_2863_, uint8_t v_b_2864_){
_start:
{
lean_object* v_str_2865_; lean_object* v_startInclusive_2866_; lean_object* v_endExclusive_2867_; lean_object* v___x_2868_; uint8_t v_decide_2869_; 
v_str_2865_ = lean_ctor_get(v_s_2862_, 0);
v_startInclusive_2866_ = lean_ctor_get(v_s_2862_, 1);
v_endExclusive_2867_ = lean_ctor_get(v_s_2862_, 2);
v___x_2868_ = lean_nat_sub(v_endExclusive_2867_, v_startInclusive_2866_);
v_decide_2869_ = lean_nat_dec_eq(v_a_2863_, v___x_2868_);
lean_dec(v___x_2868_);
if (v_decide_2869_ == 0)
{
lean_object* v___x_2870_; uint32_t v___x_2871_; uint32_t v___x_2872_; uint8_t v___x_2873_; 
v___x_2870_ = lean_nat_add(v_startInclusive_2866_, v_a_2863_);
lean_dec(v_a_2863_);
v___x_2871_ = lean_string_utf8_get_fast(v_str_2865_, v___x_2870_);
v___x_2872_ = 46;
v___x_2873_ = lean_uint32_dec_eq(v___x_2871_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_string_utf8_next_fast(v_str_2865_, v___x_2870_);
lean_dec(v___x_2870_);
v___x_2875_ = lean_nat_sub(v___x_2874_, v_startInclusive_2866_);
v_a_2863_ = v___x_2875_;
v_b_2864_ = v___x_2873_;
goto _start;
}
else
{
lean_dec(v___x_2870_);
return v___x_2873_;
}
}
else
{
lean_dec(v_a_2863_);
return v_b_2864_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_s_2877_, lean_object* v_a_2878_, lean_object* v_b_2879_){
_start:
{
uint8_t v_b_boxed_2880_; uint8_t v_res_2881_; lean_object* v_r_2882_; 
v_b_boxed_2880_ = lean_unbox(v_b_2879_);
v_res_2881_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2877_, v_a_2878_, v_b_boxed_2880_);
lean_dec_ref(v_s_2877_);
v_r_2882_ = lean_box(v_res_2881_);
return v_r_2882_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object* v_s_2883_){
_start:
{
lean_object* v_searcher_2884_; uint8_t v___x_2885_; uint8_t v___x_2886_; 
v_searcher_2884_ = lean_unsigned_to_nat(0u);
v___x_2885_ = 0;
v___x_2886_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2883_, v_searcher_2884_, v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object* v_s_2887_){
_start:
{
uint8_t v_res_2888_; lean_object* v_r_2889_; 
v_res_2888_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2887_);
lean_dec_ref(v_s_2887_);
v_r_2889_ = lean_box(v_res_2888_);
return v_r_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object* v_si_2890_, lean_object* v_val_2891_){
_start:
{
lean_object* v___y_2893_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2899_ = lean_unsigned_to_nat(0u);
v___x_2900_ = lean_string_utf8_byte_size(v_val_2891_);
lean_inc_ref(v_val_2891_);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v_val_2891_);
lean_ctor_set(v___x_2901_, 1, v___x_2899_);
lean_ctor_set(v___x_2901_, 2, v___x_2900_);
v___x_2902_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_2901_);
lean_dec_ref_known(v___x_2901_, 3);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_box(0);
lean_inc_ref(v_val_2891_);
v___x_2904_ = l_Lean_Name_str___override(v___x_2903_, v_val_2891_);
v___y_2893_ = v___x_2904_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_2905_; 
lean_inc_ref(v_val_2891_);
v___x_2905_ = l_String_toName(v_val_2891_);
v___y_2893_ = v___x_2905_;
goto v___jp_2892_;
}
v___jp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2894_ = lean_unsigned_to_nat(0u);
v___x_2895_ = lean_string_utf8_byte_size(v_val_2891_);
v___x_2896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2896_, 0, v_val_2891_);
lean_ctor_set(v___x_2896_, 1, v___x_2894_);
lean_ctor_set(v___x_2896_, 2, v___x_2895_);
v___x_2897_ = lean_box(0);
v___x_2898_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2898_, 0, v_si_2890_);
lean_ctor_set(v___x_2898_, 1, v___x_2896_);
lean_ctor_set(v___x_2898_, 2, v___y_2893_);
lean_ctor_set(v___x_2898_, 3, v___x_2897_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object* v_eval_2907_, uint8_t v_logExceptions_2908_, lean_object* v_onErr_2909_, lean_object* v_init_2910_, lean_object* v_cfg_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2911_);
v___x_2941_ = l_Lean_Syntax_isOfKind(v_cfg_2911_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2942_ = l_Lean_Syntax_getNumArgs(v_cfg_2911_);
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_nat_dec_eq(v___x_2942_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v_atomAsIdent_2945_; uint8_t v___x_2946_; 
v_atomAsIdent_2945_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0));
v___x_2946_ = lean_nat_dec_le(v___x_2943_, v___x_2942_);
if (v___x_2946_ == 0)
{
lean_dec(v___x_2942_);
if (lean_obj_tag(v_cfg_2911_) == 2)
{
lean_object* v_info_2947_; lean_object* v_val_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec_ref(v_onErr_2909_);
v_info_2947_ = lean_ctor_get(v_cfg_2911_, 0);
v_val_2948_ = lean_ctor_get(v_cfg_2911_, 1);
lean_inc_ref(v_val_2948_);
lean_inc(v_info_2947_);
v___x_2949_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_2947_, v_val_2948_);
v___x_2950_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2951_ = l_Lean_mkCIdentFrom(v_cfg_2911_, v___x_2950_, v___x_2946_);
v___x_2952_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2953_ = l_Lean_TSyntax_getId(v___x_2949_);
v___x_2954_ = l_Lean_Name_eraseMacroScopes(v___x_2953_);
lean_dec(v___x_2953_);
v___x_2955_ = lean_box(0);
lean_inc(v___x_2949_);
v___x_2956_ = l_Lean_Syntax_identComponents(v___x_2949_, v___x_2955_);
v___x_2957_ = lean_box(0);
v___x_2958_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2958_, 0, v_cfg_2911_);
lean_ctor_set(v___x_2958_, 1, v___x_2949_);
lean_ctor_set(v___x_2958_, 2, v___x_2951_);
lean_ctor_set(v___x_2958_, 3, v___x_2952_);
lean_ctor_set(v___x_2958_, 4, v___x_2954_);
lean_ctor_set(v___x_2958_, 5, v___x_2956_);
lean_ctor_set(v___x_2958_, 6, v___x_2957_);
v___x_2959_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2907_, v_init_2910_, v___x_2958_, v_logExceptions_2908_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2959_;
}
else
{
lean_dec_ref(v_eval_2907_);
goto v___jp_2930_;
}
}
else
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_unsigned_to_nat(0u);
v___x_2961_ = l_Lean_Syntax_getArg(v_cfg_2911_, v___x_2960_);
if (lean_obj_tag(v___x_2961_) == 2)
{
lean_object* v_val_2962_; lean_object* v___y_2964_; uint8_t v_val_2965_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_val_2962_ = lean_ctor_get(v___x_2961_, 1);
v___x_2976_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2977_ = lean_string_dec_eq(v_val_2962_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2979_ = lean_string_dec_eq(v_val_2962_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
lean_inc_ref(v_val_2962_);
lean_dec_ref_known(v___x_2961_, 2);
v___x_2980_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2981_ = lean_string_dec_eq(v_val_2962_, v___x_2980_);
lean_dec_ref(v_val_2962_);
if (v___x_2981_ == 0)
{
lean_dec(v___x_2942_);
lean_dec_ref(v_eval_2907_);
goto v___jp_2930_;
}
else
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = lean_unsigned_to_nat(5u);
v___x_2983_ = lean_nat_dec_le(v___x_2942_, v___x_2982_);
lean_dec(v___x_2942_);
if (v___x_2983_ == 0)
{
lean_dec_ref(v_eval_2907_);
goto v___jp_2930_;
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = l_Lean_Syntax_getArg(v_cfg_2911_, v___x_2943_);
v___x_2985_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2945_, v___x_2984_);
if (lean_obj_tag(v___x_2985_) == 1)
{
lean_object* v_val_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec_ref(v_onErr_2909_);
v_val_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc_n(v_val_2986_, 2);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = lean_unsigned_to_nat(3u);
v___x_2988_ = l_Lean_Syntax_getArg(v_cfg_2911_, v___x_2987_);
v___x_2989_ = lean_box(0);
v___x_2990_ = l_Lean_TSyntax_getId(v_val_2986_);
v___x_2991_ = l_Lean_Name_eraseMacroScopes(v___x_2990_);
lean_dec(v___x_2990_);
v___x_2992_ = l_Lean_Syntax_identComponents(v_val_2986_, v___x_2989_);
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2994_, 0, v_cfg_2911_);
lean_ctor_set(v___x_2994_, 1, v_val_2986_);
lean_ctor_set(v___x_2994_, 2, v___x_2988_);
lean_ctor_set(v___x_2994_, 3, v___x_2989_);
lean_ctor_set(v___x_2994_, 4, v___x_2991_);
lean_ctor_set(v___x_2994_, 5, v___x_2992_);
lean_ctor_set(v___x_2994_, 6, v___x_2993_);
v___x_2995_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2907_, v_init_2910_, v___x_2994_, v_logExceptions_2908_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2995_;
}
else
{
lean_dec(v___x_2985_);
lean_dec_ref(v_eval_2907_);
goto v___jp_2930_;
}
}
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_box(v___x_2977_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___y_2964_ = v___x_2997_;
v_val_2965_ = v___x_2977_;
goto v___jp_2963_;
}
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_box(v___x_2946_);
v___x_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
v___y_2964_ = v___x_2999_;
v_val_2965_ = v___x_2946_;
goto v___jp_2963_;
}
v___jp_2963_:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = lean_unsigned_to_nat(2u);
v___x_2967_ = lean_nat_dec_eq(v___x_2942_, v___x_2966_);
lean_dec(v___x_2942_);
if (v___x_2967_ == 0)
{
lean_dec(v___y_2964_);
lean_dec_ref_known(v___x_2961_, 2);
lean_dec_ref(v_eval_2907_);
goto v___jp_2930_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = l_Lean_Syntax_getArg(v_cfg_2911_, v___x_2943_);
v___x_2969_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2945_, v___x_2968_);
if (lean_obj_tag(v___x_2969_) == 1)
{
lean_dec_ref(v_onErr_2909_);
if (v_val_2965_ == 0)
{
lean_object* v_val_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_val_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_val_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2972_ = l_Lean_mkCIdentFrom(v___x_2961_, v___x_2971_, v_val_2965_);
lean_dec_ref_known(v___x_2961_, 2);
v___y_2920_ = v_val_2970_;
v___y_2921_ = v___y_2964_;
v___y_2922_ = v___x_2972_;
goto v___jp_2919_;
}
else
{
lean_object* v_val_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_val_2973_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_val_2973_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2974_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2975_ = l_Lean_mkCIdentFrom(v___x_2961_, v___x_2974_, v___x_2944_);
lean_dec_ref_known(v___x_2961_, 2);
v___y_2920_ = v_val_2973_;
v___y_2921_ = v___y_2964_;
v___y_2922_ = v___x_2975_;
goto v___jp_2919_;
}
}
else
{
lean_dec(v___x_2969_);
lean_dec(v___y_2964_);
lean_dec_ref_known(v___x_2961_, 2);
lean_dec_ref(v_eval_2907_);
goto v___jp_2930_;
}
}
}
}
else
{
lean_dec(v___x_2961_);
lean_dec(v___x_2942_);
lean_dec_ref(v_eval_2907_);
goto v___jp_2930_;
}
}
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v___x_2942_);
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = l_Lean_Syntax_getArg(v_cfg_2911_, v___x_3000_);
lean_dec(v_cfg_2911_);
v_cfg_2911_ = v___x_3001_;
goto _start;
}
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = l_Lean_Syntax_getArgs(v_cfg_2911_);
lean_dec(v_cfg_2911_);
v___x_3004_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_2907_, v_logExceptions_2908_, v_onErr_2909_, v_init_2910_, v___x_3003_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec_ref(v___x_3003_);
return v___x_3004_;
}
v___jp_2919_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2923_ = l_Lean_TSyntax_getId(v___y_2920_);
v___x_2924_ = l_Lean_Name_eraseMacroScopes(v___x_2923_);
lean_dec(v___x_2923_);
v___x_2925_ = lean_box(0);
lean_inc(v___y_2920_);
v___x_2926_ = l_Lean_Syntax_identComponents(v___y_2920_, v___x_2925_);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2928_, 0, v_cfg_2911_);
lean_ctor_set(v___x_2928_, 1, v___y_2920_);
lean_ctor_set(v___x_2928_, 2, v___y_2922_);
lean_ctor_set(v___x_2928_, 3, v___y_2921_);
lean_ctor_set(v___x_2928_, 4, v___x_2924_);
lean_ctor_set(v___x_2928_, 5, v___x_2926_);
lean_ctor_set(v___x_2928_, 6, v___x_2927_);
v___x_2929_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2907_, v_init_2910_, v___x_2928_, v_logExceptions_2908_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2929_;
}
v___jp_2930_:
{
lean_object* v_toCold_2931_; lean_object* v_currRecDepth_2932_; lean_object* v_ref_2933_; uint16_t v_optionFlags_2934_; uint8_t v_suppressElabErrors_2935_; uint8_t v_isRecordingDeps_2936_; lean_object* v_ref_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_toCold_2931_ = lean_ctor_get(v___y_2916_, 0);
v_currRecDepth_2932_ = lean_ctor_get(v___y_2916_, 1);
v_ref_2933_ = lean_ctor_get(v___y_2916_, 2);
v_optionFlags_2934_ = lean_ctor_get_uint16(v___y_2916_, sizeof(void*)*3);
v_suppressElabErrors_2935_ = lean_ctor_get_uint8(v___y_2916_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2936_ = lean_ctor_get_uint8(v___y_2916_, sizeof(void*)*3 + 3);
v_ref_2937_ = l_Lean_replaceRef(v_cfg_2911_, v_ref_2933_);
lean_inc(v_currRecDepth_2932_);
lean_inc_ref(v_toCold_2931_);
v___x_2938_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2938_, 0, v_toCold_2931_);
lean_ctor_set(v___x_2938_, 1, v_currRecDepth_2932_);
lean_ctor_set(v___x_2938_, 2, v_ref_2937_);
lean_ctor_set_uint16(v___x_2938_, sizeof(void*)*3, v_optionFlags_2934_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*3 + 2, v_suppressElabErrors_2935_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*3 + 3, v_isRecordingDeps_2936_);
lean_inc(v___y_2917_);
lean_inc(v___y_2915_);
lean_inc_ref(v___y_2914_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
v___x_2939_ = lean_apply_9(v_onErr_2909_, v_init_2910_, v_cfg_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___x_2938_, v___y_2917_, lean_box(0));
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object* v_eval_3005_, uint8_t v_logExceptions_3006_, lean_object* v_onErr_3007_, lean_object* v_as_3008_, size_t v_i_3009_, size_t v_stop_3010_, lean_object* v_b_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_usize_dec_eq(v_i_3009_, v_stop_3010_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_array_uget_borrowed(v_as_3008_, v_i_3009_);
lean_inc(v___x_3020_);
lean_inc_ref(v_onErr_3007_);
lean_inc_ref(v_eval_3005_);
v___x_3021_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3005_, v_logExceptions_3006_, v_onErr_3007_, v_b_3011_, v___x_3020_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; size_t v___x_3023_; size_t v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_add(v_i_3009_, v___x_3023_);
v_i_3009_ = v___x_3024_;
v_b_3011_ = v_a_3022_;
goto _start;
}
else
{
lean_dec_ref(v_onErr_3007_);
lean_dec_ref(v_eval_3005_);
return v___x_3021_;
}
}
else
{
lean_object* v___x_3026_; 
lean_dec_ref(v_onErr_3007_);
lean_dec_ref(v_eval_3005_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_b_3011_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object* v_eval_3027_, uint8_t v_logExceptions_3028_, lean_object* v_onErr_3029_, lean_object* v_init_3030_, lean_object* v_cfgs_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = lean_array_get_size(v_cfgs_3031_);
v___x_3041_ = lean_nat_dec_lt(v___x_3039_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; 
lean_dec_ref(v_onErr_3029_);
lean_dec_ref(v_eval_3027_);
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v_init_3030_);
return v___x_3042_;
}
else
{
size_t v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = lean_usize_of_nat(v___x_3040_);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3027_, v_logExceptions_3028_, v_onErr_3029_, v_cfgs_3031_, v___x_3043_, v___x_3044_, v_init_3030_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object* v_eval_3046_, lean_object* v_logExceptions_3047_, lean_object* v_onErr_3048_, lean_object* v_init_3049_, lean_object* v_cfgs_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
uint8_t v_logExceptions_boxed_3058_; lean_object* v_res_3059_; 
v_logExceptions_boxed_3058_ = lean_unbox(v_logExceptions_3047_);
v_res_3059_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3046_, v_logExceptions_boxed_3058_, v_onErr_3048_, v_init_3049_, v_cfgs_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v_cfgs_3050_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_eval_3060_, lean_object* v_logExceptions_3061_, lean_object* v_onErr_3062_, lean_object* v_as_3063_, lean_object* v_i_3064_, lean_object* v_stop_3065_, lean_object* v_b_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
uint8_t v_logExceptions_boxed_3074_; size_t v_i_boxed_3075_; size_t v_stop_boxed_3076_; lean_object* v_res_3077_; 
v_logExceptions_boxed_3074_ = lean_unbox(v_logExceptions_3061_);
v_i_boxed_3075_ = lean_unbox_usize(v_i_3064_);
lean_dec(v_i_3064_);
v_stop_boxed_3076_ = lean_unbox_usize(v_stop_3065_);
lean_dec(v_stop_3065_);
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3060_, v_logExceptions_boxed_3074_, v_onErr_3062_, v_as_3063_, v_i_boxed_3075_, v_stop_boxed_3076_, v_b_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v_as_3063_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object* v_eval_3078_, lean_object* v_logExceptions_3079_, lean_object* v_onErr_3080_, lean_object* v_init_3081_, lean_object* v_cfg_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
uint8_t v_logExceptions_boxed_3090_; lean_object* v_res_3091_; 
v_logExceptions_boxed_3090_ = lean_unbox(v_logExceptions_3079_);
v_res_3091_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3078_, v_logExceptions_boxed_3090_, v_onErr_3080_, v_init_3081_, v_cfg_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object* v_eval_3092_, lean_object* v_init_3093_, lean_object* v_cfg_3094_, lean_object* v_onErr_3095_, uint8_t v_logExceptions_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3092_, v_logExceptions_3096_, v_onErr_3095_, v_init_3093_, v_cfg_3094_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object* v_eval_3105_, lean_object* v_init_3106_, lean_object* v_cfg_3107_, lean_object* v_onErr_3108_, lean_object* v_logExceptions_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
uint8_t v_logExceptions_boxed_3117_; lean_object* v_res_3118_; 
v_logExceptions_boxed_3117_ = lean_unbox(v_logExceptions_3109_);
v_res_3118_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3105_, v_init_3106_, v_cfg_3107_, v_onErr_3108_, v_logExceptions_boxed_3117_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object* v_00_u03b1_3119_, lean_object* v_eval_3120_, lean_object* v_init_3121_, lean_object* v_cfg_3122_, lean_object* v_onErr_3123_, uint8_t v_logExceptions_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3120_, v_logExceptions_3124_, v_onErr_3123_, v_init_3121_, v_cfg_3122_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_eval_3134_, lean_object* v_init_3135_, lean_object* v_cfg_3136_, lean_object* v_onErr_3137_, lean_object* v_logExceptions_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
uint8_t v_logExceptions_boxed_3146_; lean_object* v_res_3147_; 
v_logExceptions_boxed_3146_ = lean_unbox(v_logExceptions_3138_);
v_res_3147_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(v_00_u03b1_3133_, v_eval_3134_, v_init_3135_, v_cfg_3136_, v_onErr_3137_, v_logExceptions_boxed_3146_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object* v_00_u03b1_3148_, lean_object* v_eval_3149_, uint8_t v_logExceptions_3150_, lean_object* v_onErr_3151_, lean_object* v_init_3152_, lean_object* v_cfg_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3149_, v_logExceptions_3150_, v_onErr_3151_, v_init_3152_, v_cfg_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(lean_object* v_00_u03b1_3162_, lean_object* v_eval_3163_, lean_object* v_logExceptions_3164_, lean_object* v_onErr_3165_, lean_object* v_init_3166_, lean_object* v_cfg_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
uint8_t v_logExceptions_boxed_3175_; lean_object* v_res_3176_; 
v_logExceptions_boxed_3175_ = lean_unbox(v_logExceptions_3164_);
v_res_3176_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_3162_, v_eval_3163_, v_logExceptions_boxed_3175_, v_onErr_3165_, v_init_3166_, v_cfg_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object* v_00_u03b1_3177_, lean_object* v_eval_3178_, uint8_t v_logExceptions_3179_, lean_object* v_onErr_3180_, lean_object* v_init_3181_, lean_object* v_cfgs_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3178_, v_logExceptions_3179_, v_onErr_3180_, v_init_3181_, v_cfgs_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3191_, lean_object* v_eval_3192_, lean_object* v_logExceptions_3193_, lean_object* v_onErr_3194_, lean_object* v_init_3195_, lean_object* v_cfgs_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
uint8_t v_logExceptions_boxed_3204_; lean_object* v_res_3205_; 
v_logExceptions_boxed_3204_ = lean_unbox(v_logExceptions_3193_);
v_res_3205_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_3191_, v_eval_3192_, v_logExceptions_boxed_3204_, v_onErr_3194_, v_init_3195_, v_cfgs_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec_ref(v_cfgs_3196_);
return v_res_3205_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object* v_s_3206_, lean_object* v_inst_3207_, lean_object* v_R_3208_, lean_object* v_a_3209_, uint8_t v_b_3210_, lean_object* v_c_3211_){
_start:
{
uint8_t v___x_3212_; 
v___x_3212_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_3206_, v_a_3209_, v_b_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_s_3213_, lean_object* v_inst_3214_, lean_object* v_R_3215_, lean_object* v_a_3216_, lean_object* v_b_3217_, lean_object* v_c_3218_){
_start:
{
uint8_t v_b_boxed_3219_; uint8_t v_res_3220_; lean_object* v_r_3221_; 
v_b_boxed_3219_ = lean_unbox(v_b_3217_);
v_res_3220_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3213_, v_inst_3214_, v_R_3215_, v_a_3216_, v_b_boxed_3219_, v_c_3218_);
lean_dec_ref(v_s_3213_);
v_r_3221_ = lean_box(v_res_3220_);
return v_r_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3222_, lean_object* v_eval_3223_, uint8_t v_logExceptions_3224_, lean_object* v_onErr_3225_, lean_object* v_as_3226_, size_t v_i_3227_, size_t v_stop_3228_, lean_object* v_b_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3223_, v_logExceptions_3224_, v_onErr_3225_, v_as_3226_, v_i_3227_, v_stop_3228_, v_b_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3238_, lean_object* v_eval_3239_, lean_object* v_logExceptions_3240_, lean_object* v_onErr_3241_, lean_object* v_as_3242_, lean_object* v_i_3243_, lean_object* v_stop_3244_, lean_object* v_b_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v_logExceptions_boxed_3253_; size_t v_i_boxed_3254_; size_t v_stop_boxed_3255_; lean_object* v_res_3256_; 
v_logExceptions_boxed_3253_ = lean_unbox(v_logExceptions_3240_);
v_i_boxed_3254_ = lean_unbox_usize(v_i_3243_);
lean_dec(v_i_3243_);
v_stop_boxed_3255_ = lean_unbox_usize(v_stop_3244_);
lean_dec(v_stop_3244_);
v_res_3256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_3238_, v_eval_3239_, v_logExceptions_boxed_3253_, v_onErr_3241_, v_as_3242_, v_i_boxed_3254_, v_stop_boxed_3255_, v_b_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v_as_3242_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object* v_eval_3257_, lean_object* v_init_3258_, lean_object* v_cfgs_3259_, lean_object* v_onErr_3260_, uint8_t v_logExceptions_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3257_, v_logExceptions_3261_, v_onErr_3260_, v_init_3258_, v_cfgs_3259_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object* v_eval_3270_, lean_object* v_init_3271_, lean_object* v_cfgs_3272_, lean_object* v_onErr_3273_, lean_object* v_logExceptions_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
uint8_t v_logExceptions_boxed_3282_; lean_object* v_res_3283_; 
v_logExceptions_boxed_3282_ = lean_unbox(v_logExceptions_3274_);
v_res_3283_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3270_, v_init_3271_, v_cfgs_3272_, v_onErr_3273_, v_logExceptions_boxed_3282_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec_ref(v_cfgs_3272_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object* v_00_u03b1_3284_, lean_object* v_eval_3285_, lean_object* v_init_3286_, lean_object* v_cfgs_3287_, lean_object* v_onErr_3288_, uint8_t v_logExceptions_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3285_, v_logExceptions_3289_, v_onErr_3288_, v_init_3286_, v_cfgs_3287_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object* v_00_u03b1_3298_, lean_object* v_eval_3299_, lean_object* v_init_3300_, lean_object* v_cfgs_3301_, lean_object* v_onErr_3302_, lean_object* v_logExceptions_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
uint8_t v_logExceptions_boxed_3311_; lean_object* v_res_3312_; 
v_logExceptions_boxed_3311_ = lean_unbox(v_logExceptions_3303_);
v_res_3312_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(v_00_u03b1_3298_, v_eval_3299_, v_init_3300_, v_cfgs_3301_, v_onErr_3302_, v_logExceptions_boxed_3311_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec_ref(v_cfgs_3301_);
return v_res_3312_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object* v_x_3313_){
_start:
{
uint8_t v___x_3314_; 
v___x_3314_ = 0;
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object* v_x_3315_){
_start:
{
uint8_t v_res_3316_; lean_object* v_r_3317_; 
v_res_3316_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3315_);
lean_dec(v_x_3315_);
v_r_3317_ = lean_box(v_res_3316_);
return v_r_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(lean_object* v___x_3318_, lean_object* v_ctx_x3f_3319_, size_t v_sz_3320_, size_t v_i_3321_, lean_object* v_bs_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_usize_dec_lt(v_i_3321_, v_sz_3320_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
lean_dec_ref(v_ctx_x3f_3319_);
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_bs_3322_);
return v___x_3331_;
}
else
{
lean_object* v_assignment_3332_; lean_object* v_v_3333_; lean_object* v___x_3334_; lean_object* v_bs_x27_3335_; lean_object* v_a_3337_; lean_object* v_tree_3342_; lean_object* v___x_3343_; 
v_assignment_3332_ = lean_ctor_get(v___x_3318_, 0);
v_v_3333_ = lean_array_uget(v_bs_3322_, v_i_3321_);
v___x_3334_ = lean_unsigned_to_nat(0u);
v_bs_x27_3335_ = lean_array_uset(v_bs_3322_, v_i_3321_, v___x_3334_);
v_tree_3342_ = l_Lean_Elab_InfoTree_substitute(v_v_3333_, v_assignment_3332_);
lean_inc_ref(v_ctx_x3f_3319_);
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3327_);
lean_inc(v___y_3326_);
lean_inc_ref(v___y_3325_);
lean_inc(v___y_3324_);
lean_inc_ref(v___y_3323_);
v___x_3343_ = lean_apply_7(v_ctx_x3f_3319_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, lean_box(0));
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
if (lean_obj_tag(v_a_3344_) == 0)
{
v_a_3337_ = v_tree_3342_;
goto v___jp_3336_;
}
else
{
lean_object* v_val_3345_; lean_object* v___x_3346_; 
v_val_3345_ = lean_ctor_get(v_a_3344_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v_a_3344_, 1);
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_val_3345_);
lean_ctor_set(v___x_3346_, 1, v_tree_3342_);
v_a_3337_ = v___x_3346_;
goto v___jp_3336_;
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v_tree_3342_);
lean_dec_ref(v_bs_x27_3335_);
lean_dec_ref(v_ctx_x3f_3319_);
v_a_3347_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3343_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3343_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
v___jp_3336_:
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3321_, v___x_3338_);
v___x_3340_ = lean_array_uset(v_bs_x27_3335_, v_i_3321_, v_a_3337_);
v_i_3321_ = v___x_3339_;
v_bs_3322_ = v___x_3340_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v___x_3355_, lean_object* v_ctx_x3f_3356_, lean_object* v_sz_3357_, lean_object* v_i_3358_, lean_object* v_bs_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
size_t v_sz_boxed_3367_; size_t v_i_boxed_3368_; lean_object* v_res_3369_; 
v_sz_boxed_3367_ = lean_unbox_usize(v_sz_3357_);
lean_dec(v_sz_3357_);
v_i_boxed_3368_ = lean_unbox_usize(v_i_3358_);
lean_dec(v_i_3358_);
v_res_3369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3355_, v_ctx_x3f_3356_, v_sz_boxed_3367_, v_i_boxed_3368_, v_bs_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec_ref(v___x_3355_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(lean_object* v___x_3370_, lean_object* v_ctx_x3f_3371_, lean_object* v_x_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
if (lean_obj_tag(v_x_3372_) == 0)
{
lean_object* v_cs_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3406_; 
v_cs_3380_ = lean_ctor_get(v_x_3372_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_x_3372_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3382_ = v_x_3372_;
v_isShared_3383_ = v_isSharedCheck_3406_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_cs_3380_);
lean_dec(v_x_3372_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3406_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
size_t v_sz_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v_sz_3384_ = lean_array_size(v_cs_3380_);
v___x_3385_ = ((size_t)0ULL);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3370_, v_ctx_x3f_3371_, v_sz_3384_, v___x_3385_, v_cs_3380_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3397_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3397_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3397_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v_a_3387_);
v___x_3392_ = v___x_3382_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3392_);
v___x_3394_ = v___x_3389_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_del_object(v___x_3382_);
v_a_3398_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3386_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3386_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
else
{
lean_object* v_vs_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3433_; 
v_vs_3407_ = lean_ctor_get(v_x_3372_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_x_3372_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3409_ = v_x_3372_;
v_isShared_3410_ = v_isSharedCheck_3433_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_vs_3407_);
lean_dec(v_x_3372_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3433_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
size_t v_sz_3411_; size_t v___x_3412_; lean_object* v___x_3413_; 
v_sz_3411_ = lean_array_size(v_vs_3407_);
v___x_3412_ = ((size_t)0ULL);
v___x_3413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3370_, v_ctx_x3f_3371_, v_sz_3411_, v___x_3412_, v_vs_3407_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3424_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3424_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3424_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_a_3414_);
v___x_3419_ = v___x_3409_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3419_);
v___x_3421_ = v___x_3416_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_del_object(v___x_3409_);
v_a_3425_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3413_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3413_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v___x_3434_, lean_object* v_ctx_x3f_3435_, size_t v_sz_3436_, size_t v_i_3437_, lean_object* v_bs_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec_ref(v_ctx_x3f_3435_);
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_bs_3438_);
return v___x_3447_;
}
else
{
lean_object* v_v_3448_; lean_object* v___x_3449_; lean_object* v_bs_x27_3450_; lean_object* v___x_3451_; 
v_v_3448_ = lean_array_uget(v_bs_3438_, v_i_3437_);
v___x_3449_ = lean_unsigned_to_nat(0u);
v_bs_x27_3450_ = lean_array_uset(v_bs_3438_, v_i_3437_, v___x_3449_);
lean_inc_ref(v_ctx_x3f_3435_);
v___x_3451_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3434_, v_ctx_x3f_3435_, v_v_3448_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = ((size_t)1ULL);
v___x_3454_ = lean_usize_add(v_i_3437_, v___x_3453_);
v___x_3455_ = lean_array_uset(v_bs_x27_3450_, v_i_3437_, v_a_3452_);
v_i_3437_ = v___x_3454_;
v_bs_3438_ = v___x_3455_;
goto _start;
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec_ref(v_bs_x27_3450_);
lean_dec_ref(v_ctx_x3f_3435_);
v_a_3457_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3451_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3451_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v___x_3465_, lean_object* v_ctx_x3f_3466_, lean_object* v_sz_3467_, lean_object* v_i_3468_, lean_object* v_bs_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
size_t v_sz_boxed_3477_; size_t v_i_boxed_3478_; lean_object* v_res_3479_; 
v_sz_boxed_3477_ = lean_unbox_usize(v_sz_3467_);
lean_dec(v_sz_3467_);
v_i_boxed_3478_ = lean_unbox_usize(v_i_3468_);
lean_dec(v_i_3468_);
v_res_3479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3465_, v_ctx_x3f_3466_, v_sz_boxed_3477_, v_i_boxed_3478_, v_bs_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec_ref(v___x_3465_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v___x_3480_, lean_object* v_ctx_x3f_3481_, lean_object* v_x_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3480_, v_ctx_x3f_3481_, v_x_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec_ref(v___x_3480_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object* v___x_3491_, lean_object* v_ctx_x3f_3492_, lean_object* v_t_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_root_3501_; lean_object* v_tail_3502_; lean_object* v_size_3503_; size_t v_shift_3504_; lean_object* v_tailOff_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3541_; 
v_root_3501_ = lean_ctor_get(v_t_3493_, 0);
v_tail_3502_ = lean_ctor_get(v_t_3493_, 1);
v_size_3503_ = lean_ctor_get(v_t_3493_, 2);
v_shift_3504_ = lean_ctor_get_usize(v_t_3493_, 4);
v_tailOff_3505_ = lean_ctor_get(v_t_3493_, 3);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_t_3493_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3507_ = v_t_3493_;
v_isShared_3508_ = v_isSharedCheck_3541_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_tailOff_3505_);
lean_inc(v_size_3503_);
lean_inc(v_tail_3502_);
lean_inc(v_root_3501_);
lean_dec(v_t_3493_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3541_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; 
lean_inc_ref(v_ctx_x3f_3492_);
v___x_3509_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3491_, v_ctx_x3f_3492_, v_root_3501_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; size_t v_sz_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v_sz_3511_ = lean_array_size(v_tail_3502_);
v___x_3512_ = ((size_t)0ULL);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3491_, v_ctx_x3f_3492_, v_sz_3511_, v___x_3512_, v_tail_3502_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3524_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3524_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3524_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v_a_3514_);
lean_ctor_set(v___x_3507_, 0, v_a_3510_);
v___x_3519_ = v___x_3507_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3510_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_a_3514_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_size_3503_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v_tailOff_3505_);
lean_ctor_set_usize(v_reuseFailAlloc_3523_, 4, v_shift_3504_);
v___x_3519_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3519_);
v___x_3521_ = v___x_3516_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
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
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_a_3510_);
lean_del_object(v___x_3507_);
lean_dec(v_tailOff_3505_);
lean_dec(v_size_3503_);
v_a_3525_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3513_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3513_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_del_object(v___x_3507_);
lean_dec(v_tailOff_3505_);
lean_dec(v_size_3503_);
lean_dec_ref(v_tail_3502_);
lean_dec_ref(v_ctx_x3f_3492_);
v_a_3533_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3509_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3509_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object* v___x_3542_, lean_object* v_ctx_x3f_3543_, lean_object* v_t_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3542_, v_ctx_x3f_3543_, v_t_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec_ref(v___x_3542_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3553_, lean_object* v_ctx_x3f_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v_a_3560_, lean_object* v_a_x3f_3561_){
_start:
{
lean_object* v___x_3563_; lean_object* v_infoState_3564_; lean_object* v_trees_3565_; lean_object* v___x_3566_; 
v___x_3563_ = lean_st_ref_get(v___y_3553_);
v_infoState_3564_ = lean_ctor_get(v___x_3563_, 8);
lean_inc_ref(v_infoState_3564_);
lean_dec(v___x_3563_);
v_trees_3565_ = lean_ctor_get(v_infoState_3564_, 2);
lean_inc_ref(v_trees_3565_);
v___x_3566_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_3564_, v_ctx_x3f_3554_, v_trees_3565_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3553_);
lean_dec_ref(v_infoState_3564_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3606_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3606_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3606_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v_infoState_3572_; lean_object* v_env_3573_; lean_object* v_nextMacroScope_3574_; lean_object* v_ngen_3575_; lean_object* v_auxDeclNGen_3576_; lean_object* v_traceState_3577_; lean_object* v_cache_3578_; lean_object* v_recordedDeps_3579_; lean_object* v_messages_3580_; lean_object* v_snapshotTasks_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3605_; 
v___x_3571_ = lean_st_ref_take(v___y_3553_);
v_infoState_3572_ = lean_ctor_get(v___x_3571_, 8);
v_env_3573_ = lean_ctor_get(v___x_3571_, 0);
v_nextMacroScope_3574_ = lean_ctor_get(v___x_3571_, 1);
v_ngen_3575_ = lean_ctor_get(v___x_3571_, 2);
v_auxDeclNGen_3576_ = lean_ctor_get(v___x_3571_, 3);
v_traceState_3577_ = lean_ctor_get(v___x_3571_, 4);
v_cache_3578_ = lean_ctor_get(v___x_3571_, 5);
v_recordedDeps_3579_ = lean_ctor_get(v___x_3571_, 6);
v_messages_3580_ = lean_ctor_get(v___x_3571_, 7);
v_snapshotTasks_3581_ = lean_ctor_get(v___x_3571_, 9);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3583_ = v___x_3571_;
v_isShared_3584_ = v_isSharedCheck_3605_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_snapshotTasks_3581_);
lean_inc(v_infoState_3572_);
lean_inc(v_messages_3580_);
lean_inc(v_recordedDeps_3579_);
lean_inc(v_cache_3578_);
lean_inc(v_traceState_3577_);
lean_inc(v_auxDeclNGen_3576_);
lean_inc(v_ngen_3575_);
lean_inc(v_nextMacroScope_3574_);
lean_inc(v_env_3573_);
lean_dec(v___x_3571_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3605_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
uint8_t v_enabled_3585_; lean_object* v_assignment_3586_; lean_object* v_lazyAssignment_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3603_; 
v_enabled_3585_ = lean_ctor_get_uint8(v_infoState_3572_, sizeof(void*)*3);
v_assignment_3586_ = lean_ctor_get(v_infoState_3572_, 0);
v_lazyAssignment_3587_ = lean_ctor_get(v_infoState_3572_, 1);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_infoState_3572_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v_infoState_3572_, 2);
lean_dec(v_unused_3604_);
v___x_3589_ = v_infoState_3572_;
v_isShared_3590_ = v_isSharedCheck_3603_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_lazyAssignment_3587_);
lean_inc(v_assignment_3586_);
lean_dec(v_infoState_3572_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3603_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3591_ = lean_box(0);
v___x_3592_ = l_Lean_PersistentArray_append___redArg(v_a_3560_, v_a_3567_);
lean_dec(v_a_3567_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 2, v___x_3592_);
v___x_3594_ = v___x_3589_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_assignment_3586_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_lazyAssignment_3587_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v___x_3592_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, sizeof(void*)*3, v_enabled_3585_);
v___x_3594_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3596_; 
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 8, v___x_3594_);
v___x_3596_ = v___x_3583_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_env_3573_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_nextMacroScope_3574_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_ngen_3575_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_auxDeclNGen_3576_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v_traceState_3577_);
lean_ctor_set(v_reuseFailAlloc_3601_, 5, v_cache_3578_);
lean_ctor_set(v_reuseFailAlloc_3601_, 6, v_recordedDeps_3579_);
lean_ctor_set(v_reuseFailAlloc_3601_, 7, v_messages_3580_);
lean_ctor_set(v_reuseFailAlloc_3601_, 8, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3601_, 9, v_snapshotTasks_3581_);
v___x_3596_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3597_ = lean_st_ref_put(v___y_3553_, v___x_3596_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3591_);
v___x_3599_ = v___x_3569_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3591_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v_a_3560_);
v_a_3607_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3566_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3566_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3615_, lean_object* v_ctx_x3f_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v_a_3622_, lean_object* v_a_x3f_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3615_, v_ctx_x3f_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v_a_3622_, v_a_x3f_3623_);
lean_dec(v_a_x3f_3623_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3615_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; lean_object* v_infoState_3629_; lean_object* v_trees_3630_; lean_object* v___x_3631_; lean_object* v_infoState_3632_; lean_object* v_env_3633_; lean_object* v_nextMacroScope_3634_; lean_object* v_ngen_3635_; lean_object* v_auxDeclNGen_3636_; lean_object* v_traceState_3637_; lean_object* v_cache_3638_; lean_object* v_recordedDeps_3639_; lean_object* v_messages_3640_; lean_object* v_snapshotTasks_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3664_; 
v___x_3628_ = lean_st_ref_get(v___y_3626_);
v_infoState_3629_ = lean_ctor_get(v___x_3628_, 8);
lean_inc_ref(v_infoState_3629_);
lean_dec(v___x_3628_);
v_trees_3630_ = lean_ctor_get(v_infoState_3629_, 2);
lean_inc_ref(v_trees_3630_);
lean_dec_ref(v_infoState_3629_);
v___x_3631_ = lean_st_ref_take(v___y_3626_);
v_infoState_3632_ = lean_ctor_get(v___x_3631_, 8);
v_env_3633_ = lean_ctor_get(v___x_3631_, 0);
v_nextMacroScope_3634_ = lean_ctor_get(v___x_3631_, 1);
v_ngen_3635_ = lean_ctor_get(v___x_3631_, 2);
v_auxDeclNGen_3636_ = lean_ctor_get(v___x_3631_, 3);
v_traceState_3637_ = lean_ctor_get(v___x_3631_, 4);
v_cache_3638_ = lean_ctor_get(v___x_3631_, 5);
v_recordedDeps_3639_ = lean_ctor_get(v___x_3631_, 6);
v_messages_3640_ = lean_ctor_get(v___x_3631_, 7);
v_snapshotTasks_3641_ = lean_ctor_get(v___x_3631_, 9);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3643_ = v___x_3631_;
v_isShared_3644_ = v_isSharedCheck_3664_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_snapshotTasks_3641_);
lean_inc(v_infoState_3632_);
lean_inc(v_messages_3640_);
lean_inc(v_recordedDeps_3639_);
lean_inc(v_cache_3638_);
lean_inc(v_traceState_3637_);
lean_inc(v_auxDeclNGen_3636_);
lean_inc(v_ngen_3635_);
lean_inc(v_nextMacroScope_3634_);
lean_inc(v_env_3633_);
lean_dec(v___x_3631_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3664_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
uint8_t v_enabled_3645_; lean_object* v_assignment_3646_; lean_object* v_lazyAssignment_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3662_; 
v_enabled_3645_ = lean_ctor_get_uint8(v_infoState_3632_, sizeof(void*)*3);
v_assignment_3646_ = lean_ctor_get(v_infoState_3632_, 0);
v_lazyAssignment_3647_ = lean_ctor_get(v_infoState_3632_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_infoState_3632_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; 
v_unused_3663_ = lean_ctor_get(v_infoState_3632_, 2);
lean_dec(v_unused_3663_);
v___x_3649_ = v_infoState_3632_;
v_isShared_3650_ = v_isSharedCheck_3662_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_lazyAssignment_3647_);
lean_inc(v_assignment_3646_);
lean_dec(v_infoState_3632_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3662_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3651_ = lean_unsigned_to_nat(32u);
v___x_3652_ = lean_mk_empty_array_with_capacity(v___x_3651_);
lean_dec_ref(v___x_3652_);
v___x_3653_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 2, v___x_3653_);
v___x_3655_ = v___x_3649_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_assignment_3646_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_lazyAssignment_3647_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v___x_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, sizeof(void*)*3, v_enabled_3645_);
v___x_3655_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 8, v___x_3655_);
v___x_3657_ = v___x_3643_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_env_3633_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_nextMacroScope_3634_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_ngen_3635_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_auxDeclNGen_3636_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_traceState_3637_);
lean_ctor_set(v_reuseFailAlloc_3660_, 5, v_cache_3638_);
lean_ctor_set(v_reuseFailAlloc_3660_, 6, v_recordedDeps_3639_);
lean_ctor_set(v_reuseFailAlloc_3660_, 7, v_messages_3640_);
lean_ctor_set(v_reuseFailAlloc_3660_, 8, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3660_, 9, v_snapshotTasks_3641_);
v___x_3657_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_st_ref_put(v___y_3626_, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v_trees_3630_);
return v___x_3659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3665_);
lean_dec(v___y_3665_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object* v_x_3668_, lean_object* v_ctx_x3f_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v___x_3677_; lean_object* v_infoState_3678_; uint8_t v_enabled_3679_; 
v___x_3677_ = lean_st_ref_get(v___y_3675_);
v_infoState_3678_ = lean_ctor_get(v___x_3677_, 8);
lean_inc_ref(v_infoState_3678_);
lean_dec(v___x_3677_);
v_enabled_3679_ = lean_ctor_get_uint8(v_infoState_3678_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3678_);
if (v_enabled_3679_ == 0)
{
lean_object* v___x_3680_; 
lean_dec_ref(v_ctx_x3f_3669_);
lean_inc(v___y_3675_);
lean_inc_ref(v___y_3674_);
lean_inc(v___y_3673_);
lean_inc_ref(v___y_3672_);
lean_inc(v___y_3671_);
lean_inc_ref(v___y_3670_);
v___x_3680_ = lean_apply_7(v_x_3668_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, lean_box(0));
return v___x_3680_;
}
else
{
lean_object* v___x_3681_; lean_object* v_a_3682_; lean_object* v_r_3683_; 
v___x_3681_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3675_);
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
lean_inc(v___y_3675_);
lean_inc_ref(v___y_3674_);
lean_inc(v___y_3673_);
lean_inc_ref(v___y_3672_);
lean_inc(v___y_3671_);
lean_inc_ref(v___y_3670_);
v_r_3683_ = lean_apply_7(v_x_3668_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, lean_box(0));
if (lean_obj_tag(v_r_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3708_; 
v_a_3684_ = lean_ctor_get(v_r_3683_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_r_3683_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3686_ = v_r_3683_;
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v_r_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
lean_inc(v_a_3684_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set_tag(v___x_3686_, 1);
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3690_; 
v___x_3690_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3675_, v_ctx_x3f_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v_a_3682_, v___x_3689_);
lean_dec_ref(v___x_3689_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; 
v_unused_3698_ = lean_ctor_get(v___x_3690_, 0);
lean_dec(v_unused_3698_);
v___x_3692_ = v___x_3690_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_dec(v___x_3690_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v_a_3684_);
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3684_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_a_3684_);
v_a_3699_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3690_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3690_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_a_3709_ = lean_ctor_get(v_r_3683_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v_r_3683_, 1);
v___x_3710_ = lean_box(0);
v___x_3711_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3675_, v_ctx_x3f_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v_a_3682_, v___x_3710_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; 
v_unused_3719_ = lean_ctor_get(v___x_3711_, 0);
lean_dec(v_unused_3719_);
v___x_3713_ = v___x_3711_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_dec(v___x_3711_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set_tag(v___x_3713_, 1);
lean_ctor_set(v___x_3713_, 0, v_a_3709_);
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3709_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec(v_a_3709_);
v_a_3720_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3711_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3711_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_3728_, lean_object* v_ctx_x3f_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3728_, v_ctx_x3f_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___x_3742_; lean_object* v_env_3743_; lean_object* v___x_3744_; lean_object* v_toCold_3745_; lean_object* v_mctx_3746_; lean_object* v_currNamespace_3747_; lean_object* v_openDecls_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v_ngen_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3742_ = lean_st_ref_get(v___y_3740_);
v_env_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc_ref(v_env_3743_);
lean_dec(v___x_3742_);
v___x_3744_ = lean_st_ref_get(v___y_3738_);
v_toCold_3745_ = lean_ctor_get(v___y_3739_, 0);
v_mctx_3746_ = lean_ctor_get(v___x_3744_, 0);
lean_inc_ref(v_mctx_3746_);
lean_dec(v___x_3744_);
v_currNamespace_3747_ = lean_ctor_get(v_toCold_3745_, 4);
v_openDecls_3748_ = lean_ctor_get(v_toCold_3745_, 5);
v___x_3749_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3739_);
v___x_3750_ = lean_st_ref_get(v___y_3740_);
v_ngen_3751_ = lean_ctor_get(v___x_3750_, 2);
lean_inc_ref(v_ngen_3751_);
lean_dec(v___x_3750_);
v___x_3752_ = lean_box(0);
v___x_3753_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_3748_);
lean_inc(v_currNamespace_3747_);
v___x_3754_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3754_, 0, v_env_3743_);
lean_ctor_set(v___x_3754_, 1, v___x_3752_);
lean_ctor_set(v___x_3754_, 2, v___x_3753_);
lean_ctor_set(v___x_3754_, 3, v_mctx_3746_);
lean_ctor_set(v___x_3754_, 4, v___x_3749_);
lean_ctor_set(v___x_3754_, 5, v_currNamespace_3747_);
lean_ctor_set(v___x_3754_, 6, v_openDecls_3748_);
lean_ctor_set(v___x_3754_, 7, v_ngen_3751_);
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; lean_object* v_toCold_3769_; lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3794_; 
v___x_3768_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3764_, v___y_3765_, v___y_3766_);
v_toCold_3769_ = lean_ctor_get(v___y_3765_, 0);
v_a_3770_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3772_ = v___x_3768_;
v_isShared_3773_ = v_isSharedCheck_3794_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3768_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3794_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v_fileMap_3774_; lean_object* v_env_3775_; lean_object* v_mctx_3776_; lean_object* v_options_3777_; lean_object* v_currNamespace_3778_; lean_object* v_openDecls_3779_; lean_object* v_ngen_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3791_; 
v_fileMap_3774_ = lean_ctor_get(v_toCold_3769_, 1);
v_env_3775_ = lean_ctor_get(v_a_3770_, 0);
v_mctx_3776_ = lean_ctor_get(v_a_3770_, 3);
v_options_3777_ = lean_ctor_get(v_a_3770_, 4);
v_currNamespace_3778_ = lean_ctor_get(v_a_3770_, 5);
v_openDecls_3779_ = lean_ctor_get(v_a_3770_, 6);
v_ngen_3780_ = lean_ctor_get(v_a_3770_, 7);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_a_3770_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; lean_object* v_unused_3793_; 
v_unused_3792_ = lean_ctor_get(v_a_3770_, 2);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_a_3770_, 1);
lean_dec(v_unused_3793_);
v___x_3782_ = v_a_3770_;
v_isShared_3783_ = v_isSharedCheck_3791_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_ngen_3780_);
lean_inc(v_openDecls_3779_);
lean_inc(v_currNamespace_3778_);
lean_inc(v_options_3777_);
lean_inc(v_mctx_3776_);
lean_inc(v_env_3775_);
lean_dec(v_a_3770_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3791_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3784_ = lean_box(0);
lean_inc_ref(v_fileMap_3774_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 2, v_fileMap_3774_);
lean_ctor_set(v___x_3782_, 1, v___x_3784_);
v___x_3786_ = v___x_3782_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_env_3775_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_fileMap_3774_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_mctx_3776_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_options_3777_);
lean_ctor_set(v_reuseFailAlloc_3790_, 5, v_currNamespace_3778_);
lean_ctor_set(v_reuseFailAlloc_3790_, 6, v_openDecls_3779_);
lean_ctor_set(v_reuseFailAlloc_3790_, 7, v_ngen_3780_);
v___x_3786_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3786_);
v___x_3788_ = v___x_3772_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3820_; 
v___x_3810_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3820_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3820_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_a_3811_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v___x_3816_);
v___x_3818_ = v___x_3813_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object* v_x_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___f_3838_; lean_object* v___x_3839_; 
v___f_3838_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0));
v___x_3839_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3830_, v___f_3838_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object* v_x_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object* v_00_u03b1_3849_, lean_object* v_x_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object* v_00_u03b1_3859_, lean_object* v_x_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(v_00_u03b1_3859_, v_x_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3868_;
}
}
static uint64_t _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_3889_; uint64_t v___x_3890_; 
v___x_3889_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3890_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3889_);
return v___x_3890_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6(void){
_start:
{
uint64_t v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3891_ = lean_uint64_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5);
v___x_3892_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3893_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set_uint64(v___x_3893_, sizeof(void*)*1, v___x_3891_);
return v___x_3893_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7(void){
_start:
{
uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3894_ = 1;
v___x_3895_ = lean_unsigned_to_nat(0u);
v___x_3896_ = lean_box(0);
v___x_3897_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1));
v___x_3898_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_3899_ = lean_box(1);
v___x_3900_ = 0;
v___x_3901_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6);
v___x_3902_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
lean_ctor_set(v___x_3902_, 1, v___x_3899_);
lean_ctor_set(v___x_3902_, 2, v___x_3898_);
lean_ctor_set(v___x_3902_, 3, v___x_3897_);
lean_ctor_set(v___x_3902_, 4, v___x_3896_);
lean_ctor_set(v___x_3902_, 5, v___x_3895_);
lean_ctor_set(v___x_3902_, 6, v___x_3896_);
lean_ctor_set_uint8(v___x_3902_, sizeof(void*)*7, v___x_3900_);
lean_ctor_set_uint8(v___x_3902_, sizeof(void*)*7 + 1, v___x_3900_);
lean_ctor_set_uint8(v___x_3902_, sizeof(void*)*7 + 2, v___x_3900_);
lean_ctor_set_uint8(v___x_3902_, sizeof(void*)*7 + 3, v___x_3894_);
return v___x_3902_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3903_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3904_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3905_ = lean_unsigned_to_nat(0u);
v___x_3906_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
lean_ctor_set(v___x_3906_, 2, v___x_3905_);
lean_ctor_set(v___x_3906_, 3, v___x_3905_);
lean_ctor_set(v___x_3906_, 4, v___x_3904_);
lean_ctor_set(v___x_3906_, 5, v___x_3904_);
lean_ctor_set(v___x_3906_, 6, v___x_3904_);
lean_ctor_set(v___x_3906_, 7, v___x_3904_);
lean_ctor_set(v___x_3906_, 8, v___x_3904_);
lean_ctor_set(v___x_3906_, 9, v___x_3904_);
lean_ctor_set(v___x_3906_, 10, v___x_3904_);
lean_ctor_set(v___x_3906_, 11, v___x_3903_);
return v___x_3906_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3908_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
lean_ctor_set(v___x_3908_, 2, v___x_3907_);
lean_ctor_set(v___x_3908_, 3, v___x_3907_);
lean_ctor_set(v___x_3908_, 4, v___x_3907_);
lean_ctor_set(v___x_3908_, 5, v___x_3907_);
return v___x_3908_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
lean_ctor_set(v___x_3910_, 2, v___x_3909_);
lean_ctor_set(v___x_3910_, 3, v___x_3909_);
lean_ctor_set(v___x_3910_, 4, v___x_3909_);
return v___x_3910_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3911_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10);
v___x_3912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_3913_ = lean_box(1);
v___x_3914_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
v___x_3915_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8);
v___x_3916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v___x_3914_);
lean_ctor_set(v___x_3916_, 2, v___x_3913_);
lean_ctor_set(v___x_3916_, 3, v___x_3912_);
lean_ctor_set(v___x_3916_, 4, v___x_3911_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object* v_mx_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3921_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed), 9, 2);
lean_closure_set(v___x_3921_, 0, lean_box(0));
lean_closure_set(v___x_3921_, 1, v_mx_3917_);
v___x_3922_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2));
v___x_3923_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3924_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7);
v___x_3925_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11);
v___x_3926_ = lean_st_mk_ref(v___x_3925_);
v___x_3927_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3921_, v___x_3922_, v___x_3923_, v___x_3924_, v___x_3926_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3937_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3937_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3937_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v_fst_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v_fst_3932_ = lean_ctor_get(v_a_3928_, 0);
lean_inc(v_fst_3932_);
lean_dec(v_a_3928_);
v___x_3933_ = lean_st_ref_get(v___x_3926_);
lean_dec(v___x_3926_);
lean_dec(v___x_3933_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v_fst_3932_);
v___x_3935_ = v___x_3930_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_fst_3932_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec(v___x_3926_);
v_a_3938_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3927_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3927_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object* v_mx_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3946_, v_a_3947_, v_a_3948_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object* v_00_u03b1_3951_, lean_object* v_mx_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3952_, v_a_3953_, v_a_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object* v_00_u03b1_3957_, lean_object* v_mx_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_3957_, v_mx_3958_, v_a_3959_, v_a_3960_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object* v_00_u03b1_3995_, lean_object* v_x_3996_, lean_object* v_ctx_x3f_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3996_, v_ctx_x3f_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4006_, lean_object* v_x_4007_, lean_object* v_ctx_x3f_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_4006_, v_x_4007_, v_ctx_x3f_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object* v_eval_4017_, uint8_t v_logExceptions_4018_, lean_object* v_onErr_4019_, lean_object* v_init_4020_, lean_object* v_cfg_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_4017_, v_logExceptions_4018_, v_onErr_4019_, v_init_4020_, v_cfg_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object* v_eval_4030_, lean_object* v_logExceptions_4031_, lean_object* v_onErr_4032_, lean_object* v_init_4033_, lean_object* v_cfg_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
uint8_t v_logExceptions_boxed_4042_; lean_object* v_res_4043_; 
v_logExceptions_boxed_4042_ = lean_unbox(v_logExceptions_4031_);
v_res_4043_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4030_, v_logExceptions_boxed_4042_, v_onErr_4032_, v_init_4033_, v_cfg_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object* v_eval_4044_, lean_object* v_init_4045_, lean_object* v_cfg_4046_, lean_object* v_onErr_4047_, uint8_t v_logExceptions_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v___x_4052_; lean_object* v___f_4053_; uint8_t v___y_4055_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v___x_4052_ = lean_box(v_logExceptions_4048_);
lean_inc_n(v_cfg_4046_, 2);
lean_inc(v_init_4045_);
v___f_4053_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4053_, 0, v_eval_4044_);
lean_closure_set(v___f_4053_, 1, v___x_4052_);
lean_closure_set(v___f_4053_, 2, v_onErr_4047_);
lean_closure_set(v___f_4053_, 3, v_init_4045_);
lean_closure_set(v___f_4053_, 4, v_cfg_4046_);
v___x_4058_ = lean_unsigned_to_nat(0u);
v___x_4059_ = l_Lean_Syntax_matchesNull(v_cfg_4046_, v___x_4058_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; 
v___x_4060_ = l_Lean_Syntax_getNumArgs(v_cfg_4046_);
v___x_4061_ = lean_unsigned_to_nat(1u);
v___x_4062_ = lean_nat_dec_eq(v___x_4060_, v___x_4061_);
lean_dec(v___x_4060_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; 
lean_dec(v_cfg_4046_);
lean_dec(v_init_4045_);
v___x_4063_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4053_, v_a_4049_, v_a_4050_);
return v___x_4063_;
}
else
{
lean_object* v___x_4064_; uint8_t v___x_4065_; 
v___x_4064_ = l_Lean_Syntax_getArg(v_cfg_4046_, v___x_4058_);
lean_dec(v_cfg_4046_);
v___x_4065_ = l_Lean_Syntax_matchesNull(v___x_4064_, v___x_4058_);
v___y_4055_ = v___x_4065_;
goto v___jp_4054_;
}
}
else
{
lean_dec(v_cfg_4046_);
v___y_4055_ = v___x_4059_;
goto v___jp_4054_;
}
v___jp_4054_:
{
if (v___y_4055_ == 0)
{
lean_object* v___x_4056_; 
lean_dec(v_init_4045_);
v___x_4056_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4053_, v_a_4049_, v_a_4050_);
return v___x_4056_;
}
else
{
lean_object* v___x_4057_; 
lean_dec_ref(v___f_4053_);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v_init_4045_);
return v___x_4057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object* v_eval_4066_, lean_object* v_init_4067_, lean_object* v_cfg_4068_, lean_object* v_onErr_4069_, lean_object* v_logExceptions_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
uint8_t v_logExceptions_boxed_4074_; lean_object* v_res_4075_; 
v_logExceptions_boxed_4074_ = lean_unbox(v_logExceptions_4070_);
v_res_4075_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4066_, v_init_4067_, v_cfg_4068_, v_onErr_4069_, v_logExceptions_boxed_4074_, v_a_4071_, v_a_4072_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object* v_00_u03b1_4076_, lean_object* v_eval_4077_, lean_object* v_init_4078_, lean_object* v_cfg_4079_, lean_object* v_onErr_4080_, uint8_t v_logExceptions_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4077_, v_init_4078_, v_cfg_4079_, v_onErr_4080_, v_logExceptions_4081_, v_a_4082_, v_a_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object* v_00_u03b1_4086_, lean_object* v_eval_4087_, lean_object* v_init_4088_, lean_object* v_cfg_4089_, lean_object* v_onErr_4090_, lean_object* v_logExceptions_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
uint8_t v_logExceptions_boxed_4095_; lean_object* v_res_4096_; 
v_logExceptions_boxed_4095_ = lean_unbox(v_logExceptions_4091_);
v_res_4096_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(v_00_u03b1_4086_, v_eval_4087_, v_init_4088_, v_cfg_4089_, v_onErr_4090_, v_logExceptions_boxed_4095_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object* v_eval_4097_, uint8_t v_logExceptions_4098_, lean_object* v_onErr_4099_, lean_object* v_init_4100_, lean_object* v_cfgs_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_4097_, v_logExceptions_4098_, v_onErr_4099_, v_init_4100_, v_cfgs_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object* v_eval_4110_, lean_object* v_logExceptions_4111_, lean_object* v_onErr_4112_, lean_object* v_init_4113_, lean_object* v_cfgs_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
uint8_t v_logExceptions_boxed_4122_; lean_object* v_res_4123_; 
v_logExceptions_boxed_4122_ = lean_unbox(v_logExceptions_4111_);
v_res_4123_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4110_, v_logExceptions_boxed_4122_, v_onErr_4112_, v_init_4113_, v_cfgs_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec_ref(v_cfgs_4114_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object* v_eval_4124_, lean_object* v_init_4125_, lean_object* v_cfgs_4126_, lean_object* v_onErr_4127_, uint8_t v_logExceptions_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4132_ = lean_array_get_size(v_cfgs_4126_);
v___x_4133_ = lean_unsigned_to_nat(0u);
v___x_4134_ = lean_nat_dec_eq(v___x_4132_, v___x_4133_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v___f_4136_; lean_object* v___x_4137_; 
v___x_4135_ = lean_box(v_logExceptions_4128_);
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4136_, 0, v_eval_4124_);
lean_closure_set(v___f_4136_, 1, v___x_4135_);
lean_closure_set(v___f_4136_, 2, v_onErr_4127_);
lean_closure_set(v___f_4136_, 3, v_init_4125_);
lean_closure_set(v___f_4136_, 4, v_cfgs_4126_);
v___x_4137_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4136_, v_a_4129_, v_a_4130_);
return v___x_4137_;
}
else
{
lean_object* v___x_4138_; 
lean_dec_ref(v_onErr_4127_);
lean_dec_ref(v_cfgs_4126_);
lean_dec_ref(v_eval_4124_);
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v_init_4125_);
return v___x_4138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object* v_eval_4139_, lean_object* v_init_4140_, lean_object* v_cfgs_4141_, lean_object* v_onErr_4142_, lean_object* v_logExceptions_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
uint8_t v_logExceptions_boxed_4147_; lean_object* v_res_4148_; 
v_logExceptions_boxed_4147_ = lean_unbox(v_logExceptions_4143_);
v_res_4148_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4139_, v_init_4140_, v_cfgs_4141_, v_onErr_4142_, v_logExceptions_boxed_4147_, v_a_4144_, v_a_4145_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object* v_00_u03b1_4149_, lean_object* v_eval_4150_, lean_object* v_init_4151_, lean_object* v_cfgs_4152_, lean_object* v_onErr_4153_, uint8_t v_logExceptions_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4150_, v_init_4151_, v_cfgs_4152_, v_onErr_4153_, v_logExceptions_4154_, v_a_4155_, v_a_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object* v_00_u03b1_4159_, lean_object* v_eval_4160_, lean_object* v_init_4161_, lean_object* v_cfgs_4162_, lean_object* v_onErr_4163_, lean_object* v_logExceptions_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
uint8_t v_logExceptions_boxed_4168_; lean_object* v_res_4169_; 
v_logExceptions_boxed_4168_ = lean_unbox(v_logExceptions_4164_);
v_res_4169_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(v_00_u03b1_4159_, v_eval_4160_, v_init_4161_, v_cfgs_4162_, v_onErr_4163_, v_logExceptions_boxed_4168_, v_a_4165_, v_a_4166_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
return v_res_4169_;
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

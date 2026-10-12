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
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27;
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
lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(lean_object* v_inst_1_, lean_object* v_stx_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
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
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermWithRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_stx_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_res_37_;
v_res_37_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_1_, v_stx_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
stack->m_obj
 = v_res_37_;
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
lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_, lean_object* v_stx_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_49_, v_stx_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
return v___x_58_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermWithRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_49_ = stack[1].m_obj;
lean_object* v_stx_50_ = stack[2].m_obj;
lean_object* v_a_51_ = stack[3].m_obj;
lean_object* v_a_52_ = stack[4].m_obj;
lean_object* v_a_53_ = stack[5].m_obj;
lean_object* v_a_54_ = stack[6].m_obj;
lean_object* v_a_55_ = stack[7].m_obj;
lean_object* v_a_56_ = stack[8].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Elab_ConfigEval_evalTermWithRef(lean_box(0), v_inst_49_, v_stx_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___boxed(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_stx_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Elab_ConfigEval_evalTermWithRef(v_00_u03b1_60_, v_inst_61_, v_stx_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_70_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_instMonadEIO___redArg();
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0);
v___x_73_ = l_StateRefT_x27_instMonad___redArg(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_82_; lean_object* v___f_83_; 
v___x_82_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_83_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_83_, 0, v___x_82_);
return v___f_83_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_84_; lean_object* v___f_85_; 
v___x_84_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_85_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_85_, 0, v___x_84_);
return v___f_85_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12(void){
_start:
{
lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___x_88_; 
v___f_86_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11);
v___f_87_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v___f_87_);
lean_ctor_set(v___x_88_, 1, v___f_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13(void){
_start:
{
lean_object* v___x_89_; lean_object* v___f_90_; 
v___x_89_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_90_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_90_, 0, v___x_89_);
return v___f_90_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14(void){
_start:
{
lean_object* v___x_91_; lean_object* v___f_92_; 
v___x_91_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_92_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_92_, 0, v___x_91_);
return v___f_92_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15(void){
_start:
{
lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
v___f_93_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14);
v___f_94_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___f_94_);
lean_ctor_set(v___x_95_, 1, v___f_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; 
v___x_96_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_97_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
return v___f_97_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17(void){
_start:
{
lean_object* v___x_98_; lean_object* v___f_99_; 
v___x_98_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_99_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_99_, 0, v___x_98_);
return v___f_99_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18(void){
_start:
{
lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_100_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17);
v___f_101_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___f_101_);
lean_ctor_set(v___x_102_, 1, v___f_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19(void){
_start:
{
lean_object* v___x_103_; lean_object* v___f_104_; 
v___x_103_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_104_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_104_, 0, v___x_103_);
return v___f_104_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20(void){
_start:
{
lean_object* v___x_105_; lean_object* v___f_106_; 
v___x_105_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_106_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_106_, 0, v___x_105_);
return v___f_106_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21(void){
_start:
{
lean_object* v___f_107_; lean_object* v___f_108_; lean_object* v___x_109_; 
v___f_107_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20);
v___f_108_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___f_108_);
lean_ctor_set(v___x_109_, 1, v___f_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_111_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23));
v___x_114_ = l_Lean_stringToMessageData(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25));
v___x_117_ = l_Lean_stringToMessageData(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27));
v___x_120_ = l_Lean_stringToMessageData(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
v___x_123_ = l_Lean_stringToMessageData(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31));
v___x_126_ = l_Lean_stringToMessageData(v___x_125_);
return v___x_126_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(lean_object* v_inst_127_, lean_object* v_stx_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; lean_object* v_toApplicative_137_; lean_object* v_toFunctor_138_; lean_object* v_toSeq_139_; lean_object* v_toSeqLeft_140_; lean_object* v_toSeqRight_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_toApplicative_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_393_; 
v___x_136_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1);
v_toApplicative_137_ = lean_ctor_get(v___x_136_, 0);
v_toFunctor_138_ = lean_ctor_get(v_toApplicative_137_, 0);
v_toSeq_139_ = lean_ctor_get(v_toApplicative_137_, 2);
v_toSeqLeft_140_ = lean_ctor_get(v_toApplicative_137_, 3);
v_toSeqRight_141_ = lean_ctor_get(v_toApplicative_137_, 4);
v___f_142_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2));
v___f_143_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_138_, 2);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_144_, 0, v_toFunctor_138_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_145_, 0, v_toFunctor_138_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___f_144_);
lean_ctor_set(v___x_146_, 1, v___f_145_);
lean_inc(v_toSeqRight_141_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeqRight_141_);
lean_inc(v_toSeqLeft_140_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_148_, 0, v_toSeqLeft_140_);
lean_inc(v_toSeq_139_);
v___f_149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_149_, 0, v_toSeq_139_);
v___x_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_150_, 0, v___x_146_);
lean_ctor_set(v___x_150_, 1, v___f_142_);
lean_ctor_set(v___x_150_, 2, v___f_149_);
lean_ctor_set(v___x_150_, 3, v___f_148_);
lean_ctor_set(v___x_150_, 4, v___f_147_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___f_143_);
v___x_152_ = l_StateRefT_x27_instMonad___redArg(v___x_151_);
v_toApplicative_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_152_, 1);
lean_dec(v_unused_394_);
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_393_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_toApplicative_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_393_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_toFunctor_157_; lean_object* v_toSeq_158_; lean_object* v_toSeqLeft_159_; lean_object* v_toSeqRight_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_391_; 
v_toFunctor_157_ = lean_ctor_get(v_toApplicative_153_, 0);
v_toSeq_158_ = lean_ctor_get(v_toApplicative_153_, 2);
v_toSeqLeft_159_ = lean_ctor_get(v_toApplicative_153_, 3);
v_toSeqRight_160_ = lean_ctor_get(v_toApplicative_153_, 4);
v_isSharedCheck_391_ = !lean_is_exclusive(v_toApplicative_153_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_toApplicative_153_, 1);
lean_dec(v_unused_392_);
v___x_162_ = v_toApplicative_153_;
v_isShared_163_ = v_isSharedCheck_391_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_toSeqRight_160_);
lean_inc(v_toSeqLeft_159_);
lean_inc(v_toSeq_158_);
lean_inc(v_toFunctor_157_);
lean_dec(v_toApplicative_153_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_391_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_173_; 
v___f_164_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4));
v___f_165_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5));
lean_inc_ref(v_toFunctor_157_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_166_, 0, v_toFunctor_157_);
v___f_167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_167_, 0, v_toFunctor_157_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___f_166_);
lean_ctor_set(v___x_168_, 1, v___f_167_);
v___f_169_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_169_, 0, v_toSeqRight_160_);
v___f_170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_170_, 0, v_toSeqLeft_159_);
v___f_171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_171_, 0, v_toSeq_158_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 4, v___f_169_);
lean_ctor_set(v___x_162_, 3, v___f_170_);
lean_ctor_set(v___x_162_, 2, v___f_171_);
lean_ctor_set(v___x_162_, 1, v___f_164_);
lean_ctor_set(v___x_162_, 0, v___x_168_);
v___x_173_ = v___x_162_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___f_164_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v___f_171_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v___f_170_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v___f_169_);
v___x_173_ = v_reuseFailAlloc_390_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___f_165_);
lean_ctor_set(v___x_155_, 0, v___x_173_);
v___x_175_ = v___x_155_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___f_165_);
v___x_175_ = v_reuseFailAlloc_389_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v_toApplicative_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_387_; 
v___x_176_ = l_StateRefT_x27_instMonad___redArg(v___x_175_);
v_toApplicative_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_176_, 1);
lean_dec(v_unused_388_);
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_387_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_toApplicative_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_387_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_toFunctor_181_; lean_object* v_toSeq_182_; lean_object* v_toSeqLeft_183_; lean_object* v_toSeqRight_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_385_; 
v_toFunctor_181_ = lean_ctor_get(v_toApplicative_177_, 0);
v_toSeq_182_ = lean_ctor_get(v_toApplicative_177_, 2);
v_toSeqLeft_183_ = lean_ctor_get(v_toApplicative_177_, 3);
v_toSeqRight_184_ = lean_ctor_get(v_toApplicative_177_, 4);
v_isSharedCheck_385_ = !lean_is_exclusive(v_toApplicative_177_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_toApplicative_177_, 1);
lean_dec(v_unused_386_);
v___x_186_ = v_toApplicative_177_;
v_isShared_187_ = v_isSharedCheck_385_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_toSeqRight_184_);
lean_inc(v_toSeqLeft_183_);
lean_inc(v_toSeq_182_);
lean_inc(v_toFunctor_181_);
lean_dec(v_toApplicative_177_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_385_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___x_197_; 
v___f_188_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6));
v___f_189_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7));
lean_inc_ref(v_toFunctor_181_);
v___f_190_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_190_, 0, v_toFunctor_181_);
v___f_191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_191_, 0, v_toFunctor_181_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___f_190_);
lean_ctor_set(v___x_192_, 1, v___f_191_);
v___f_193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_193_, 0, v_toSeqRight_184_);
v___f_194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_194_, 0, v_toSeqLeft_183_);
v___f_195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_195_, 0, v_toSeq_182_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 4, v___f_193_);
lean_ctor_set(v___x_186_, 3, v___f_194_);
lean_ctor_set(v___x_186_, 2, v___f_195_);
lean_ctor_set(v___x_186_, 1, v___f_188_);
lean_ctor_set(v___x_186_, 0, v___x_192_);
v___x_197_ = v___x_186_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___f_188_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___f_195_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v___f_194_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v___f_193_);
v___x_197_ = v_reuseFailAlloc_384_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___f_189_);
lean_ctor_set(v___x_179_, 0, v___x_197_);
v___x_199_ = v___x_179_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___f_189_);
v___x_199_ = v_reuseFailAlloc_383_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; lean_object* v_toMonadQuotation_201_; lean_object* v_toMonadRef_202_; lean_object* v___x_203_; lean_object* v_getMCtx_204_; lean_object* v_modifyMCtx_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___f_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_evalExpr_217_; lean_object* v_expectedType_x3f_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_382_; 
v___x_200_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_201_ = lean_ctor_get(v___x_200_, 0);
v_toMonadRef_202_ = lean_ctor_get(v_toMonadQuotation_201_, 0);
v___x_203_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_204_ = lean_ctor_get(v___x_203_, 0);
v_modifyMCtx_205_ = lean_ctor_get(v___x_203_, 1);
v___f_206_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8));
v___x_207_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9));
lean_inc(v_modifyMCtx_205_);
v___f_208_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_208_, 0, v_modifyMCtx_205_);
lean_closure_set(v___f_208_, 1, v___x_207_);
lean_inc(v_getMCtx_204_);
v___x_209_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, lean_box(0));
lean_closure_set(v___x_209_, 2, lean_box(0));
lean_closure_set(v___x_209_, 3, lean_box(0));
lean_closure_set(v___x_209_, 4, v_getMCtx_204_);
v___f_210_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_210_, 0, v___f_208_);
lean_closure_set(v___f_210_, 1, v___f_206_);
v___x_211_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_211_, 0, lean_box(0));
lean_closure_set(v___x_211_, 1, v___x_209_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___f_210_);
v___x_213_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_214_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_202_);
v___x_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v_toMonadRef_202_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
v___x_216_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22);
v_evalExpr_217_ = lean_ctor_get(v_inst_127_, 0);
v_expectedType_x3f_218_ = lean_ctor_get(v_inst_127_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_inst_127_);
if (v_isSharedCheck_382_ == 0)
{
v___x_220_ = v_inst_127_;
v_isShared_221_ = v_isSharedCheck_382_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_expectedType_x3f_218_);
lean_inc(v_evalExpr_217_);
lean_dec(v_inst_127_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_382_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_toCold_227_; lean_object* v_currRecDepth_228_; lean_object* v_ref_229_; uint16_t v_optionFlags_230_; uint8_t v_suppressElabErrors_231_; uint8_t v_isRecordingDeps_232_; uint8_t v___x_233_; lean_object* v_ref_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_222_ = 1;
v___x_223_ = lean_box(0);
v___x_224_ = lean_box(v___x_222_);
v___x_225_ = lean_box(v___x_222_);
lean_inc(v_expectedType_x3f_218_);
lean_inc(v_stx_128_);
v___x_226_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_226_, 0, v_stx_128_);
lean_closure_set(v___x_226_, 1, v_expectedType_x3f_218_);
lean_closure_set(v___x_226_, 2, v___x_224_);
lean_closure_set(v___x_226_, 3, v___x_225_);
lean_closure_set(v___x_226_, 4, v___x_223_);
v_toCold_227_ = lean_ctor_get(v_a_133_, 0);
v_currRecDepth_228_ = lean_ctor_get(v_a_133_, 1);
v_ref_229_ = lean_ctor_get(v_a_133_, 2);
v_optionFlags_230_ = lean_ctor_get_uint16(v_a_133_, sizeof(void*)*3);
v_suppressElabErrors_231_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*3 + 2);
v_isRecordingDeps_232_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*3 + 3);
v___x_233_ = 1;
v_ref_234_ = l_Lean_replaceRef(v_stx_128_, v_ref_229_);
lean_dec(v_stx_128_);
lean_inc(v_currRecDepth_228_);
lean_inc_ref(v_toCold_227_);
v___x_235_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_235_, 0, v_toCold_227_);
lean_ctor_set(v___x_235_, 1, v_currRecDepth_228_);
lean_ctor_set(v___x_235_, 2, v_ref_234_);
lean_ctor_set_uint16(v___x_235_, sizeof(void*)*3, v_optionFlags_230_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 2, v_suppressElabErrors_231_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 3, v_isRecordingDeps_232_);
v___x_236_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_226_, v___x_233_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v___x_235_, v_a_134_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_3629__overap_238_; lean_object* v___x_239_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
lean_inc_ref(v___x_199_);
v___x_3629__overap_238_ = l_Lean_instantiateMVars___redArg(v___x_199_, v___x_212_, v_a_237_);
lean_inc(v_a_134_);
lean_inc_ref(v___x_235_);
lean_inc(v_a_132_);
lean_inc_ref(v_a_131_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
v___x_239_ = lean_apply_7(v___x_3629__overap_238_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v___x_235_, v_a_134_, lean_box(0));
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; uint8_t v___y_267_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; uint8_t v___x_354_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v___x_354_ = l_Lean_Expr_hasSorry(v_a_240_);
if (v___x_354_ == 0)
{
v___y_297_ = v_a_129_;
v___y_298_ = v_a_130_;
v___y_299_ = v_a_131_;
v___y_300_ = v_a_132_;
v___y_301_ = v___x_235_;
v___y_302_ = v_a_134_;
goto v___jp_296_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = l_Lean_Expr_hasSyntheticSorry(v_a_240_);
if (v___x_355_ == 0)
{
v___y_335_ = v_a_129_;
v___y_336_ = v_a_130_;
v___y_337_ = v_a_131_;
v___y_338_ = v_a_132_;
v___y_339_ = v___x_235_;
v___y_340_ = v_a_134_;
goto v___jp_334_;
}
else
{
lean_object* v___x_3637__overap_356_; lean_object* v___x_357_; 
v___x_3637__overap_356_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_216_);
lean_inc(v_a_134_);
lean_inc_ref(v___x_235_);
lean_inc(v_a_132_);
lean_inc_ref(v_a_131_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
v___x_357_ = lean_apply_7(v___x_3637__overap_356_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v___x_235_, v_a_134_, lean_box(0));
if (lean_obj_tag(v___x_357_) == 0)
{
lean_dec_ref_known(v___x_357_, 1);
v___y_335_ = v_a_129_;
v___y_336_ = v_a_130_;
v___y_337_ = v_a_131_;
v___y_338_ = v_a_132_;
v___y_339_ = v___x_235_;
v___y_340_ = v_a_134_;
goto v___jp_334_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_240_);
lean_dec_ref_known(v___x_235_, 3);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref(v_evalExpr_217_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
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
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 7);
lean_ctor_set(v___x_220_, 1, v___x_250_);
lean_ctor_set(v___x_220_, 0, v___x_249_);
v___x_252_ = v___x_220_;
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
lean_object* v___x_253_; lean_object* v___x_3631__overap_254_; lean_object* v___x_255_; 
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___y_248_);
v___x_3631__overap_254_ = l_Lean_throwError___redArg(v___x_199_, v___x_215_, v___x_253_);
lean_inc(v___y_243_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_242_);
v___x_255_ = lean_apply_7(v___x_3631__overap_254_, v___y_242_, v___y_247_, v___y_244_, v___y_245_, v___y_246_, v___y_243_, lean_box(0));
return v___x_255_;
}
}
v___jp_257_:
{
if (v___y_267_ == 0)
{
if (lean_obj_tag(v___y_263_) == 0)
{
lean_dec_ref_known(v___y_263_, 2);
lean_dec_ref(v___y_265_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
return v___y_266_;
}
else
{
lean_object* v_id_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_282_; 
v_id_268_ = lean_ctor_get(v___y_263_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___y_263_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___y_263_, 1);
lean_dec(v_unused_283_);
v___x_270_ = v___y_263_;
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_id_268_);
lean_dec(v___y_263_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
uint8_t v___x_272_; 
v___x_272_ = l_Lean_instBEqInternalExceptionId_beq(v___y_262_, v_id_268_);
lean_dec(v_id_268_);
if (v___x_272_ == 0)
{
lean_del_object(v___x_270_);
lean_dec_ref(v___y_265_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
return v___y_266_;
}
else
{
lean_dec_ref(v___y_266_);
if (lean_obj_tag(v_expectedType_x3f_218_) == 1)
{
lean_object* v_val_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v_val_273_ = lean_ctor_get(v_expectedType_x3f_218_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v_expectedType_x3f_218_, 1);
v___x_274_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26);
v___x_275_ = l_Lean_MessageData_ofExpr(v_val_273_);
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 7);
lean_ctor_set(v___x_270_, 1, v___x_275_);
lean_ctor_set(v___x_270_, 0, v___x_274_);
v___x_277_ = v___x_270_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_275_);
v___x_277_ = v_reuseFailAlloc_280_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___y_242_ = v___y_258_;
v___y_243_ = v___y_259_;
v___y_244_ = v___y_260_;
v___y_245_ = v___y_261_;
v___y_246_ = v___y_265_;
v___y_247_ = v___y_264_;
v___y_248_ = v___x_279_;
goto v___jp_241_;
}
}
else
{
lean_object* v___x_281_; 
lean_del_object(v___x_270_);
lean_dec(v_expectedType_x3f_218_);
v___x_281_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_242_ = v___y_258_;
v___y_243_ = v___y_259_;
v___y_244_ = v___y_260_;
v___y_245_ = v___y_261_;
v___y_246_ = v___y_265_;
v___y_247_ = v___y_264_;
v___y_248_ = v___x_281_;
goto v___jp_241_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_265_);
lean_dec_ref(v___y_263_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
return v___y_266_;
}
}
v___jp_284_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v___y_290_);
lean_inc_ref(v___y_289_);
lean_inc(v___y_288_);
lean_inc_ref(v___y_287_);
lean_inc(v_a_240_);
v___x_292_ = lean_apply_6(v_evalExpr_217_, v_a_240_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, lean_box(0));
if (lean_obj_tag(v___x_292_) == 0)
{
lean_dec_ref(v___y_289_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
return v___x_292_;
}
else
{
lean_object* v_a_293_; uint8_t v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
v___x_294_ = l_Lean_Exception_isInterrupt(v_a_293_);
if (v___x_294_ == 0)
{
uint8_t v___x_295_; 
lean_inc(v_a_293_);
v___x_295_ = l_Lean_Exception_isRuntime(v_a_293_);
v___y_258_ = v___y_285_;
v___y_259_ = v___y_290_;
v___y_260_ = v___y_287_;
v___y_261_ = v___y_288_;
v___y_262_ = v___x_291_;
v___y_263_ = v_a_293_;
v___y_264_ = v___y_286_;
v___y_265_ = v___y_289_;
v___y_266_ = v___x_292_;
v___y_267_ = v___x_295_;
goto v___jp_257_;
}
else
{
v___y_258_ = v___y_285_;
v___y_259_ = v___y_290_;
v___y_260_ = v___y_287_;
v___y_261_ = v___y_288_;
v___y_262_ = v___x_291_;
v___y_263_ = v_a_293_;
v___y_264_ = v___y_286_;
v___y_265_ = v___y_289_;
v___y_266_ = v___x_292_;
v___y_267_ = v___x_294_;
goto v___jp_257_;
}
}
}
v___jp_296_:
{
lean_object* v___x_303_; 
lean_inc(v_a_240_);
v___x_303_ = l_Lean_Meta_getMVars(v_a_240_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
v___x_305_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_304_, v___x_223_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v_a_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; uint8_t v___x_307_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = lean_unbox(v_a_306_);
lean_dec(v_a_306_);
if (v___x_307_ == 0)
{
v___y_285_ = v___y_297_;
v___y_286_ = v___y_298_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_300_;
v___y_289_ = v___y_301_;
v___y_290_ = v___y_302_;
goto v___jp_284_;
}
else
{
lean_object* v___x_3633__overap_308_; lean_object* v___x_309_; 
v___x_3633__overap_308_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_216_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc(v___y_298_);
lean_inc_ref(v___y_297_);
v___x_309_ = lean_apply_7(v___x_3633__overap_308_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, lean_box(0));
if (lean_obj_tag(v___x_309_) == 0)
{
lean_dec_ref_known(v___x_309_, 1);
v___y_285_ = v___y_297_;
v___y_286_ = v___y_298_;
v___y_287_ = v___y_299_;
v___y_288_ = v___y_300_;
v___y_289_ = v___y_301_;
v___y_290_ = v___y_302_;
goto v___jp_284_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v___y_301_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref(v_evalExpr_217_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v___y_301_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref(v_evalExpr_217_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
v_a_318_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_305_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_305_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v___y_301_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref(v_evalExpr_217_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
v_a_326_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_303_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_303_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
v___jp_334_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_3635__overap_344_; lean_object* v___x_345_; 
v___x_341_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32);
lean_inc(v_a_240_);
v___x_342_ = l_Lean_indentExpr(v_a_240_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
lean_inc_ref(v___x_215_);
lean_inc_ref(v___x_199_);
v___x_3635__overap_344_ = l_Lean_throwError___redArg(v___x_199_, v___x_215_, v___x_343_);
lean_inc(v___y_340_);
lean_inc_ref(v___y_339_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
v___x_345_ = lean_apply_7(v___x_3635__overap_344_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, lean_box(0));
if (lean_obj_tag(v___x_345_) == 0)
{
lean_dec_ref_known(v___x_345_, 1);
v___y_297_ = v___y_335_;
v___y_298_ = v___y_336_;
v___y_299_ = v___y_337_;
v___y_300_ = v___y_338_;
v___y_301_ = v___y_339_;
v___y_302_ = v___y_340_;
goto v___jp_296_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___y_339_);
lean_dec(v_a_240_);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref(v_evalExpr_217_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref_known(v___x_235_, 3);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref(v_evalExpr_217_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref(v___x_199_);
v_a_366_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_239_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_239_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref_known(v___x_235_, 3);
lean_del_object(v___x_220_);
lean_dec(v_expectedType_x3f_218_);
lean_dec_ref(v_evalExpr_217_);
lean_dec_ref_known(v___x_215_, 3);
lean_dec_ref_known(v___x_212_, 2);
lean_dec_ref(v___x_199_);
v_a_374_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_236_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_236_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
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
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_127_ = stack[0].m_obj;
lean_object* v_stx_128_ = stack[1].m_obj;
lean_object* v_a_129_ = stack[2].m_obj;
lean_object* v_a_130_ = stack[3].m_obj;
lean_object* v_a_131_ = stack[4].m_obj;
lean_object* v_a_132_ = stack[5].m_obj;
lean_object* v_a_133_ = stack[6].m_obj;
lean_object* v_a_134_ = stack[7].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_127_, v_stx_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___boxed(lean_object* v_inst_396_, lean_object* v_stx_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_396_, v_stx_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_405_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab(lean_object* v_00_u03b1_406_, lean_object* v_inst_407_, lean_object* v_stx_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_407_, v_stx_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_416_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_407_ = stack[1].m_obj;
lean_object* v_stx_408_ = stack[2].m_obj;
lean_object* v_a_409_ = stack[3].m_obj;
lean_object* v_a_410_ = stack[4].m_obj;
lean_object* v_a_411_ = stack[5].m_obj;
lean_object* v_a_412_ = stack[6].m_obj;
lean_object* v_a_413_ = stack[7].m_obj;
lean_object* v_a_414_ = stack[8].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lean_Elab_ConfigEval_evalExprWithElab(lean_box(0), v_inst_407_, v_stx_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___boxed(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_stx_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Elab_ConfigEval_evalExprWithElab(v_00_u03b1_418_, v_inst_419_, v_stx_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_428_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_stx_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_evalTerm_439_; lean_object* v_toCold_440_; lean_object* v_currRecDepth_441_; lean_object* v_ref_442_; uint16_t v_optionFlags_443_; uint8_t v_suppressElabErrors_444_; uint8_t v_isRecordingDeps_445_; lean_object* v___x_446_; lean_object* v_ref_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_evalTerm_439_ = lean_ctor_get(v_inst_429_, 0);
lean_inc_ref(v_evalTerm_439_);
lean_dec_ref(v_inst_429_);
v_toCold_440_ = lean_ctor_get(v_a_436_, 0);
v_currRecDepth_441_ = lean_ctor_get(v_a_436_, 1);
v_ref_442_ = lean_ctor_get(v_a_436_, 2);
v_optionFlags_443_ = lean_ctor_get_uint16(v_a_436_, sizeof(void*)*3);
v_suppressElabErrors_444_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 2);
v_isRecordingDeps_445_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 3);
v___x_446_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_447_ = l_Lean_replaceRef(v_stx_431_, v_ref_442_);
lean_inc(v_currRecDepth_441_);
lean_inc_ref(v_toCold_440_);
v___x_448_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_448_, 0, v_toCold_440_);
lean_ctor_set(v___x_448_, 1, v_currRecDepth_441_);
lean_ctor_set(v___x_448_, 2, v_ref_447_);
lean_ctor_set_uint16(v___x_448_, sizeof(void*)*3, v_optionFlags_443_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*3 + 2, v_suppressElabErrors_444_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*3 + 3, v_isRecordingDeps_445_);
lean_inc(v_a_437_);
lean_inc_ref(v___x_448_);
lean_inc(v_a_435_);
lean_inc_ref(v_a_434_);
lean_inc(v_a_433_);
lean_inc_ref(v_a_432_);
lean_inc(v_stx_431_);
v___x_449_ = lean_apply_8(v_evalTerm_439_, v_stx_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v___x_448_, v_a_437_, lean_box(0));
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref_known(v___x_448_, 3);
lean_dec(v_stx_431_);
lean_dec_ref(v_inst_430_);
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_458_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_fst_454_; lean_object* v___x_456_; 
v_fst_454_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_fst_454_);
lean_dec(v_a_450_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_fst_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_473_; 
v_a_459_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_473_ == 0)
{
v___x_461_ = v___x_449_;
v_isShared_462_ = v_isSharedCheck_473_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_449_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_473_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
lean_inc(v_a_459_);
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_472_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
uint8_t v___y_466_; uint8_t v___x_470_; 
v___x_470_ = l_Lean_Exception_isInterrupt(v_a_459_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
lean_inc(v_a_459_);
v___x_471_ = l_Lean_Exception_isRuntime(v_a_459_);
v___y_466_ = v___x_471_;
goto v___jp_465_;
}
else
{
v___y_466_ = v___x_470_;
goto v___jp_465_;
}
v___jp_465_:
{
if (v___y_466_ == 0)
{
if (lean_obj_tag(v_a_459_) == 0)
{
lean_dec_ref_known(v_a_459_, 2);
lean_dec_ref_known(v___x_448_, 3);
lean_dec(v_stx_431_);
lean_dec_ref(v_inst_430_);
return v___x_464_;
}
else
{
lean_object* v_id_467_; uint8_t v___x_468_; 
v_id_467_ = lean_ctor_get(v_a_459_, 0);
lean_inc(v_id_467_);
lean_dec_ref_known(v_a_459_, 2);
v___x_468_ = l_Lean_instBEqInternalExceptionId_beq(v___x_446_, v_id_467_);
lean_dec(v_id_467_);
if (v___x_468_ == 0)
{
lean_dec_ref_known(v___x_448_, 3);
lean_dec(v_stx_431_);
lean_dec_ref(v_inst_430_);
return v___x_464_;
}
else
{
lean_object* v___x_469_; 
lean_dec_ref(v___x_464_);
v___x_469_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_430_, v_stx_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v___x_448_, v_a_437_);
lean_dec_ref_known(v___x_448_, 3);
return v___x_469_;
}
}
}
else
{
lean_dec(v_a_459_);
lean_dec_ref_known(v___x_448_, 3);
lean_dec(v_stx_431_);
lean_dec_ref(v_inst_430_);
return v___x_464_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_429_ = stack[0].m_obj;
lean_object* v_inst_430_ = stack[1].m_obj;
lean_object* v_stx_431_ = stack[2].m_obj;
lean_object* v_a_432_ = stack[3].m_obj;
lean_object* v_a_433_ = stack[4].m_obj;
lean_object* v_a_434_ = stack[5].m_obj;
lean_object* v_a_435_ = stack[6].m_obj;
lean_object* v_a_436_ = stack[7].m_obj;
lean_object* v_a_437_ = stack[8].m_obj;
lean_object* v_res_474_;
v_res_474_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_429_, v_inst_430_, v_stx_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_stx_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_475_, v_inst_476_, v_stx_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
return v_res_485_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(lean_object* v_00_u03b1_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_stx_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_487_, v_inst_488_, v_stx_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
return v___x_497_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_487_ = stack[1].m_obj;
lean_object* v_inst_488_ = stack[2].m_obj;
lean_object* v_stx_489_ = stack[3].m_obj;
lean_object* v_a_490_ = stack[4].m_obj;
lean_object* v_a_491_ = stack[5].m_obj;
lean_object* v_a_492_ = stack[6].m_obj;
lean_object* v_a_493_ = stack[7].m_obj;
lean_object* v_a_494_ = stack[8].m_obj;
lean_object* v_a_495_ = stack[9].m_obj;
lean_object* v_res_498_;
v_res_498_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(lean_box(0), v_inst_487_, v_inst_488_, v_stx_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___boxed(lean_object* v_00_u03b1_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_stx_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(v_00_u03b1_499_, v_inst_500_, v_inst_501_, v_stx_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4));
lean_inc(v_x_529_);
v___x_531_ = l_Lean_Syntax_isOfKind(v_x_529_, v___x_530_);
if (v___x_531_ == 0)
{
return v_x_529_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = l_Lean_Syntax_getArg(v_x_529_, v___x_532_);
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6));
lean_inc(v___x_533_);
v___x_535_ = l_Lean_Syntax_isOfKind(v___x_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_dec(v___x_533_);
return v_x_529_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = l_Lean_Syntax_getArg(v___x_533_, v___x_536_);
lean_dec(v___x_533_);
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8));
lean_inc(v___x_537_);
v___x_539_ = l_Lean_Syntax_isOfKind(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v___x_537_);
return v_x_529_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = l_Lean_Syntax_getArg(v___x_537_, v___x_532_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v___x_542_ = l_Lean_Syntax_matchesIdent(v___x_540_, v___x_541_);
lean_dec(v___x_540_);
if (v___x_542_ == 0)
{
return v_x_529_;
}
else
{
lean_object* v_t_543_; 
v_t_543_ = l_Lean_Syntax_getArg(v_x_529_, v___x_536_);
lean_dec(v_x_529_);
v_x_529_ = v_t_543_;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(lean_object* v_expectedType_x3f_545_, lean_object* v_f_546_, lean_object* v_stx_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_toCold_555_; lean_object* v_currRecDepth_556_; lean_object* v_ref_557_; uint16_t v_optionFlags_558_; uint8_t v_suppressElabErrors_559_; uint8_t v_isRecordingDeps_560_; lean_object* v___x_561_; lean_object* v_ref_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_toCold_555_ = lean_ctor_get(v_a_552_, 0);
v_currRecDepth_556_ = lean_ctor_get(v_a_552_, 1);
v_ref_557_ = lean_ctor_get(v_a_552_, 2);
v_optionFlags_558_ = lean_ctor_get_uint16(v_a_552_, sizeof(void*)*3);
v_suppressElabErrors_559_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*3 + 2);
v_isRecordingDeps_560_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*3 + 3);
lean_inc(v_stx_547_);
v___x_561_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_547_);
v_ref_562_ = l_Lean_replaceRef(v_stx_547_, v_ref_557_);
lean_inc(v_currRecDepth_556_);
lean_inc_ref(v_toCold_555_);
v___x_563_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_563_, 0, v_toCold_555_);
lean_ctor_set(v___x_563_, 1, v_currRecDepth_556_);
lean_ctor_set(v___x_563_, 2, v_ref_562_);
lean_ctor_set_uint16(v___x_563_, sizeof(void*)*3, v_optionFlags_558_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*3 + 2, v_suppressElabErrors_559_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*3 + 3, v_isRecordingDeps_560_);
lean_inc(v_a_553_);
lean_inc(v_a_551_);
lean_inc_ref(v_a_550_);
lean_inc(v_a_549_);
lean_inc_ref(v_a_548_);
v___x_564_ = lean_apply_8(v_f_546_, v___x_561_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v___x_563_, v_a_553_, lean_box(0));
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_596_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_596_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_596_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_596_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_snd_569_; lean_object* v___x_570_; lean_object* v_infoState_571_; uint8_t v_enabled_572_; 
v_snd_569_ = lean_ctor_get(v_a_565_, 1);
v___x_570_ = lean_st_ref_get(v_a_553_);
v_infoState_571_ = lean_ctor_get(v___x_570_, 8);
lean_inc_ref(v_infoState_571_);
lean_dec(v___x_570_);
v_enabled_572_ = lean_ctor_get_uint8(v_infoState_571_, sizeof(void*)*3);
lean_dec_ref(v_infoState_571_);
if (v_enabled_572_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v_stx_547_);
lean_dec(v_expectedType_x3f_545_);
if (v_isShared_568_ == 0)
{
v___x_574_ = v___x_567_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_565_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; lean_object* v___x_579_; 
lean_del_object(v___x_567_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_box(0);
v___x_578_ = 0;
lean_inc(v_snd_569_);
v___x_579_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_547_, v_snd_569_, v_expectedType_x3f_545_, v___x_576_, v___x_577_, v___x_578_, v___x_578_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v___x_579_, 0);
lean_dec(v_unused_587_);
v___x_581_ = v___x_579_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_579_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_a_565_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_565_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_a_565_);
v_a_588_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_579_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_579_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_547_);
lean_dec(v_expectedType_x3f_545_);
return v___x_564_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedType_x3f_545_ = stack[0].m_obj;
lean_object* v_f_546_ = stack[1].m_obj;
lean_object* v_stx_547_ = stack[2].m_obj;
lean_object* v_a_548_ = stack[3].m_obj;
lean_object* v_a_549_ = stack[4].m_obj;
lean_object* v_a_550_ = stack[5].m_obj;
lean_object* v_a_551_ = stack[6].m_obj;
lean_object* v_a_552_ = stack[7].m_obj;
lean_object* v_a_553_ = stack[8].m_obj;
lean_object* v_res_597_;
v_res_597_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(v_expectedType_x3f_545_, v_f_546_, v_stx_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg___boxed(lean_object* v_expectedType_x3f_598_, lean_object* v_f_599_, lean_object* v_stx_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(v_expectedType_x3f_598_, v_f_599_, v_stx_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_608_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(lean_object* v_00_u03b1_609_, lean_object* v_expectedType_x3f_610_, lean_object* v_f_611_, lean_object* v_stx_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_toCold_620_; lean_object* v_currRecDepth_621_; lean_object* v_ref_622_; uint16_t v_optionFlags_623_; uint8_t v_suppressElabErrors_624_; uint8_t v_isRecordingDeps_625_; lean_object* v___x_626_; lean_object* v_ref_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_toCold_620_ = lean_ctor_get(v_a_617_, 0);
v_currRecDepth_621_ = lean_ctor_get(v_a_617_, 1);
v_ref_622_ = lean_ctor_get(v_a_617_, 2);
v_optionFlags_623_ = lean_ctor_get_uint16(v_a_617_, sizeof(void*)*3);
v_suppressElabErrors_624_ = lean_ctor_get_uint8(v_a_617_, sizeof(void*)*3 + 2);
v_isRecordingDeps_625_ = lean_ctor_get_uint8(v_a_617_, sizeof(void*)*3 + 3);
lean_inc(v_stx_612_);
v___x_626_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_612_);
v_ref_627_ = l_Lean_replaceRef(v_stx_612_, v_ref_622_);
lean_inc(v_currRecDepth_621_);
lean_inc_ref(v_toCold_620_);
v___x_628_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_628_, 0, v_toCold_620_);
lean_ctor_set(v___x_628_, 1, v_currRecDepth_621_);
lean_ctor_set(v___x_628_, 2, v_ref_627_);
lean_ctor_set_uint16(v___x_628_, sizeof(void*)*3, v_optionFlags_623_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*3 + 2, v_suppressElabErrors_624_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*3 + 3, v_isRecordingDeps_625_);
lean_inc(v_a_618_);
lean_inc(v_a_616_);
lean_inc_ref(v_a_615_);
lean_inc(v_a_614_);
lean_inc_ref(v_a_613_);
v___x_629_ = lean_apply_8(v_f_611_, v___x_626_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v___x_628_, v_a_618_, lean_box(0));
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_661_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_661_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_661_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_661_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_snd_634_; lean_object* v___x_635_; lean_object* v_infoState_636_; uint8_t v_enabled_637_; 
v_snd_634_ = lean_ctor_get(v_a_630_, 1);
v___x_635_ = lean_st_ref_get(v_a_618_);
v_infoState_636_ = lean_ctor_get(v___x_635_, 8);
lean_inc_ref(v_infoState_636_);
lean_dec(v___x_635_);
v_enabled_637_ = lean_ctor_get_uint8(v_infoState_636_, sizeof(void*)*3);
lean_dec_ref(v_infoState_636_);
if (v_enabled_637_ == 0)
{
lean_object* v___x_639_; 
lean_dec(v_stx_612_);
lean_dec(v_expectedType_x3f_610_);
if (v_isShared_633_ == 0)
{
v___x_639_ = v___x_632_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_630_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
lean_del_object(v___x_632_);
v___x_641_ = lean_box(0);
v___x_642_ = lean_box(0);
v___x_643_ = 0;
lean_inc(v_snd_634_);
v___x_644_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_612_, v_snd_634_, v_expectedType_x3f_610_, v___x_641_, v___x_642_, v___x_643_, v___x_643_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_652_);
v___x_646_ = v___x_644_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_644_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v_a_630_);
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_630_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_630_);
v_a_653_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_644_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_644_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_612_);
lean_dec(v_expectedType_x3f_610_);
return v___x_629_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedType_x3f_610_ = stack[1].m_obj;
lean_object* v_f_611_ = stack[2].m_obj;
lean_object* v_stx_612_ = stack[3].m_obj;
lean_object* v_a_613_ = stack[4].m_obj;
lean_object* v_a_614_ = stack[5].m_obj;
lean_object* v_a_615_ = stack[6].m_obj;
lean_object* v_a_616_ = stack[7].m_obj;
lean_object* v_a_617_ = stack[8].m_obj;
lean_object* v_a_618_ = stack[9].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(lean_box(0), v_expectedType_x3f_610_, v_f_611_, v_stx_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___boxed(lean_object* v_00_u03b1_663_, lean_object* v_expectedType_x3f_664_, lean_object* v_f_665_, lean_object* v_stx_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(v_00_u03b1_663_, v_expectedType_x3f_664_, v_f_665_, v_stx_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_674_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(lean_object* v_inst_675_, lean_object* v_f_676_, lean_object* v_stx_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_toExpr_685_; lean_object* v_toTypeExpr_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_744_; 
v_toExpr_685_ = lean_ctor_get(v_inst_675_, 0);
v_toTypeExpr_686_ = lean_ctor_get(v_inst_675_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_inst_675_);
if (v_isSharedCheck_744_ == 0)
{
v___x_688_ = v_inst_675_;
v_isShared_689_ = v_isSharedCheck_744_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_toTypeExpr_686_);
lean_inc(v_toExpr_685_);
lean_dec(v_inst_675_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_744_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_toCold_690_; lean_object* v_currRecDepth_691_; lean_object* v_ref_692_; uint16_t v_optionFlags_693_; uint8_t v_suppressElabErrors_694_; uint8_t v_isRecordingDeps_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_ref_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_toCold_690_ = lean_ctor_get(v_a_682_, 0);
v_currRecDepth_691_ = lean_ctor_get(v_a_682_, 1);
v_ref_692_ = lean_ctor_get(v_a_682_, 2);
v_optionFlags_693_ = lean_ctor_get_uint16(v_a_682_, sizeof(void*)*3);
v_suppressElabErrors_694_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 2);
v_isRecordingDeps_695_ = lean_ctor_get_uint8(v_a_682_, sizeof(void*)*3 + 3);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_toTypeExpr_686_);
lean_inc(v_stx_677_);
v___x_697_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_677_);
v_ref_698_ = l_Lean_replaceRef(v_stx_677_, v_ref_692_);
lean_inc(v_currRecDepth_691_);
lean_inc_ref(v_toCold_690_);
v___x_699_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_699_, 0, v_toCold_690_);
lean_ctor_set(v___x_699_, 1, v_currRecDepth_691_);
lean_ctor_set(v___x_699_, 2, v_ref_698_);
lean_ctor_set_uint16(v___x_699_, sizeof(void*)*3, v_optionFlags_693_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3 + 2, v_suppressElabErrors_694_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3 + 3, v_isRecordingDeps_695_);
lean_inc(v_a_683_);
lean_inc(v_a_681_);
lean_inc_ref(v_a_680_);
lean_inc(v_a_679_);
lean_inc_ref(v_a_678_);
v___x_700_ = lean_apply_8(v_f_676_, v___x_697_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v___x_699_, v_a_683_, lean_box(0));
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_735_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_735_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_735_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_735_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_inc(v_a_701_);
v___x_705_ = lean_apply_1(v_toExpr_685_, v_a_701_);
lean_inc_ref(v___x_705_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_705_);
lean_ctor_set(v___x_688_, 0, v_a_701_);
v___x_707_ = v___x_688_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_701_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_734_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v_infoState_709_; uint8_t v_enabled_710_; 
v___x_708_ = lean_st_ref_get(v_a_683_);
v_infoState_709_ = lean_ctor_get(v___x_708_, 8);
lean_inc_ref(v_infoState_709_);
lean_dec(v___x_708_);
v_enabled_710_ = lean_ctor_get_uint8(v_infoState_709_, sizeof(void*)*3);
lean_dec_ref(v_infoState_709_);
if (v_enabled_710_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v___x_705_);
lean_dec_ref_known(v___x_696_, 1);
lean_dec(v_stx_677_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; 
lean_del_object(v___x_703_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_box(0);
v___x_716_ = 0;
v___x_717_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_677_, v___x_705_, v___x_696_, v___x_714_, v___x_715_, v___x_716_, v___x_716_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_725_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_707_);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_707_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v___x_707_);
v_a_726_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_717_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_717_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref_known(v___x_696_, 1);
lean_del_object(v___x_688_);
lean_dec_ref(v_toExpr_685_);
lean_dec(v_stx_677_);
v_a_736_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_700_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_700_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_675_ = stack[0].m_obj;
lean_object* v_f_676_ = stack[1].m_obj;
lean_object* v_stx_677_ = stack[2].m_obj;
lean_object* v_a_678_ = stack[3].m_obj;
lean_object* v_a_679_ = stack[4].m_obj;
lean_object* v_a_680_ = stack[5].m_obj;
lean_object* v_a_681_ = stack[6].m_obj;
lean_object* v_a_682_ = stack[7].m_obj;
lean_object* v_a_683_ = stack[8].m_obj;
lean_object* v_res_745_;
v_res_745_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(v_inst_675_, v_f_676_, v_stx_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
stack->m_obj
 = v_res_745_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg___boxed(lean_object* v_inst_746_, lean_object* v_f_747_, lean_object* v_stx_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(v_inst_746_, v_f_747_, v_stx_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_756_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(lean_object* v_00_u03b1_757_, lean_object* v_inst_758_, lean_object* v_f_759_, lean_object* v_stx_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_toExpr_768_; lean_object* v_toTypeExpr_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_827_; 
v_toExpr_768_ = lean_ctor_get(v_inst_758_, 0);
v_toTypeExpr_769_ = lean_ctor_get(v_inst_758_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_inst_758_);
if (v_isSharedCheck_827_ == 0)
{
v___x_771_ = v_inst_758_;
v_isShared_772_ = v_isSharedCheck_827_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_toTypeExpr_769_);
lean_inc(v_toExpr_768_);
lean_dec(v_inst_758_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_827_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_toCold_773_; lean_object* v_currRecDepth_774_; lean_object* v_ref_775_; uint16_t v_optionFlags_776_; uint8_t v_suppressElabErrors_777_; uint8_t v_isRecordingDeps_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_ref_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_toCold_773_ = lean_ctor_get(v_a_765_, 0);
v_currRecDepth_774_ = lean_ctor_get(v_a_765_, 1);
v_ref_775_ = lean_ctor_get(v_a_765_, 2);
v_optionFlags_776_ = lean_ctor_get_uint16(v_a_765_, sizeof(void*)*3);
v_suppressElabErrors_777_ = lean_ctor_get_uint8(v_a_765_, sizeof(void*)*3 + 2);
v_isRecordingDeps_778_ = lean_ctor_get_uint8(v_a_765_, sizeof(void*)*3 + 3);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v_toTypeExpr_769_);
lean_inc(v_stx_760_);
v___x_780_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_760_);
v_ref_781_ = l_Lean_replaceRef(v_stx_760_, v_ref_775_);
lean_inc(v_currRecDepth_774_);
lean_inc_ref(v_toCold_773_);
v___x_782_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_782_, 0, v_toCold_773_);
lean_ctor_set(v___x_782_, 1, v_currRecDepth_774_);
lean_ctor_set(v___x_782_, 2, v_ref_781_);
lean_ctor_set_uint16(v___x_782_, sizeof(void*)*3, v_optionFlags_776_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 2, v_suppressElabErrors_777_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 3, v_isRecordingDeps_778_);
lean_inc(v_a_766_);
lean_inc(v_a_764_);
lean_inc_ref(v_a_763_);
lean_inc(v_a_762_);
lean_inc_ref(v_a_761_);
v___x_783_ = lean_apply_8(v_f_759_, v___x_780_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v___x_782_, v_a_766_, lean_box(0));
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_818_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_818_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_818_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_818_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
lean_inc(v_a_784_);
v___x_788_ = lean_apply_1(v_toExpr_768_, v_a_784_);
lean_inc_ref(v___x_788_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_788_);
lean_ctor_set(v___x_771_, 0, v_a_784_);
v___x_790_ = v___x_771_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_784_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_817_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v_infoState_792_; uint8_t v_enabled_793_; 
v___x_791_ = lean_st_ref_get(v_a_766_);
v_infoState_792_ = lean_ctor_get(v___x_791_, 8);
lean_inc_ref(v_infoState_792_);
lean_dec(v___x_791_);
v_enabled_793_ = lean_ctor_get_uint8(v_infoState_792_, sizeof(void*)*3);
lean_dec_ref(v_infoState_792_);
if (v_enabled_793_ == 0)
{
lean_object* v___x_795_; 
lean_dec_ref(v___x_788_);
lean_dec_ref_known(v___x_779_, 1);
lean_dec(v_stx_760_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_790_);
v___x_795_ = v___x_786_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_786_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_box(0);
v___x_799_ = 0;
v___x_800_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_760_, v___x_788_, v___x_779_, v___x_797_, v___x_798_, v___x_799_, v___x_799_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_808_);
v___x_802_ = v___x_800_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_dec(v___x_800_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_790_);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_790_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v___x_790_);
v_a_809_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_800_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_800_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref_known(v___x_779_, 1);
lean_del_object(v___x_771_);
lean_dec_ref(v_toExpr_768_);
lean_dec(v_stx_760_);
v_a_819_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_783_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_783_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_758_ = stack[1].m_obj;
lean_object* v_f_759_ = stack[2].m_obj;
lean_object* v_stx_760_ = stack[3].m_obj;
lean_object* v_a_761_ = stack[4].m_obj;
lean_object* v_a_762_ = stack[5].m_obj;
lean_object* v_a_763_ = stack[6].m_obj;
lean_object* v_a_764_ = stack[7].m_obj;
lean_object* v_a_765_ = stack[8].m_obj;
lean_object* v_a_766_ = stack[9].m_obj;
lean_object* v_res_828_;
v_res_828_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(lean_box(0), v_inst_758_, v_f_759_, v_stx_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___boxed(lean_object* v_00_u03b1_829_, lean_object* v_inst_830_, lean_object* v_f_831_, lean_object* v_stx_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(v_00_u03b1_829_, v_inst_830_, v_f_831_, v_stx_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_840_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(lean_object* v_msgData_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v_env_848_; uint8_t v___x_849_; lean_object* v_env_850_; lean_object* v___x_851_; lean_object* v_toCold_852_; lean_object* v_mctx_853_; lean_object* v_lctx_854_; lean_object* v_options_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_847_ = lean_st_ref_get(v___y_845_);
v_env_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc_ref(v_env_848_);
lean_dec(v___x_847_);
v___x_849_ = 0;
v_env_850_ = l_Lean_Environment_setRecordingDeps(v_env_848_, v___x_849_);
v___x_851_ = lean_st_ref_get(v___y_843_);
v_toCold_852_ = lean_ctor_get(v___y_844_, 0);
v_mctx_853_ = lean_ctor_get(v___x_851_, 0);
lean_inc_ref(v_mctx_853_);
lean_dec(v___x_851_);
v_lctx_854_ = lean_ctor_get(v___y_842_, 2);
v_options_855_ = lean_ctor_get(v_toCold_852_, 2);
lean_inc_ref(v_options_855_);
lean_inc_ref(v_lctx_854_);
v___x_856_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_856_, 0, v_env_850_);
lean_ctor_set(v___x_856_, 1, v_mctx_853_);
lean_ctor_set(v___x_856_, 2, v_lctx_854_);
lean_ctor_set(v___x_856_, 3, v_options_855_);
v___x_857_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v_msgData_841_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_841_ = stack[0].m_obj;
lean_object* v___y_842_ = stack[1].m_obj;
lean_object* v___y_843_ = stack[2].m_obj;
lean_object* v___y_844_ = stack[3].m_obj;
lean_object* v___y_845_ = stack[4].m_obj;
lean_object* v_res_859_;
v_res_859_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(lean_object* v_msgData_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_866_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(lean_object* v_msg_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_ref_873_; lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_ref_873_ = lean_ctor_get(v___y_870_, 2);
v___x_874_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
lean_inc(v_ref_873_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_ref_873_);
lean_ctor_set(v___x_879_, 1, v_a_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 1);
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_867_ = stack[0].m_obj;
lean_object* v___y_868_ = stack[1].m_obj;
lean_object* v___y_869_ = stack[2].m_obj;
lean_object* v___y_870_ = stack[3].m_obj;
lean_object* v___y_871_ = stack[4].m_obj;
lean_object* v_res_884_;
v_res_884_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg___boxed(lean_object* v_msg_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(lean_object* v_f_895_, lean_object* v_e_896_, lean_object* v_errMsg_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v___y_905_; lean_object* v___y_906_; uint8_t v___y_907_; lean_object* v___y_923_; lean_object* v_a_924_; lean_object* v___x_927_; 
v___x_903_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_inc_ref(v_f_895_);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc_ref(v_a_898_);
lean_inc_ref(v_e_896_);
v___x_927_ = lean_apply_6(v_f_895_, v_e_896_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, lean_box(0));
if (lean_obj_tag(v___x_927_) == 0)
{
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
lean_dec_ref(v_f_895_);
return v___x_927_;
}
else
{
lean_object* v_a_928_; uint8_t v___y_930_; uint8_t v___x_945_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
v___x_945_ = l_Lean_Exception_isInterrupt(v_a_928_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; 
lean_inc(v_a_928_);
v___x_946_ = l_Lean_Exception_isRuntime(v_a_928_);
v___y_930_ = v___x_946_;
goto v___jp_929_;
}
else
{
v___y_930_ = v___x_945_;
goto v___jp_929_;
}
v___jp_929_:
{
if (v___y_930_ == 0)
{
if (lean_obj_tag(v_a_928_) == 0)
{
lean_dec_ref_known(v_a_928_, 2);
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
lean_dec_ref(v_f_895_);
return v___x_927_;
}
else
{
lean_object* v_id_931_; uint8_t v___x_932_; 
v_id_931_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_id_931_);
lean_dec_ref_known(v_a_928_, 2);
v___x_932_ = l_Lean_instBEqInternalExceptionId_beq(v___x_903_, v_id_931_);
lean_dec(v_id_931_);
if (v___x_932_ == 0)
{
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
lean_dec_ref(v_f_895_);
return v___x_927_;
}
else
{
lean_object* v___x_933_; 
lean_dec_ref_known(v___x_927_, 1);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc_ref(v_a_898_);
lean_inc_ref(v_e_896_);
v___x_933_ = lean_whnf(v_e_896_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc_ref(v_a_898_);
v___x_935_ = lean_apply_6(v_f_895_, v_a_934_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, lean_box(0));
if (lean_obj_tag(v___x_935_) == 0)
{
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
return v___x_935_;
}
else
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
v___y_923_ = v___x_935_;
v_a_924_ = v_a_936_;
goto v___jp_922_;
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_f_895_);
v_a_937_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
lean_inc(v_a_937_);
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
v___y_923_ = v___x_942_;
v_a_924_ = v_a_937_;
goto v___jp_922_;
}
}
}
}
}
}
else
{
lean_dec(v_a_928_);
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
lean_dec_ref(v_f_895_);
return v___x_927_;
}
}
}
v___jp_904_:
{
if (v___y_907_ == 0)
{
if (lean_obj_tag(v___y_906_) == 0)
{
lean_dec_ref_known(v___y_906_, 2);
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
return v___y_905_;
}
else
{
lean_object* v_id_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_920_; 
v_id_908_ = lean_ctor_get(v___y_906_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___y_906_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___y_906_, 1);
lean_dec(v_unused_921_);
v___x_910_ = v___y_906_;
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_id_908_);
lean_dec(v___y_906_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_instBEqInternalExceptionId_beq(v___x_903_, v_id_908_);
lean_dec(v_id_908_);
if (v___x_912_ == 0)
{
lean_del_object(v___x_910_);
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
return v___y_905_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
lean_dec_ref(v___y_905_);
v___x_913_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1);
v___x_914_ = l_Lean_indentExpr(v_e_896_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 7);
lean_ctor_set(v___x_910_, 1, v___x_914_);
lean_ctor_set(v___x_910_, 0, v___x_913_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_914_);
v___x_916_ = v_reuseFailAlloc_919_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_errMsg_897_);
v___x_918_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v___x_917_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_918_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_906_);
lean_dec_ref(v_errMsg_897_);
lean_dec_ref(v_e_896_);
return v___y_905_;
}
}
v___jp_922_:
{
uint8_t v___x_925_; 
v___x_925_ = l_Lean_Exception_isInterrupt(v_a_924_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; 
lean_inc_ref(v_a_924_);
v___x_926_ = l_Lean_Exception_isRuntime(v_a_924_);
v___y_905_ = v___y_923_;
v___y_906_ = v_a_924_;
v___y_907_ = v___x_926_;
goto v___jp_904_;
}
else
{
v___y_905_ = v___y_923_;
v___y_906_ = v_a_924_;
v___y_907_ = v___x_925_;
goto v___jp_904_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_895_ = stack[0].m_obj;
lean_object* v_e_896_ = stack[1].m_obj;
lean_object* v_errMsg_897_ = stack[2].m_obj;
lean_object* v_a_898_ = stack[3].m_obj;
lean_object* v_a_899_ = stack[4].m_obj;
lean_object* v_a_900_ = stack[5].m_obj;
lean_object* v_a_901_ = stack[6].m_obj;
lean_object* v_res_947_;
v_res_947_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_895_, v_e_896_, v_errMsg_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___boxed(lean_object* v_f_948_, lean_object* v_e_949_, lean_object* v_errMsg_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_948_, v_e_949_, v_errMsg_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_956_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(lean_object* v_00_u03b1_957_, lean_object* v_f_958_, lean_object* v_e_959_, lean_object* v_errMsg_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_958_, v_e_959_, v_errMsg_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
return v___x_966_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalExpr_withWHNF_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_958_ = stack[1].m_obj;
lean_object* v_e_959_ = stack[2].m_obj;
lean_object* v_errMsg_960_ = stack[3].m_obj;
lean_object* v_a_961_ = stack[4].m_obj;
lean_object* v_a_962_ = stack[5].m_obj;
lean_object* v_a_963_ = stack[6].m_obj;
lean_object* v_a_964_ = stack[7].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(lean_box(0), v_f_958_, v_e_959_, v_errMsg_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___boxed(lean_object* v_00_u03b1_968_, lean_object* v_f_969_, lean_object* v_e_970_, lean_object* v_errMsg_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(v_00_u03b1_968_, v_f_969_, v_e_970_, v_errMsg_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
return v_res_977_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(lean_object* v_00_u03b1_978_, lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
return v___x_985_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_979_ = stack[1].m_obj;
lean_object* v___y_980_ = stack[2].m_obj;
lean_object* v___y_981_ = stack[3].m_obj;
lean_object* v___y_982_ = stack[4].m_obj;
lean_object* v___y_983_ = stack[5].m_obj;
lean_object* v_res_986_;
v_res_986_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(lean_box(0), v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___boxed(lean_object* v_00_u03b1_987_, lean_object* v_msg_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(v_00_u03b1_987_, v_msg_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_994_;
}
}
uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object* v_item_995_){
_start:
{
lean_object* v_optionComps_996_; uint8_t v___x_997_; 
v_optionComps_996_ = lean_ctor_get(v_item_995_, 5);
v___x_997_ = l_List_isEmpty___redArg(v_optionComps_996_);
return v___x_997_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_995_ = stack[0].m_obj;
uint8_t v_res_998_;
v_res_998_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_995_);
stack->m_num = v_res_998_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(lean_object* v_item_999_){
_start:
{
uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_res_1000_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_999_);
lean_dec_ref(v_item_999_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root(lean_object* v_item_1002_){
_start:
{
lean_object* v_optionComps_1003_; 
v_optionComps_1003_ = lean_ctor_get(v_item_1002_, 5);
if (lean_obj_tag(v_optionComps_1003_) == 1)
{
lean_object* v_head_1004_; 
v_head_1004_ = lean_ctor_get(v_optionComps_1003_, 0);
lean_inc(v_head_1004_);
return v_head_1004_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_box(0);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(lean_object* v_item_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1006_);
lean_dec_ref(v_item_1006_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object* v_item_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1008_);
v___x_1010_ = l_Lean_Syntax_getId(v___x_1009_);
lean_dec(v___x_1009_);
if (lean_obj_tag(v___x_1010_) == 1)
{
lean_object* v_str_1011_; 
v_str_1011_ = lean_ctor_get(v___x_1010_, 1);
lean_inc_ref(v_str_1011_);
lean_dec_ref_known(v___x_1010_, 2);
return v_str_1011_;
}
else
{
lean_object* v___x_1012_; 
lean_dec(v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(lean_object* v_item_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1013_);
lean_dec_ref(v_item_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(lean_object* v_item_1015_){
_start:
{
lean_object* v_prevOptionComps_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_prevOptionComps_1016_ = lean_ctor_get(v_item_1015_, 6);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = l_List_get_x3fInternal___redArg(v_prevOptionComps_1016_, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(lean_object* v_item_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(v_item_1019_);
lean_dec_ref(v_item_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(lean_object* v_item_1021_){
_start:
{
lean_object* v_prevOptionComps_1022_; 
v_prevOptionComps_1022_ = lean_ctor_get(v_item_1021_, 6);
if (lean_obj_tag(v_prevOptionComps_1022_) == 1)
{
lean_object* v_head_1023_; 
v_head_1023_ = lean_ctor_get(v_prevOptionComps_1022_, 0);
lean_inc(v_head_1023_);
return v_head_1023_;
}
else
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_box(0);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(lean_object* v_item_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_1025_);
lean_dec_ref(v_item_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
if (lean_obj_tag(v_x_1028_) == 0)
{
return v_x_1027_;
}
else
{
lean_object* v_head_1029_; lean_object* v_tail_1030_; lean_object* v___x_1031_; 
v_head_1029_ = lean_ctor_get(v_x_1028_, 0);
lean_inc(v_head_1029_);
v_tail_1030_ = lean_ctor_get(v_x_1028_, 1);
lean_inc(v_tail_1030_);
lean_dec_ref_known(v_x_1028_, 2);
v___x_1031_ = l_Lean_Name_appendCore(v_x_1027_, v_head_1029_);
lean_dec(v_x_1027_);
v_x_1027_ = v___x_1031_;
v_x_1028_ = v_tail_1030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
if (lean_obj_tag(v_a_1033_) == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = l_List_reverse___redArg(v_a_1034_);
return v___x_1035_;
}
else
{
lean_object* v_head_1036_; lean_object* v_tail_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1046_; 
v_head_1036_ = lean_ctor_get(v_a_1033_, 0);
v_tail_1037_ = lean_ctor_get(v_a_1033_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1039_ = v_a_1033_;
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_tail_1037_);
lean_inc(v_head_1036_);
lean_dec(v_a_1033_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = l_Lean_Syntax_getId(v_head_1036_);
lean_dec(v_head_1036_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v_a_1034_);
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1034_);
v___x_1043_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
v_a_1033_ = v_tail_1037_;
v_a_1034_ = v___x_1043_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(lean_object* v_item_1047_){
_start:
{
lean_object* v_optionComps_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_optionComps_1048_ = lean_ctor_get(v_item_1047_, 5);
lean_inc(v_optionComps_1048_);
lean_dec_ref(v_item_1047_);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_box(0);
v___x_1051_ = l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(v_optionComps_1048_, v___x_1050_);
v___x_1052_ = l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(v___x_1049_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object* v_item_1053_){
_start:
{
lean_object* v_ref_1054_; lean_object* v_option_1055_; lean_object* v_value_1056_; lean_object* v_bool_x3f_1057_; lean_object* v_origOptionName_1058_; lean_object* v_optionComps_1059_; lean_object* v_prevOptionComps_1060_; lean_object* v___y_1062_; 
v_ref_1054_ = lean_ctor_get(v_item_1053_, 0);
lean_inc(v_ref_1054_);
v_option_1055_ = lean_ctor_get(v_item_1053_, 1);
lean_inc(v_option_1055_);
v_value_1056_ = lean_ctor_get(v_item_1053_, 2);
lean_inc(v_value_1056_);
v_bool_x3f_1057_ = lean_ctor_get(v_item_1053_, 3);
lean_inc(v_bool_x3f_1057_);
v_origOptionName_1058_ = lean_ctor_get(v_item_1053_, 4);
lean_inc(v_origOptionName_1058_);
v_optionComps_1059_ = lean_ctor_get(v_item_1053_, 5);
v_prevOptionComps_1060_ = lean_ctor_get(v_item_1053_, 6);
lean_inc(v_prevOptionComps_1060_);
if (lean_obj_tag(v_optionComps_1059_) == 0)
{
v___y_1062_ = v_optionComps_1059_;
goto v___jp_1061_;
}
else
{
lean_object* v_tail_1079_; 
v_tail_1079_ = lean_ctor_get(v_optionComps_1059_, 1);
lean_inc(v_tail_1079_);
v___y_1062_ = v_tail_1079_;
goto v___jp_1061_;
}
v___jp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v___x_1063_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1053_);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_item_1053_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1072_ = lean_ctor_get(v_item_1053_, 6);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_item_1053_, 5);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_item_1053_, 4);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_item_1053_, 3);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_item_1053_, 2);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_item_1053_, 1);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_item_1053_, 0);
lean_dec(v_unused_1078_);
v___x_1065_ = v_item_1053_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v_item_1053_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1063_);
lean_ctor_set(v___x_1067_, 1, v_prevOptionComps_1060_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 6, v___x_1067_);
lean_ctor_set(v___x_1065_, 5, v___y_1062_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_ref_1054_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_option_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_value_1056_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_bool_x3f_1057_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_origOptionName_1058_);
lean_ctor_set(v_reuseFailAlloc_1070_, 5, v___y_1062_);
lean_ctor_set(v_reuseFailAlloc_1070_, 6, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_box(1);
v___x_1081_ = l_Lean_MessageData_ofFormat(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2));
v___x_1086_ = l_Lean_MessageData_ofFormat(v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
return v_x_1087_;
}
else
{
lean_object* v_head_1089_; lean_object* v_tail_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1112_; 
v_head_1089_ = lean_ctor_get(v_x_1088_, 0);
v_tail_1090_ = lean_ctor_get(v_x_1088_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1088_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1092_ = v_x_1088_;
v_isShared_1093_ = v_isSharedCheck_1112_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_tail_1090_);
lean_inc(v_head_1089_);
lean_dec(v_x_1088_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1112_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_before_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1110_; 
v_before_1094_ = lean_ctor_get(v_head_1089_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_head_1089_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v_head_1089_, 1);
lean_dec(v_unused_1111_);
v___x_1096_ = v_head_1089_;
v_isShared_1097_ = v_isSharedCheck_1110_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_before_1094_);
lean_dec(v_head_1089_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1110_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 7);
lean_ctor_set(v___x_1096_, 1, v___x_1098_);
lean_ctor_set(v___x_1096_, 0, v_x_1087_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_x_1087_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 7);
lean_ctor_set(v___x_1092_, 1, v___x_1101_);
lean_ctor_set(v___x_1092_, 0, v___x_1100_);
v___x_1103_ = v___x_1092_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = l_Lean_MessageData_ofSyntax(v_before_1094_);
v___x_1105_ = l_Lean_indentD(v___x_1104_);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v_x_1087_ = v___x_1106_;
v_x_1088_ = v_tail_1090_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(lean_object* v_opts_1113_, lean_object* v_opt_1114_){
_start:
{
lean_object* v_name_1115_; lean_object* v_defValue_1116_; lean_object* v_map_1117_; lean_object* v___x_1118_; 
v_name_1115_ = lean_ctor_get(v_opt_1114_, 0);
v_defValue_1116_ = lean_ctor_get(v_opt_1114_, 1);
v_map_1117_ = lean_ctor_get(v_opts_1113_, 0);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1117_, v_name_1115_);
if (lean_obj_tag(v___x_1118_) == 0)
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_unbox(v_defValue_1116_);
return v___x_1119_;
}
else
{
lean_object* v_val_1120_; 
v_val_1120_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_val_1120_);
lean_dec_ref_known(v___x_1118_, 1);
if (lean_obj_tag(v_val_1120_) == 1)
{
uint8_t v_v_1121_; 
v_v_1121_ = lean_ctor_get_uint8(v_val_1120_, 0);
lean_dec_ref_known(v_val_1120_, 0);
return v_v_1121_;
}
else
{
uint8_t v___x_1122_; 
lean_dec(v_val_1120_);
v___x_1122_ = lean_unbox(v_defValue_1116_);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1113_ = stack[0].m_obj;
lean_object* v_opt_1114_ = stack[1].m_obj;
uint8_t v_res_1123_;
v_res_1123_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_1113_, v_opt_1114_);
stack->m_num = v_res_1123_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_1124_, lean_object* v_opt_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_1124_, v_opt_1125_);
lean_dec_ref(v_opt_1125_);
lean_dec_ref(v_opts_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_1132_ = l_Lean_MessageData_ofFormat(v___x_1131_);
return v___x_1132_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_1133_, lean_object* v_macroStack_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1135_);
v___x_1138_ = l_Lean_Elab_pp_macroStack;
v___x_1139_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_1137_, v___x_1138_);
lean_dec_ref(v___x_1137_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_dec(v_macroStack_1134_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_msgData_1133_);
return v___x_1140_;
}
else
{
if (lean_obj_tag(v_macroStack_1134_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_msgData_1133_);
return v___x_1141_;
}
else
{
lean_object* v_head_1142_; lean_object* v_after_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1158_; 
v_head_1142_ = lean_ctor_get(v_macroStack_1134_, 0);
lean_inc(v_head_1142_);
v_after_1143_ = lean_ctor_get(v_head_1142_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_head_1142_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_head_1142_, 0);
lean_dec(v_unused_1159_);
v___x_1145_ = v_head_1142_;
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_after_1143_);
lean_dec(v_head_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 7);
lean_ctor_set(v___x_1145_, 1, v___x_1147_);
lean_ctor_set(v___x_1145_, 0, v_msgData_1133_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_msgData_1133_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_msgData_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1150_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_ofSyntax(v_after_1143_);
v___x_1153_ = l_Lean_indentD(v___x_1152_);
v_msgData_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1154_, 0, v___x_1151_);
lean_ctor_set(v_msgData_1154_, 1, v___x_1153_);
v___x_1155_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(v_msgData_1154_, v_macroStack_1134_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1133_ = stack[0].m_obj;
lean_object* v_macroStack_1134_ = stack[1].m_obj;
lean_object* v___y_1135_ = stack[2].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1133_, v_macroStack_1134_, v___y_1135_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_1161_, lean_object* v_macroStack_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1161_, v_macroStack_1162_, v___y_1163_);
lean_dec_ref(v___y_1163_);
return v_res_1165_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_ref_1174_; lean_object* v_macroStack_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
v_ref_1174_ = lean_ctor_get(v___y_1171_, 2);
v_macroStack_1175_ = lean_ctor_get(v___y_1167_, 1);
v___x_1176_ = l_Lean_Elab_getBetterRef(v_ref_1174_, v_macroStack_1175_);
v___x_1177_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_1166_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
lean_inc(v_macroStack_1175_);
v___x_1179_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_1178_, v_macroStack_1175_, v___y_1171_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1176_);
lean_ctor_set(v___x_1184_, 1, v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1166_ = stack[0].m_obj;
lean_object* v___y_1167_ = stack[1].m_obj;
lean_object* v___y_1168_ = stack[2].m_obj;
lean_object* v___y_1169_ = stack[3].m_obj;
lean_object* v___y_1170_ = stack[4].m_obj;
lean_object* v___y_1171_ = stack[5].m_obj;
lean_object* v___y_1172_ = stack[6].m_obj;
lean_object* v_res_1189_;
v_res_1189_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
stack->m_obj
 = v_res_1189_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1198_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(lean_object* v_ref_1199_, lean_object* v_msg_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_toCold_1208_; lean_object* v_currRecDepth_1209_; lean_object* v_ref_1210_; uint16_t v_optionFlags_1211_; uint8_t v_suppressElabErrors_1212_; uint8_t v_isRecordingDeps_1213_; lean_object* v_ref_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_toCold_1208_ = lean_ctor_get(v___y_1205_, 0);
v_currRecDepth_1209_ = lean_ctor_get(v___y_1205_, 1);
v_ref_1210_ = lean_ctor_get(v___y_1205_, 2);
v_optionFlags_1211_ = lean_ctor_get_uint16(v___y_1205_, sizeof(void*)*3);
v_suppressElabErrors_1212_ = lean_ctor_get_uint8(v___y_1205_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1213_ = lean_ctor_get_uint8(v___y_1205_, sizeof(void*)*3 + 3);
v_ref_1214_ = l_Lean_replaceRef(v_ref_1199_, v_ref_1210_);
lean_inc(v_currRecDepth_1209_);
lean_inc_ref(v_toCold_1208_);
v___x_1215_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1215_, 0, v_toCold_1208_);
lean_ctor_set(v___x_1215_, 1, v_currRecDepth_1209_);
lean_ctor_set(v___x_1215_, 2, v_ref_1214_);
lean_ctor_set_uint16(v___x_1215_, sizeof(void*)*3, v_optionFlags_1211_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*3 + 2, v_suppressElabErrors_1212_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*3 + 3, v_isRecordingDeps_1213_);
v___x_1216_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___x_1215_, v___y_1206_);
lean_dec_ref_known(v___x_1215_, 3);
return v___x_1216_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1199_ = stack[0].m_obj;
lean_object* v_msg_1200_ = stack[1].m_obj;
lean_object* v___y_1201_ = stack[2].m_obj;
lean_object* v___y_1202_ = stack[3].m_obj;
lean_object* v___y_1203_ = stack[4].m_obj;
lean_object* v___y_1204_ = stack[5].m_obj;
lean_object* v___y_1205_ = stack[6].m_obj;
lean_object* v___y_1206_ = stack[7].m_obj;
lean_object* v_res_1217_;
v_res_1217_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1199_, v_msg_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(lean_object* v_ref_1218_, lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1218_, v_msg_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v_ref_1218_);
return v_res_1227_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object* v_item_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_bool_x3f_1242_; 
v_bool_x3f_1242_ = lean_ctor_get(v_item_1234_, 3);
if (lean_obj_tag(v_bool_x3f_1242_) == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_item_1234_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
else
{
lean_object* v_option_1245_; lean_object* v_origOptionName_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_option_1245_ = lean_ctor_get(v_item_1234_, 1);
lean_inc(v_option_1245_);
v_origOptionName_1246_ = lean_ctor_get(v_item_1234_, 4);
lean_inc(v_origOptionName_1246_);
lean_dec_ref(v_item_1234_);
v___x_1247_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1);
v___x_1248_ = l_Lean_MessageData_ofName(v_origOptionName_1246_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1245_, v___x_1251_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_option_1245_);
return v___x_1252_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_1234_ = stack[0].m_obj;
lean_object* v_a_1235_ = stack[1].m_obj;
lean_object* v_a_1236_ = stack[2].m_obj;
lean_object* v_a_1237_ = stack[3].m_obj;
lean_object* v_a_1238_ = stack[4].m_obj;
lean_object* v_a_1239_ = stack[5].m_obj;
lean_object* v_a_1240_ = stack[6].m_obj;
lean_object* v_res_1253_;
v_res_1253_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(lean_object* v_item_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
return v_res_1262_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(lean_object* v_00_u03b1_1263_, lean_object* v_ref_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1264_, v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1264_ = stack[1].m_obj;
lean_object* v_msg_1265_ = stack[2].m_obj;
lean_object* v___y_1266_ = stack[3].m_obj;
lean_object* v___y_1267_ = stack[4].m_obj;
lean_object* v___y_1268_ = stack[5].m_obj;
lean_object* v___y_1269_ = stack[6].m_obj;
lean_object* v___y_1270_ = stack[7].m_obj;
lean_object* v___y_1271_ = stack[8].m_obj;
lean_object* v_res_1274_;
v_res_1274_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(lean_box(0), v_ref_1264_, v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_ref_1276_, lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(v_00_u03b1_1275_, v_ref_1276_, v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v_ref_1276_);
return v_res_1285_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(lean_object* v_00_u03b1_1286_, lean_object* v_msg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1287_ = stack[1].m_obj;
lean_object* v___y_1288_ = stack[2].m_obj;
lean_object* v___y_1289_ = stack[3].m_obj;
lean_object* v___y_1290_ = stack[4].m_obj;
lean_object* v___y_1291_ = stack[5].m_obj;
lean_object* v___y_1292_ = stack[6].m_obj;
lean_object* v___y_1293_ = stack[7].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(lean_box(0), v_msg_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_msg_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_1297_, v_msg_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1306_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(lean_object* v_msgData_1307_, lean_object* v_macroStack_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1307_, v_macroStack_1308_, v___y_1313_);
return v___x_1316_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1307_ = stack[0].m_obj;
lean_object* v_macroStack_1308_ = stack[1].m_obj;
lean_object* v___y_1309_ = stack[2].m_obj;
lean_object* v___y_1310_ = stack[3].m_obj;
lean_object* v___y_1311_ = stack[4].m_obj;
lean_object* v___y_1312_ = stack[5].m_obj;
lean_object* v___y_1313_ = stack[6].m_obj;
lean_object* v___y_1314_ = stack[7].m_obj;
lean_object* v_res_1317_;
v_res_1317_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_1307_, v_macroStack_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
stack->m_obj
 = v_res_1317_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1318_, lean_object* v_macroStack_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_1318_, v_macroStack_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1327_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4));
v___x_1336_ = l_Lean_stringToMessageData(v___x_1335_);
return v___x_1336_;
}
}
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object* v_item_1337_, lean_object* v_structName_x3f_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_option_1346_; lean_object* v_origOptionName_1347_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1356_; uint8_t v___x_1365_; 
v_option_1346_ = lean_ctor_get(v_item_1337_, 1);
lean_inc(v_option_1346_);
v_origOptionName_1347_ = lean_ctor_get(v_item_1337_, 4);
lean_inc(v_origOptionName_1347_);
lean_dec_ref(v_item_1337_);
v___x_1365_ = l_Lean_Name_isAnonymous(v_origOptionName_1347_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1366_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1367_ = l_Lean_MessageData_ofName(v_origOptionName_1347_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___y_1356_ = v___x_1370_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1371_; 
lean_dec(v_origOptionName_1347_);
v___x_1371_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1356_ = v___x_1371_;
goto v___jp_1355_;
}
v___jp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___y_1349_);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___y_1350_);
v___x_1354_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1346_, v___x_1353_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_option_1346_);
return v___x_1354_;
}
v___jp_1355_:
{
if (lean_obj_tag(v_structName_x3f_1338_) == 1)
{
lean_object* v_val_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_val_1357_ = lean_ctor_get(v_structName_x3f_1338_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v_structName_x3f_1338_, 1);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1359_ = 0;
v___x_1360_ = l_Lean_MessageData_ofConstName(v_val_1357_, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1358_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___y_1349_ = v___y_1356_;
v___y_1350_ = v___x_1363_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_structName_x3f_1338_);
v___x_1364_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1349_ = v___y_1356_;
v___y_1350_ = v___x_1364_;
goto v___jp_1348_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_1337_ = stack[0].m_obj;
lean_object* v_structName_x3f_1338_ = stack[1].m_obj;
lean_object* v_a_1339_ = stack[2].m_obj;
lean_object* v_a_1340_ = stack[3].m_obj;
lean_object* v_a_1341_ = stack[4].m_obj;
lean_object* v_a_1342_ = stack[5].m_obj;
lean_object* v_a_1343_ = stack[6].m_obj;
lean_object* v_a_1344_ = stack[7].m_obj;
lean_object* v_res_1372_;
v_res_1372_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1337_, v_structName_x3f_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
stack->m_obj
 = v_res_1372_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___boxed(lean_object* v_item_1373_, lean_object* v_structName_x3f_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1373_, v_structName_x3f_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
return v_res_1382_;
}
}
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(lean_object* v_00_u03b1_1383_, lean_object* v_item_1384_, lean_object* v_structName_x3f_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1384_, v_structName_x3f_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_1384_ = stack[1].m_obj;
lean_object* v_structName_x3f_1385_ = stack[2].m_obj;
lean_object* v_a_1386_ = stack[3].m_obj;
lean_object* v_a_1387_ = stack[4].m_obj;
lean_object* v_a_1388_ = stack[5].m_obj;
lean_object* v_a_1389_ = stack[6].m_obj;
lean_object* v_a_1390_ = stack[7].m_obj;
lean_object* v_a_1391_ = stack[8].m_obj;
lean_object* v_res_1394_;
v_res_1394_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(lean_box(0), v_item_1384_, v_structName_x3f_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
stack->m_obj
 = v_res_1394_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___boxed(lean_object* v_00_u03b1_1395_, lean_object* v_item_1396_, lean_object* v_structName_x3f_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(v_00_u03b1_1395_, v_item_1396_, v_structName_x3f_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1405_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0));
v___x_1408_ = l_Lean_stringToMessageData(v___x_1407_);
return v___x_1408_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2));
v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
return v___x_1411_;
}
}
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(lean_object* v_item_1412_, lean_object* v_structName_x3f_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_option_1421_; lean_object* v_origOptionName_1422_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1433_; uint8_t v___x_1442_; 
v_option_1421_ = lean_ctor_get(v_item_1412_, 1);
lean_inc(v_option_1421_);
v_origOptionName_1422_ = lean_ctor_get(v_item_1412_, 4);
lean_inc(v_origOptionName_1422_);
lean_dec_ref(v_item_1412_);
v___x_1442_ = l_Lean_Name_isAnonymous(v_origOptionName_1422_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1443_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1444_ = l_Lean_MessageData_ofName(v_origOptionName_1422_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___y_1433_ = v___x_1447_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1448_; 
lean_dec(v_origOptionName_1422_);
v___x_1448_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1433_ = v___x_1448_;
goto v___jp_1432_;
}
v___jp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1426_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v___y_1424_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v___y_1425_);
v___x_1429_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1421_, v___x_1430_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_option_1421_);
return v___x_1431_;
}
v___jp_1432_:
{
if (lean_obj_tag(v_structName_x3f_1413_) == 1)
{
lean_object* v_val_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_val_1434_ = lean_ctor_get(v_structName_x3f_1413_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v_structName_x3f_1413_, 1);
v___x_1435_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1436_ = 0;
v___x_1437_ = l_Lean_MessageData_ofConstName(v_val_1434_, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1435_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___y_1424_ = v___y_1433_;
v___y_1425_ = v___x_1440_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1441_; 
lean_dec(v_structName_x3f_1413_);
v___x_1441_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1424_ = v___y_1433_;
v___y_1425_ = v___x_1441_;
goto v___jp_1423_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_1412_ = stack[0].m_obj;
lean_object* v_structName_x3f_1413_ = stack[1].m_obj;
lean_object* v_a_1414_ = stack[2].m_obj;
lean_object* v_a_1415_ = stack[3].m_obj;
lean_object* v_a_1416_ = stack[4].m_obj;
lean_object* v_a_1417_ = stack[5].m_obj;
lean_object* v_a_1418_ = stack[6].m_obj;
lean_object* v_a_1419_ = stack[7].m_obj;
lean_object* v_res_1449_;
v_res_1449_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1412_, v_structName_x3f_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___boxed(lean_object* v_item_1450_, lean_object* v_structName_x3f_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1450_, v_structName_x3f_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
return v_res_1459_;
}
}
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(lean_object* v_00_u03b1_1460_, lean_object* v_item_1461_, lean_object* v_structName_x3f_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1461_, v_structName_x3f_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_1461_ = stack[1].m_obj;
lean_object* v_structName_x3f_1462_ = stack[2].m_obj;
lean_object* v_a_1463_ = stack[3].m_obj;
lean_object* v_a_1464_ = stack[4].m_obj;
lean_object* v_a_1465_ = stack[5].m_obj;
lean_object* v_a_1466_ = stack[6].m_obj;
lean_object* v_a_1467_ = stack[7].m_obj;
lean_object* v_a_1468_ = stack[8].m_obj;
lean_object* v_res_1471_;
v_res_1471_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(lean_box(0), v_item_1461_, v_structName_x3f_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
stack->m_obj
 = v_res_1471_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___boxed(lean_object* v_00_u03b1_1472_, lean_object* v_item_1473_, lean_object* v_structName_x3f_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(v_00_u03b1_1472_, v_item_1473_, v_structName_x3f_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1482_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_ctor_set(v___x_1489_, 2, v___x_1488_);
lean_ctor_set(v___x_1489_, 3, v___x_1488_);
lean_ctor_set(v___x_1489_, 4, v___x_1487_);
lean_ctor_set(v___x_1489_, 5, v___x_1487_);
lean_ctor_set(v___x_1489_, 6, v___x_1487_);
lean_ctor_set(v___x_1489_, 7, v___x_1487_);
lean_ctor_set(v___x_1489_, 8, v___x_1487_);
lean_ctor_set(v___x_1489_, 9, v___x_1487_);
lean_ctor_set(v___x_1489_, 10, v___x_1487_);
lean_ctor_set(v___x_1489_, 11, v___x_1486_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_unsigned_to_nat(32u);
v___x_1491_ = lean_mk_empty_array_with_capacity(v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1493_ = ((size_t)5ULL);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_unsigned_to_nat(32u);
v___x_1496_ = lean_mk_empty_array_with_capacity(v___x_1495_);
v___x_1497_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1498_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
lean_ctor_set(v___x_1498_, 2, v___x_1494_);
lean_ctor_set(v___x_1498_, 3, v___x_1494_);
lean_ctor_set_usize(v___x_1498_, 4, v___x_1493_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1499_ = lean_box(1);
v___x_1500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___x_1500_);
lean_ctor_set(v___x_1502_, 2, v___x_1499_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1511_ = l_Lean_stringToMessageData(v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__26));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1536_, lean_object* v_declHint_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_env_1542_; uint8_t v___x_1543_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_st_ref_get(v___y_1538_);
v_env_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_ref(v_env_1542_);
lean_dec(v___x_1541_);
v___x_1543_ = l_Lean_Name_isAnonymous(v_declHint_1537_);
if (v___x_1543_ == 0)
{
uint8_t v_isExporting_1544_; 
v_isExporting_1544_ = lean_ctor_get_uint8(v_env_1542_, sizeof(void*)*13);
if (v_isExporting_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref(v_env_1542_);
lean_dec(v_declHint_1537_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_msg_1536_);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
lean_inc_ref(v_env_1542_);
v___x_1546_ = l_Lean_Environment_setExporting(v_env_1542_, v___x_1543_);
lean_inc(v_declHint_1537_);
lean_inc_ref(v___x_1546_);
v___x_1547_ = l_Lean_Environment_contains(v___x_1546_, v_declHint_1537_, v_isExporting_1544_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v_env_1542_);
lean_dec(v_declHint_1537_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_msg_1536_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_c_1554_; lean_object* v___x_1555_; 
v___x_1549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1551_ = l_Lean_Options_empty;
v___x_1552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1546_);
lean_ctor_set(v___x_1552_, 1, v___x_1549_);
lean_ctor_set(v___x_1552_, 2, v___x_1550_);
lean_ctor_set(v___x_1552_, 3, v___x_1551_);
lean_inc(v_declHint_1537_);
v___x_1553_ = l_Lean_MessageData_ofConstName(v_declHint_1537_, v___x_1543_);
v_c_1554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1554_, 0, v___x_1552_);
lean_ctor_set(v_c_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1542_, v_declHint_1537_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v_env_1542_);
lean_dec(v_declHint_1537_);
v___x_1556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v_c_1554_);
v___x_1558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_MessageData_note(v___x_1559_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_msg_1536_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
else
{
lean_object* v_val_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1619_; 
v_val_1563_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1565_ = v___x_1555_;
v_isShared_1566_ = v_isSharedCheck_1619_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_val_1563_);
lean_dec(v___x_1555_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1619_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v_modules_1568_; lean_object* v_moduleNames_1569_; lean_object* v_mod_1570_; uint8_t v___y_1572_; uint8_t v___x_1602_; 
v___x_1567_ = l_Lean_Environment_header(v_env_1542_);
lean_dec_ref(v_env_1542_);
v_modules_1568_ = lean_ctor_get(v___x_1567_, 3);
lean_inc_ref(v_modules_1568_);
v_moduleNames_1569_ = lean_ctor_get(v___x_1567_, 4);
lean_inc_ref(v_moduleNames_1569_);
lean_dec_ref(v___x_1567_);
v_mod_1570_ = lean_array_get(v___x_1540_, v_moduleNames_1569_, v_val_1563_);
lean_dec_ref(v_moduleNames_1569_);
v___x_1602_ = l_Lean_isPrivateName(v_declHint_1537_);
lean_dec(v_declHint_1537_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_array_get_size(v_modules_1568_);
v___x_1604_ = lean_nat_dec_lt(v_val_1563_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_dec_ref(v_modules_1568_);
lean_dec(v_val_1563_);
v___y_1572_ = v___x_1602_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1605_; lean_object* v_toImport_1606_; uint8_t v_isExported_1607_; 
v___x_1605_ = lean_array_fget(v_modules_1568_, v_val_1563_);
lean_dec(v_val_1563_);
lean_dec_ref(v_modules_1568_);
v_toImport_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc_ref(v_toImport_1606_);
lean_dec(v___x_1605_);
v_isExported_1607_ = lean_ctor_get_uint8(v_toImport_1606_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1606_);
v___y_1572_ = v_isExported_1607_;
goto v___jp_1571_;
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec_ref(v_modules_1568_);
lean_del_object(v___x_1565_);
lean_dec(v_val_1563_);
v___x_1608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v_c_1554_);
v___x_1610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_MessageData_ofName(v_mod_1570_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_MessageData_note(v___x_1615_);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_msg_1536_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
v___jp_1571_:
{
if (v___y_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1573_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_c_1554_);
v___x_1575_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_MessageData_ofName(v_mod_1570_);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_MessageData_note(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_msg_1536_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1582_);
v___x_1584_ = v___x_1565_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1586_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_c_1554_);
v___x_1588_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_MessageData_ofName(v_mod_1570_);
lean_inc_ref(v___x_1590_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1590_);
v___x_1595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_Lean_MessageData_note(v___x_1596_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_msg_1536_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1598_);
v___x_1600_ = v___x_1565_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1620_; 
lean_dec_ref(v_env_1542_);
lean_dec(v_declHint_1537_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_msg_1536_);
return v___x_1620_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1536_ = stack[0].m_obj;
lean_object* v_declHint_1537_ = stack[1].m_obj;
lean_object* v___y_1538_ = stack[2].m_obj;
lean_object* v_res_1621_;
v_res_1621_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1536_, v_declHint_1537_, v___y_1538_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1622_, lean_object* v_declHint_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1622_, v_declHint_1623_, v___y_1624_);
lean_dec(v___y_1624_);
return v_res_1626_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_1627_, lean_object* v_declHint_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1646_; 
v___x_1636_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1627_, v_declHint_1628_, v___y_1634_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1641_ = l_Lean_unknownIdentifierMessageTag;
v___x_1642_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1637_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1627_ = stack[0].m_obj;
lean_object* v_declHint_1628_ = stack[1].m_obj;
lean_object* v___y_1629_ = stack[2].m_obj;
lean_object* v___y_1630_ = stack[3].m_obj;
lean_object* v___y_1631_ = stack[4].m_obj;
lean_object* v___y_1632_ = stack[5].m_obj;
lean_object* v___y_1633_ = stack[6].m_obj;
lean_object* v___y_1634_ = stack[7].m_obj;
lean_object* v_res_1647_;
v_res_1647_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1627_, v_declHint_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
stack->m_obj
 = v_res_1647_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_1648_, lean_object* v_declHint_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1648_, v_declHint_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
return v_res_1657_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1658_, lean_object* v_msg_1659_, lean_object* v_declHint_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v_a_1669_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1659_, v_declHint_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1658_, v_a_1669_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1670_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1658_ = stack[0].m_obj;
lean_object* v_msg_1659_ = stack[1].m_obj;
lean_object* v_declHint_1660_ = stack[2].m_obj;
lean_object* v___y_1661_ = stack[3].m_obj;
lean_object* v___y_1662_ = stack[4].m_obj;
lean_object* v___y_1663_ = stack[5].m_obj;
lean_object* v___y_1664_ = stack[6].m_obj;
lean_object* v___y_1665_ = stack[7].m_obj;
lean_object* v___y_1666_ = stack[8].m_obj;
lean_object* v_res_1671_;
v_res_1671_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1658_, v_msg_1659_, v_declHint_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
stack->m_obj
 = v_res_1671_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1672_, lean_object* v_msg_1673_, lean_object* v_declHint_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1672_, v_msg_1673_, v_declHint_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v_ref_1672_);
return v_res_1682_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_1686_, lean_object* v_constName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1695_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1696_ = 0;
lean_inc(v_constName_1687_);
v___x_1697_ = l_Lean_MessageData_ofConstName(v_constName_1687_, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1686_, v___x_1700_, v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1701_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1686_ = stack[0].m_obj;
lean_object* v_constName_1687_ = stack[1].m_obj;
lean_object* v___y_1688_ = stack[2].m_obj;
lean_object* v___y_1689_ = stack[3].m_obj;
lean_object* v___y_1690_ = stack[4].m_obj;
lean_object* v___y_1691_ = stack[5].m_obj;
lean_object* v___y_1692_ = stack[6].m_obj;
lean_object* v___y_1693_ = stack[7].m_obj;
lean_object* v_res_1702_;
v_res_1702_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1686_, v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
stack->m_obj
 = v_res_1702_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1703_, lean_object* v_constName_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1703_, v_constName_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_ref_1703_);
return v_res_1712_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_ref_1721_; lean_object* v___x_1722_; 
v_ref_1721_ = lean_ctor_get(v___y_1718_, 2);
v___x_1722_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1721_, v_constName_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1722_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1713_ = stack[0].m_obj;
lean_object* v___y_1714_ = stack[1].m_obj;
lean_object* v___y_1715_ = stack[2].m_obj;
lean_object* v___y_1716_ = stack[3].m_obj;
lean_object* v___y_1717_ = stack[4].m_obj;
lean_object* v___y_1718_ = stack[5].m_obj;
lean_object* v___y_1719_ = stack[6].m_obj;
lean_object* v_res_1723_;
v_res_1723_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
stack->m_obj
 = v_res_1723_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1732_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object* v_constName_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; lean_object* v_env_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = lean_st_ref_get(v___y_1739_);
v_env_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc_ref(v_env_1742_);
lean_dec(v___x_1741_);
v___x_1743_ = 0;
lean_inc(v_constName_1733_);
v___x_1744_ = l_Lean_Environment_findConstVal_x3f(v_env_1742_, v_constName_1733_, v___x_1743_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1745_;
}
else
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_constName_1733_);
v_val_1746_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1744_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v___x_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 0);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_val_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1733_ = stack[0].m_obj;
lean_object* v___y_1734_ = stack[1].m_obj;
lean_object* v___y_1735_ = stack[2].m_obj;
lean_object* v___y_1736_ = stack[3].m_obj;
lean_object* v___y_1737_ = stack[4].m_obj;
lean_object* v___y_1738_ = stack[5].m_obj;
lean_object* v___y_1739_ = stack[6].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
if (lean_obj_tag(v_a_1764_) == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = l_List_reverse___redArg(v_a_1765_);
return v___x_1766_;
}
else
{
lean_object* v_head_1767_; lean_object* v_tail_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1777_; 
v_head_1767_ = lean_ctor_get(v_a_1764_, 0);
v_tail_1768_ = lean_ctor_get(v_a_1764_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_a_1764_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1770_ = v_a_1764_;
v_isShared_1771_ = v_isSharedCheck_1777_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_tail_1768_);
lean_inc(v_head_1767_);
lean_dec(v_a_1764_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1777_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = l_Lean_mkLevelParam(v_head_1767_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 1, v_a_1765_);
lean_ctor_set(v___x_1770_, 0, v___x_1772_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_a_1765_);
v___x_1774_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
v_a_1764_ = v_tail_1768_;
v_a_1765_ = v___x_1774_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object* v_constName_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
lean_inc(v_constName_1778_);
v___x_1786_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1798_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_levelParams_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v_levelParams_1791_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_levelParams_1791_);
lean_dec(v_a_1787_);
v___x_1792_ = lean_box(0);
v___x_1793_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_1791_, v___x_1792_);
v___x_1794_ = l_Lean_mkConst(v_constName_1778_, v___x_1793_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1794_);
v___x_1796_ = v___x_1789_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_constName_1778_);
v_a_1799_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1786_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1786_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1778_ = stack[0].m_obj;
lean_object* v___y_1779_ = stack[1].m_obj;
lean_object* v___y_1780_ = stack[2].m_obj;
lean_object* v___y_1781_ = stack[3].m_obj;
lean_object* v___y_1782_ = stack[4].m_obj;
lean_object* v___y_1783_ = stack[5].m_obj;
lean_object* v___y_1784_ = stack[6].m_obj;
lean_object* v_res_1807_;
v_res_1807_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
stack->m_obj
 = v_res_1807_;
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object* v_constName_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v_res_1816_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v_infoState_1821_; uint8_t v_enabled_1822_; 
v___x_1820_ = lean_st_ref_get(v___y_1818_);
v_infoState_1821_ = lean_ctor_get(v___x_1820_, 8);
lean_inc_ref(v_infoState_1821_);
lean_dec(v___x_1820_);
v_enabled_1822_ = lean_ctor_get_uint8(v_infoState_1821_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1821_);
if (v_enabled_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v_t_1817_);
v___x_1823_ = lean_box(0);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v_infoState_1826_; lean_object* v_env_1827_; lean_object* v_nextMacroScope_1828_; lean_object* v_ngen_1829_; lean_object* v_auxDeclNGen_1830_; lean_object* v_traceState_1831_; lean_object* v_cache_1832_; lean_object* v_recordedDeps_1833_; lean_object* v_messages_1834_; lean_object* v_snapshotTasks_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1857_; 
v___x_1825_ = lean_st_ref_take(v___y_1818_);
v_infoState_1826_ = lean_ctor_get(v___x_1825_, 8);
v_env_1827_ = lean_ctor_get(v___x_1825_, 0);
v_nextMacroScope_1828_ = lean_ctor_get(v___x_1825_, 1);
v_ngen_1829_ = lean_ctor_get(v___x_1825_, 2);
v_auxDeclNGen_1830_ = lean_ctor_get(v___x_1825_, 3);
v_traceState_1831_ = lean_ctor_get(v___x_1825_, 4);
v_cache_1832_ = lean_ctor_get(v___x_1825_, 5);
v_recordedDeps_1833_ = lean_ctor_get(v___x_1825_, 6);
v_messages_1834_ = lean_ctor_get(v___x_1825_, 7);
v_snapshotTasks_1835_ = lean_ctor_get(v___x_1825_, 9);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1837_ = v___x_1825_;
v_isShared_1838_ = v_isSharedCheck_1857_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_snapshotTasks_1835_);
lean_inc(v_infoState_1826_);
lean_inc(v_messages_1834_);
lean_inc(v_recordedDeps_1833_);
lean_inc(v_cache_1832_);
lean_inc(v_traceState_1831_);
lean_inc(v_auxDeclNGen_1830_);
lean_inc(v_ngen_1829_);
lean_inc(v_nextMacroScope_1828_);
lean_inc(v_env_1827_);
lean_dec(v___x_1825_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1857_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v_enabled_1839_; lean_object* v_assignment_1840_; lean_object* v_lazyAssignment_1841_; lean_object* v_trees_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1856_; 
v_enabled_1839_ = lean_ctor_get_uint8(v_infoState_1826_, sizeof(void*)*3);
v_assignment_1840_ = lean_ctor_get(v_infoState_1826_, 0);
v_lazyAssignment_1841_ = lean_ctor_get(v_infoState_1826_, 1);
v_trees_1842_ = lean_ctor_get(v_infoState_1826_, 2);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_infoState_1826_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1844_ = v_infoState_1826_;
v_isShared_1845_ = v_isSharedCheck_1856_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_trees_1842_);
lean_inc(v_lazyAssignment_1841_);
lean_inc(v_assignment_1840_);
lean_dec(v_infoState_1826_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1856_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Lean_PersistentArray_push___redArg(v_trees_1842_, v_t_1817_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 2, v___x_1847_);
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_assignment_1840_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_lazyAssignment_1841_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v___x_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*3, v_enabled_1839_);
v___x_1849_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 8, v___x_1849_);
v___x_1851_ = v___x_1837_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_env_1827_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_nextMacroScope_1828_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_ngen_1829_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_auxDeclNGen_1830_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v_traceState_1831_);
lean_ctor_set(v_reuseFailAlloc_1854_, 5, v_cache_1832_);
lean_ctor_set(v_reuseFailAlloc_1854_, 6, v_recordedDeps_1833_);
lean_ctor_set(v_reuseFailAlloc_1854_, 7, v_messages_1834_);
lean_ctor_set(v_reuseFailAlloc_1854_, 8, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1854_, 9, v_snapshotTasks_1835_);
v___x_1851_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_st_ref_put(v___y_1818_, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1846_);
return v___x_1853_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1817_ = stack[0].m_obj;
lean_object* v___y_1818_ = stack[1].m_obj;
lean_object* v_res_1858_;
v_res_1858_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1817_, v___y_1818_);
stack->m_obj
 = v_res_1858_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1859_, v___y_1860_);
lean_dec(v___y_1860_);
return v_res_1862_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_unsigned_to_nat(32u);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1866_ = ((size_t)5ULL);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_unsigned_to_nat(32u);
v___x_1869_ = lean_mk_empty_array_with_capacity(v___x_1868_);
v___x_1870_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
v___x_1871_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___x_1869_);
lean_ctor_set(v___x_1871_, 2, v___x_1867_);
lean_ctor_set(v___x_1871_, 3, v___x_1867_);
lean_ctor_set_usize(v___x_1871_, 4, v___x_1866_);
return v___x_1871_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object* v_t_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v_infoState_1881_; uint8_t v_enabled_1882_; 
v___x_1880_ = lean_st_ref_get(v___y_1878_);
v_infoState_1881_ = lean_ctor_get(v___x_1880_, 8);
lean_inc_ref(v_infoState_1881_);
lean_dec(v___x_1880_);
v_enabled_1882_ = lean_ctor_get_uint8(v_infoState_1881_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1881_);
if (v_enabled_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v_t_1872_);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
v___x_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1886_, 0, v_t_1872_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_1886_, v___y_1878_);
return v___x_1887_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1872_ = stack[0].m_obj;
lean_object* v___y_1873_ = stack[1].m_obj;
lean_object* v___y_1874_ = stack[2].m_obj;
lean_object* v___y_1875_ = stack[3].m_obj;
lean_object* v___y_1876_ = stack[4].m_obj;
lean_object* v___y_1877_ = stack[5].m_obj;
lean_object* v___y_1878_ = stack[6].m_obj;
lean_object* v_res_1888_;
v_res_1888_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
stack->m_obj
 = v_res_1888_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object* v_t_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1897_;
}
}
lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object* v_stx_1898_, lean_object* v_n_1899_, lean_object* v_expectedType_x3f_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_1899_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v_stx_1898_);
v___x_1912_ = l_Lean_LocalContext_empty;
v___x_1913_ = 0;
v___x_1914_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1914_, 0, v___x_1911_);
lean_ctor_set(v___x_1914_, 1, v___x_1912_);
lean_ctor_set(v___x_1914_, 2, v_expectedType_x3f_1900_);
lean_ctor_set(v___x_1914_, 3, v_a_1909_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*4, v___x_1913_);
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*4 + 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
v___x_1916_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1915_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
return v___x_1916_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_expectedType_x3f_1900_);
lean_dec(v_stx_1898_);
v_a_1917_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1908_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1908_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1898_ = stack[0].m_obj;
lean_object* v_n_1899_ = stack[1].m_obj;
lean_object* v_expectedType_x3f_1900_ = stack[2].m_obj;
lean_object* v___y_1901_ = stack[3].m_obj;
lean_object* v___y_1902_ = stack[4].m_obj;
lean_object* v___y_1903_ = stack[5].m_obj;
lean_object* v___y_1904_ = stack[6].m_obj;
lean_object* v___y_1905_ = stack[7].m_obj;
lean_object* v___y_1906_ = stack[8].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1898_, v_n_1899_, v_expectedType_x3f_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object* v_stx_1926_, lean_object* v_n_1927_, lean_object* v_expectedType_x3f_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1926_, v_n_1927_, v_expectedType_x3f_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1936_;
}
}
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object* v_item_1937_, lean_object* v_projFn_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v_infoState_1947_; uint8_t v_enabled_1948_; 
v___x_1946_ = lean_st_ref_get(v_a_1944_);
v_infoState_1947_ = lean_ctor_get(v___x_1946_, 8);
lean_inc_ref(v_infoState_1947_);
lean_dec(v___x_1946_);
v_enabled_1948_ = lean_ctor_get_uint8(v_infoState_1947_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1947_);
if (v_enabled_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_dec(v_projFn_1938_);
v___x_1949_ = lean_box(0);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; lean_object* v_env_1952_; uint8_t v___x_1953_; 
v___x_1951_ = lean_st_ref_get(v_a_1944_);
v_env_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc_ref(v_env_1952_);
lean_dec(v___x_1951_);
lean_inc(v_projFn_1938_);
v___x_1953_ = l_Lean_Environment_contains(v_env_1952_, v_projFn_1938_, v_enabled_1948_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v_projFn_1938_);
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1937_);
v___x_1957_ = lean_box(0);
v___x_1958_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_1956_, v_projFn_1938_, v___x_1957_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_1937_ = stack[0].m_obj;
lean_object* v_projFn_1938_ = stack[1].m_obj;
lean_object* v_a_1939_ = stack[2].m_obj;
lean_object* v_a_1940_ = stack[3].m_obj;
lean_object* v_a_1941_ = stack[4].m_obj;
lean_object* v_a_1942_ = stack[5].m_obj;
lean_object* v_a_1943_ = stack[6].m_obj;
lean_object* v_a_1944_ = stack[7].m_obj;
lean_object* v_res_1959_;
v_res_1959_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1937_, v_projFn_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
stack->m_obj
 = v_res_1959_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object* v_item_1960_, lean_object* v_projFn_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1960_, v_projFn_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec_ref(v_item_1960_);
return v_res_1969_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object* v_t_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1970_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1970_ = stack[0].m_obj;
lean_object* v___y_1971_ = stack[1].m_obj;
lean_object* v___y_1972_ = stack[2].m_obj;
lean_object* v___y_1973_ = stack[3].m_obj;
lean_object* v___y_1974_ = stack[4].m_obj;
lean_object* v___y_1975_ = stack[5].m_obj;
lean_object* v___y_1976_ = stack[6].m_obj;
lean_object* v_res_1979_;
v_res_1979_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
stack->m_obj
 = v_res_1979_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1988_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1989_, lean_object* v_constName_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1990_ = stack[1].m_obj;
lean_object* v___y_1991_ = stack[2].m_obj;
lean_object* v___y_1992_ = stack[3].m_obj;
lean_object* v___y_1993_ = stack[4].m_obj;
lean_object* v___y_1994_ = stack[5].m_obj;
lean_object* v___y_1995_ = stack[6].m_obj;
lean_object* v___y_1996_ = stack[7].m_obj;
lean_object* v_res_1999_;
v_res_1999_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_constName_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
stack->m_obj
 = v_res_1999_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_constName_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2000_, v_constName_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2009_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2010_, lean_object* v_ref_2011_, lean_object* v_constName_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2011_, v_constName_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2011_ = stack[1].m_obj;
lean_object* v_constName_2012_ = stack[2].m_obj;
lean_object* v___y_2013_ = stack[3].m_obj;
lean_object* v___y_2014_ = stack[4].m_obj;
lean_object* v___y_2015_ = stack[5].m_obj;
lean_object* v___y_2016_ = stack[6].m_obj;
lean_object* v___y_2017_ = stack[7].m_obj;
lean_object* v___y_2018_ = stack[8].m_obj;
lean_object* v_res_2021_;
v_res_2021_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_box(0), v_ref_2011_, v_constName_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
stack->m_obj
 = v_res_2021_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_ref_2023_, lean_object* v_constName_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2022_, v_ref_2023_, v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v_ref_2023_);
return v_res_2032_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2033_, lean_object* v_ref_2034_, lean_object* v_msg_2035_, lean_object* v_declHint_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2034_, v_msg_2035_, v_declHint_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2034_ = stack[1].m_obj;
lean_object* v_msg_2035_ = stack[2].m_obj;
lean_object* v_declHint_2036_ = stack[3].m_obj;
lean_object* v___y_2037_ = stack[4].m_obj;
lean_object* v___y_2038_ = stack[5].m_obj;
lean_object* v___y_2039_ = stack[6].m_obj;
lean_object* v___y_2040_ = stack[7].m_obj;
lean_object* v___y_2041_ = stack[8].m_obj;
lean_object* v___y_2042_ = stack[9].m_obj;
lean_object* v_res_2045_;
v_res_2045_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_box(0), v_ref_2034_, v_msg_2035_, v_declHint_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2046_, lean_object* v_ref_2047_, lean_object* v_msg_2048_, lean_object* v_declHint_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2046_, v_ref_2047_, v_msg_2048_, v_declHint_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v_ref_2047_);
return v_res_2057_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2058_, lean_object* v_declHint_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2058_, v_declHint_2059_, v___y_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2058_ = stack[0].m_obj;
lean_object* v_declHint_2059_ = stack[1].m_obj;
lean_object* v___y_2060_ = stack[2].m_obj;
lean_object* v___y_2061_ = stack[3].m_obj;
lean_object* v___y_2062_ = stack[4].m_obj;
lean_object* v___y_2063_ = stack[5].m_obj;
lean_object* v___y_2064_ = stack[6].m_obj;
lean_object* v___y_2065_ = stack[7].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2058_, v_declHint_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2069_, lean_object* v_declHint_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2069_, v_declHint_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2078_;
}
}
lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object* v_info_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_info_2079_);
v___x_2088_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_2087_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2088_;
}
}
LEAN_EXPORT void l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2079_ = stack[0].m_obj;
lean_object* v___y_2080_ = stack[1].m_obj;
lean_object* v___y_2081_ = stack[2].m_obj;
lean_object* v___y_2082_ = stack[3].m_obj;
lean_object* v___y_2083_ = stack[4].m_obj;
lean_object* v___y_2084_ = stack[5].m_obj;
lean_object* v___y_2085_ = stack[6].m_obj;
lean_object* v_res_2089_;
v_res_2089_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2089_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(lean_object* v_info_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2098_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2101_ = lean_box(1);
v___x_2102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2103_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_2104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v___x_2102_);
lean_ctor_set(v___x_2104_, 2, v___x_2101_);
return v___x_2104_;
}
}
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object* v_item_2105_, lean_object* v_structName_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v_infoState_2115_; uint8_t v_enabled_2116_; 
v___x_2114_ = lean_st_ref_get(v_a_2112_);
v_infoState_2115_ = lean_ctor_get(v___x_2114_, 8);
lean_inc_ref(v_infoState_2115_);
lean_dec(v___x_2114_);
v_enabled_2116_ = lean_ctor_get_uint8(v_infoState_2115_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2115_);
if (v_enabled_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v_structName_2106_);
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; lean_object* v_env_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_st_ref_get(v_a_2112_);
v_env_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc_ref(v_env_2120_);
lean_dec(v___x_2119_);
lean_inc(v_structName_2106_);
v___x_2121_ = l_Lean_Environment_contains(v_env_2120_, v_structName_2106_, v_enabled_2116_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec(v_structName_2106_);
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2124_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_2105_);
v___x_2125_ = l_Lean_Syntax_getId(v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___x_2127_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2128_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2124_);
lean_ctor_set(v___x_2128_, 1, v___x_2126_);
lean_ctor_set(v___x_2128_, 2, v___x_2127_);
lean_ctor_set(v___x_2128_, 3, v_structName_2106_);
v___x_2129_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2128_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_item_2105_ = stack[0].m_obj;
lean_object* v_structName_2106_ = stack[1].m_obj;
lean_object* v_a_2107_ = stack[2].m_obj;
lean_object* v_a_2108_ = stack[3].m_obj;
lean_object* v_a_2109_ = stack[4].m_obj;
lean_object* v_a_2110_ = stack[5].m_obj;
lean_object* v_a_2111_ = stack[6].m_obj;
lean_object* v_a_2112_ = stack[7].m_obj;
lean_object* v_res_2130_;
v_res_2130_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2105_, v_structName_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
stack->m_obj
 = v_res_2130_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object* v_item_2131_, lean_object* v_structName_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2131_, v_structName_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec_ref(v_item_2131_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object* v_cfg_2141_, lean_object* v_withRef_2142_, lean_object* v___x_2143_, lean_object* v_oldRef_2144_){
_start:
{
lean_object* v_ref_2145_; lean_object* v___x_2146_; 
v_ref_2145_ = l_Lean_replaceRef(v_cfg_2141_, v_oldRef_2144_);
v___x_2146_ = lean_apply_3(v_withRef_2142_, lean_box(0), v_ref_2145_, v___x_2143_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object* v_cfg_2147_, lean_object* v_withRef_2148_, lean_object* v___x_2149_, lean_object* v_oldRef_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(v_cfg_2147_, v_withRef_2148_, v___x_2149_, v_oldRef_2150_);
lean_dec(v_oldRef_2150_);
lean_dec(v_cfg_2147_);
return v_res_2151_;
}
}
uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t v_x_2152_){
_start:
{
uint32_t v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = 46;
v___x_2154_ = lean_uint32_dec_eq(v_x_2152_, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_2152_ = stack[0].m_num;
uint8_t v_res_2155_;
v_res_2155_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_2152_);
stack->m_num = v_res_2155_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object* v_x_2156_){
_start:
{
uint32_t v_x_880__boxed_2157_; uint8_t v_res_2158_; lean_object* v_r_2159_; 
v_x_880__boxed_2157_ = lean_unbox_uint32(v_x_2156_);
lean_dec(v_x_2156_);
v_res_2158_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_880__boxed_2157_);
v_r_2159_ = lean_box(v_res_2158_);
return v_r_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object* v___f_2160_, lean_object* v_s_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2160_);
v___x_2169_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2161_, v___x_2168_, v___y_2162_, lean_box(0), lean_box(0), v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object* v___f_2171_, lean_object* v_si_2172_, lean_object* v_val_2173_){
_start:
{
lean_object* v___y_2175_; lean_object* v___f_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___f_2181_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0));
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_string_utf8_byte_size(v_val_2173_);
lean_inc_ref(v_val_2173_);
v___x_2184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2184_, 0, v_val_2173_);
lean_ctor_set(v___x_2184_, 1, v___x_2182_);
lean_ctor_set(v___x_2184_, 2, v___x_2183_);
v___x_2185_ = l_String_Slice_contains___redArg(v___f_2171_, v___x_2184_, v___f_2181_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_box(0);
lean_inc_ref(v_val_2173_);
v___x_2187_ = l_Lean_Name_str___override(v___x_2186_, v_val_2173_);
v___y_2175_ = v___x_2187_;
goto v___jp_2174_;
}
else
{
lean_object* v___x_2188_; 
lean_inc_ref(v_val_2173_);
v___x_2188_ = l_String_toName(v_val_2173_);
v___y_2175_ = v___x_2188_;
goto v___jp_2174_;
}
v___jp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = lean_string_utf8_byte_size(v_val_2173_);
v___x_2178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2178_, 0, v_val_2173_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
lean_ctor_set(v___x_2178_, 2, v___x_2177_);
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2180_, 0, v_si_2172_);
lean_ctor_set(v___x_2180_, 1, v___x_2178_);
lean_ctor_set(v___x_2180_, 2, v___y_2175_);
lean_ctor_set(v___x_2180_, 3, v___x_2179_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object* v_atomAsIdent_2189_, lean_object* v_stx_2190_){
_start:
{
switch(lean_obj_tag(v_stx_2190_))
{
case 3:
{
lean_object* v___x_2191_; 
lean_dec_ref(v_atomAsIdent_2189_);
v___x_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_stx_2190_);
return v___x_2191_;
}
case 2:
{
lean_object* v_info_2192_; lean_object* v_val_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_info_2192_ = lean_ctor_get(v_stx_2190_, 0);
lean_inc(v_info_2192_);
v_val_2193_ = lean_ctor_get(v_stx_2190_, 1);
lean_inc_ref(v_val_2193_);
lean_dec_ref_known(v_stx_2190_, 2);
v___x_2194_ = lean_apply_2(v_atomAsIdent_2189_, v_info_2192_, v_val_2193_);
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
default: 
{
lean_object* v___x_2196_; 
lean_dec(v_stx_2190_);
lean_dec_ref(v_atomAsIdent_2189_);
v___x_2196_ = lean_box(0);
return v___x_2196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_init_2222_, lean_object* v_cfgs_2223_, lean_object* v_k_2224_, lean_object* v_onErr_2225_){
_start:
{
lean_object* v_toApplicative_2226_; lean_object* v_toPure_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v_toApplicative_2226_ = lean_ctor_get(v_inst_2220_, 0);
v_toPure_2227_ = lean_ctor_get(v_toApplicative_2226_, 1);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_array_get_size(v_cfgs_2223_);
v___x_2230_ = lean_nat_dec_lt(v___x_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; 
lean_inc(v_toPure_2227_);
lean_dec(v_onErr_2225_);
lean_dec(v_k_2224_);
lean_dec_ref(v_cfgs_2223_);
lean_dec_ref(v_inst_2221_);
lean_dec_ref(v_inst_2220_);
v___x_2231_ = lean_apply_2(v_toPure_2227_, lean_box(0), v_init_2222_);
return v___x_2231_;
}
else
{
lean_object* v___f_2232_; uint8_t v___x_2233_; 
lean_inc_ref(v_inst_2220_);
v___f_2232_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_2232_, 0, v_inst_2220_);
lean_closure_set(v___f_2232_, 1, v_inst_2221_);
lean_closure_set(v___f_2232_, 2, v_k_2224_);
lean_closure_set(v___f_2232_, 3, v_onErr_2225_);
v___x_2233_ = lean_nat_dec_le(v___x_2229_, v___x_2229_);
if (v___x_2233_ == 0)
{
if (v___x_2230_ == 0)
{
lean_object* v___x_2234_; 
lean_inc(v_toPure_2227_);
lean_dec_ref(v___f_2232_);
lean_dec_ref(v_cfgs_2223_);
lean_dec_ref(v_inst_2220_);
v___x_2234_ = lean_apply_2(v_toPure_2227_, lean_box(0), v_init_2222_);
return v___x_2234_;
}
else
{
size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = lean_usize_of_nat(v___x_2229_);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2220_, v___f_2232_, v_cfgs_2223_, v___x_2235_, v___x_2236_, v_init_2222_);
return v___x_2237_;
}
}
else
{
size_t v___x_2238_; size_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = ((size_t)0ULL);
v___x_2239_ = lean_usize_of_nat(v___x_2229_);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2220_, v___f_2232_, v_cfgs_2223_, v___x_2238_, v___x_2239_, v_init_2222_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_init_2243_, lean_object* v_cfg_2244_, lean_object* v_k_2245_, lean_object* v_onErr_2246_){
_start:
{
lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2244_);
v___x_2266_ = l_Lean_Syntax_isOfKind(v_cfg_2244_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2267_ = l_Lean_Syntax_getNumArgs(v_cfg_2244_);
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = lean_nat_dec_eq(v___x_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___f_2270_; lean_object* v_atomAsIdent_2271_; uint8_t v___x_2272_; 
v___f_2270_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3));
v_atomAsIdent_2271_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4));
v___x_2272_ = lean_nat_dec_le(v___x_2268_, v___x_2267_);
if (v___x_2272_ == 0)
{
lean_dec(v___x_2267_);
if (lean_obj_tag(v_cfg_2244_) == 2)
{
lean_object* v_info_2273_; lean_object* v_val_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec(v_onErr_2246_);
lean_dec_ref(v_inst_2242_);
lean_dec_ref(v_inst_2241_);
v_info_2273_ = lean_ctor_get(v_cfg_2244_, 0);
v_val_2274_ = lean_ctor_get(v_cfg_2244_, 1);
lean_inc_ref(v_val_2274_);
lean_inc(v_info_2273_);
v___x_2275_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(v___f_2270_, v_info_2273_, v_val_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2277_ = l_Lean_mkCIdentFrom(v_cfg_2244_, v___x_2276_, v___x_2272_);
v___x_2278_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2279_ = l_Lean_TSyntax_getId(v___x_2275_);
v___x_2280_ = l_Lean_Name_eraseMacroScopes(v___x_2279_);
lean_dec(v___x_2279_);
v___x_2281_ = lean_box(0);
lean_inc(v___x_2275_);
v___x_2282_ = l_Lean_Syntax_identComponents(v___x_2275_, v___x_2281_);
v___x_2283_ = lean_box(0);
v___x_2284_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2284_, 0, v_cfg_2244_);
lean_ctor_set(v___x_2284_, 1, v___x_2275_);
lean_ctor_set(v___x_2284_, 2, v___x_2277_);
lean_ctor_set(v___x_2284_, 3, v___x_2278_);
lean_ctor_set(v___x_2284_, 4, v___x_2280_);
lean_ctor_set(v___x_2284_, 5, v___x_2282_);
lean_ctor_set(v___x_2284_, 6, v___x_2283_);
v___x_2285_ = lean_apply_2(v_k_2245_, v_init_2243_, v___x_2284_);
return v___x_2285_;
}
else
{
lean_dec(v_k_2245_);
goto v___jp_2258_;
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_unsigned_to_nat(0u);
v___x_2287_ = l_Lean_Syntax_getArg(v_cfg_2244_, v___x_2286_);
if (lean_obj_tag(v___x_2287_) == 2)
{
lean_object* v_val_2288_; lean_object* v___y_2290_; uint8_t v_val_2291_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_val_2288_ = lean_ctor_get(v___x_2287_, 1);
v___x_2302_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2303_ = lean_string_dec_eq(v_val_2288_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2305_ = lean_string_dec_eq(v_val_2288_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
lean_inc_ref(v_val_2288_);
lean_dec_ref_known(v___x_2287_, 2);
v___x_2306_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2307_ = lean_string_dec_eq(v_val_2288_, v___x_2306_);
lean_dec_ref(v_val_2288_);
if (v___x_2307_ == 0)
{
lean_dec(v___x_2267_);
lean_dec(v_k_2245_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = lean_unsigned_to_nat(5u);
v___x_2309_ = lean_nat_dec_le(v___x_2267_, v___x_2308_);
lean_dec(v___x_2267_);
if (v___x_2309_ == 0)
{
lean_dec(v_k_2245_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = l_Lean_Syntax_getArg(v_cfg_2244_, v___x_2268_);
v___x_2311_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2271_, v___x_2310_);
if (lean_obj_tag(v___x_2311_) == 1)
{
lean_object* v_val_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_onErr_2246_);
lean_dec_ref(v_inst_2242_);
lean_dec_ref(v_inst_2241_);
v_val_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc_n(v_val_2312_, 2);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = lean_unsigned_to_nat(3u);
v___x_2314_ = l_Lean_Syntax_getArg(v_cfg_2244_, v___x_2313_);
v___x_2315_ = lean_box(0);
v___x_2316_ = l_Lean_TSyntax_getId(v_val_2312_);
v___x_2317_ = l_Lean_Name_eraseMacroScopes(v___x_2316_);
lean_dec(v___x_2316_);
v___x_2318_ = l_Lean_Syntax_identComponents(v_val_2312_, v___x_2315_);
v___x_2319_ = lean_box(0);
v___x_2320_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2320_, 0, v_cfg_2244_);
lean_ctor_set(v___x_2320_, 1, v_val_2312_);
lean_ctor_set(v___x_2320_, 2, v___x_2314_);
lean_ctor_set(v___x_2320_, 3, v___x_2315_);
lean_ctor_set(v___x_2320_, 4, v___x_2317_);
lean_ctor_set(v___x_2320_, 5, v___x_2318_);
lean_ctor_set(v___x_2320_, 6, v___x_2319_);
v___x_2321_ = lean_apply_2(v_k_2245_, v_init_2243_, v___x_2320_);
return v___x_2321_;
}
else
{
lean_dec(v___x_2311_);
lean_dec(v_k_2245_);
goto v___jp_2258_;
}
}
}
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_box(v___x_2303_);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
v___y_2290_ = v___x_2323_;
v_val_2291_ = v___x_2303_;
goto v___jp_2289_;
}
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_box(v___x_2272_);
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
v___y_2290_ = v___x_2325_;
v_val_2291_ = v___x_2272_;
goto v___jp_2289_;
}
v___jp_2289_:
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = lean_unsigned_to_nat(2u);
v___x_2293_ = lean_nat_dec_eq(v___x_2267_, v___x_2292_);
lean_dec(v___x_2267_);
if (v___x_2293_ == 0)
{
lean_dec(v___y_2290_);
lean_dec_ref_known(v___x_2287_, 2);
lean_dec(v_k_2245_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = l_Lean_Syntax_getArg(v_cfg_2244_, v___x_2268_);
v___x_2295_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2271_, v___x_2294_);
if (lean_obj_tag(v___x_2295_) == 1)
{
lean_dec(v_onErr_2246_);
lean_dec_ref(v_inst_2242_);
lean_dec_ref(v_inst_2241_);
if (v_val_2291_ == 0)
{
lean_object* v_val_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_val_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2297_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2298_ = l_Lean_mkCIdentFrom(v___x_2287_, v___x_2297_, v_val_2291_);
lean_dec_ref_known(v___x_2287_, 2);
v___y_2248_ = v_val_2296_;
v___y_2249_ = v___y_2290_;
v___y_2250_ = v___x_2298_;
goto v___jp_2247_;
}
else
{
lean_object* v_val_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_val_2299_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2299_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2300_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2301_ = l_Lean_mkCIdentFrom(v___x_2287_, v___x_2300_, v___x_2269_);
lean_dec_ref_known(v___x_2287_, 2);
v___y_2248_ = v_val_2299_;
v___y_2249_ = v___y_2290_;
v___y_2250_ = v___x_2301_;
goto v___jp_2247_;
}
}
else
{
lean_dec(v___x_2295_);
lean_dec(v___y_2290_);
lean_dec_ref_known(v___x_2287_, 2);
lean_dec(v_k_2245_);
goto v___jp_2258_;
}
}
}
}
else
{
lean_dec(v___x_2287_);
lean_dec(v___x_2267_);
lean_dec(v_k_2245_);
goto v___jp_2258_;
}
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v___x_2267_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = l_Lean_Syntax_getArg(v_cfg_2244_, v___x_2326_);
lean_dec(v_cfg_2244_);
v_cfg_2244_ = v___x_2327_;
goto _start;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = l_Lean_Syntax_getArgs(v_cfg_2244_);
lean_dec(v_cfg_2244_);
v___x_2330_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2241_, v_inst_2242_, v_init_2243_, v___x_2329_, v_k_2245_, v_onErr_2246_);
return v___x_2330_;
}
v___jp_2247_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2251_ = l_Lean_TSyntax_getId(v___y_2248_);
v___x_2252_ = l_Lean_Name_eraseMacroScopes(v___x_2251_);
lean_dec(v___x_2251_);
v___x_2253_ = lean_box(0);
lean_inc(v___y_2248_);
v___x_2254_ = l_Lean_Syntax_identComponents(v___y_2248_, v___x_2253_);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2256_, 0, v_cfg_2244_);
lean_ctor_set(v___x_2256_, 1, v___y_2248_);
lean_ctor_set(v___x_2256_, 2, v___y_2250_);
lean_ctor_set(v___x_2256_, 3, v___y_2249_);
lean_ctor_set(v___x_2256_, 4, v___x_2252_);
lean_ctor_set(v___x_2256_, 5, v___x_2254_);
lean_ctor_set(v___x_2256_, 6, v___x_2255_);
v___x_2257_ = lean_apply_2(v_k_2245_, v_init_2243_, v___x_2256_);
return v___x_2257_;
}
v___jp_2258_:
{
lean_object* v_toBind_2259_; lean_object* v_getRef_2260_; lean_object* v_withRef_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; 
v_toBind_2259_ = lean_ctor_get(v_inst_2241_, 1);
lean_inc(v_toBind_2259_);
lean_dec_ref(v_inst_2241_);
v_getRef_2260_ = lean_ctor_get(v_inst_2242_, 0);
lean_inc(v_getRef_2260_);
v_withRef_2261_ = lean_ctor_get(v_inst_2242_, 1);
lean_inc(v_withRef_2261_);
lean_dec_ref(v_inst_2242_);
lean_inc(v_cfg_2244_);
v___x_2262_ = lean_apply_2(v_onErr_2246_, v_init_2243_, v_cfg_2244_);
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2263_, 0, v_cfg_2244_);
lean_closure_set(v___f_2263_, 1, v_withRef_2261_);
lean_closure_set(v___f_2263_, 2, v___x_2262_);
v___x_2264_ = lean_apply_4(v_toBind_2259_, lean_box(0), lean_box(0), v_getRef_2260_, v___f_2263_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_k_2333_, lean_object* v_onErr_2334_, lean_object* v_x_2335_, lean_object* v_cfg_x27_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2331_, v_inst_2332_, v_x_2335_, v_cfg_x27_2336_, v_k_2333_, v_onErr_2334_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object* v_00_u03b1_2338_, lean_object* v_m_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_init_2342_, lean_object* v_cfg_2343_, lean_object* v_k_2344_, lean_object* v_onErr_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2340_, v_inst_2341_, v_init_2342_, v_cfg_2343_, v_k_2344_, v_onErr_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object* v_00_u03b1_2347_, lean_object* v_m_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_init_2351_, lean_object* v_cfgs_2352_, lean_object* v_k_2353_, lean_object* v_onErr_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2349_, v_inst_2350_, v_init_2351_, v_cfgs_2352_, v_k_2353_, v_onErr_2354_);
return v___x_2355_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_2364_, uint8_t v___y_2365_, lean_object* v_x_2366_){
_start:
{
if (lean_obj_tag(v_x_2366_) == 1)
{
lean_object* v_pre_2367_; 
v_pre_2367_ = lean_ctor_get(v_x_2366_, 0);
switch(lean_obj_tag(v_pre_2367_))
{
case 1:
{
lean_object* v_pre_2368_; 
v_pre_2368_ = lean_ctor_get(v_pre_2367_, 0);
switch(lean_obj_tag(v_pre_2368_))
{
case 0:
{
lean_object* v_str_2369_; lean_object* v_str_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_str_2369_ = lean_ctor_get(v_x_2366_, 1);
v_str_2370_ = lean_ctor_get(v_pre_2367_, 1);
v___x_2371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_2372_ = lean_string_dec_eq(v_str_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_2374_ = lean_string_dec_eq(v_str_2370_, v___x_2373_);
if (v___x_2374_ == 0)
{
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_2376_ = lean_string_dec_eq(v_str_2369_, v___x_2375_);
if (v___x_2376_ == 0)
{
return v___x_2376_;
}
else
{
return v_suppressElabErrors_2364_;
}
}
}
else
{
lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_2378_ = lean_string_dec_eq(v_str_2369_, v___x_2377_);
if (v___x_2378_ == 0)
{
return v___x_2378_;
}
else
{
return v_suppressElabErrors_2364_;
}
}
}
case 1:
{
lean_object* v_pre_2379_; 
v_pre_2379_ = lean_ctor_get(v_pre_2368_, 0);
if (lean_obj_tag(v_pre_2379_) == 0)
{
lean_object* v_str_2380_; lean_object* v_str_2381_; lean_object* v_str_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_str_2380_ = lean_ctor_get(v_x_2366_, 1);
v_str_2381_ = lean_ctor_get(v_pre_2367_, 1);
v_str_2382_ = lean_ctor_get(v_pre_2368_, 1);
v___x_2383_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_2384_ = lean_string_dec_eq(v_str_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
return v___x_2384_;
}
else
{
lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_2386_ = lean_string_dec_eq(v_str_2381_, v___x_2385_);
if (v___x_2386_ == 0)
{
return v___x_2386_;
}
else
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_2388_ = lean_string_dec_eq(v_str_2380_, v___x_2387_);
if (v___x_2388_ == 0)
{
return v___x_2388_;
}
else
{
return v_suppressElabErrors_2364_;
}
}
}
}
else
{
return v___y_2365_;
}
}
default: 
{
return v___y_2365_;
}
}
}
case 0:
{
lean_object* v_str_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v_str_2389_ = lean_ctor_get(v_x_2366_, 1);
v___x_2390_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_2391_ = lean_string_dec_eq(v_str_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
return v___x_2391_;
}
else
{
return v_suppressElabErrors_2364_;
}
}
default: 
{
return v___y_2365_;
}
}
}
else
{
return v___y_2365_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_2364_ = stack[0].m_num;
uint8_t v___y_2365_ = stack[1].m_num;
lean_object* v_x_2366_ = stack[2].m_obj;
uint8_t v_res_2392_;
v_res_2392_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_2364_, v___y_2365_, v_x_2366_);
stack->m_num = v_res_2392_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2393_, lean_object* v___y_2394_, lean_object* v_x_2395_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2396_; uint8_t v___y_6094__boxed_2397_; uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_suppressElabErrors_boxed_2396_ = lean_unbox(v_suppressElabErrors_2393_);
v___y_6094__boxed_2397_ = lean_unbox(v___y_2394_);
v_res_2398_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_2396_, v___y_6094__boxed_2397_, v_x_2395_);
lean_dec(v_x_2395_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2400_, lean_object* v_msgData_2401_, uint8_t v_severity_2402_, uint8_t v_isSilent_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; uint8_t v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v_toCold_2417_; lean_object* v___y_2418_; lean_object* v___y_2447_; lean_object* v___y_2448_; uint8_t v___y_2449_; lean_object* v___y_2450_; uint8_t v___y_2451_; uint8_t v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2474_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; uint8_t v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; uint8_t v___y_2484_; uint8_t v___y_2485_; uint8_t v___y_2486_; uint8_t v___x_2497_; uint8_t v___y_2499_; uint8_t v___y_2500_; uint8_t v___y_2501_; uint8_t v___y_2503_; uint8_t v___x_2511_; 
v___x_2497_ = 2;
v___x_2511_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2402_, v___x_2497_);
if (v___x_2511_ == 0)
{
v___y_2503_ = v___x_2511_;
goto v___jp_2502_;
}
else
{
uint8_t v___x_2512_; 
lean_inc_ref(v_msgData_2401_);
v___x_2512_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2401_);
v___y_2503_ = v___x_2512_;
goto v___jp_2502_;
}
v___jp_2409_:
{
lean_object* v_currNamespace_2419_; lean_object* v_openDecls_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_env_2425_; lean_object* v_nextMacroScope_2426_; lean_object* v_ngen_2427_; lean_object* v_auxDeclNGen_2428_; lean_object* v_traceState_2429_; lean_object* v_cache_2430_; lean_object* v_recordedDeps_2431_; lean_object* v_messages_2432_; lean_object* v_infoState_2433_; lean_object* v_snapshotTasks_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2445_; 
v_currNamespace_2419_ = lean_ctor_get(v_toCold_2417_, 4);
v_openDecls_2420_ = lean_ctor_get(v_toCold_2417_, 5);
lean_inc(v_openDecls_2420_);
lean_inc(v_currNamespace_2419_);
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_currNamespace_2419_);
lean_ctor_set(v___x_2421_, 1, v_openDecls_2420_);
v___x_2422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v___y_2411_);
lean_inc_ref(v___y_2415_);
lean_inc_ref(v___y_2416_);
v___x_2423_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2423_, 0, v___y_2416_);
lean_ctor_set(v___x_2423_, 1, v___y_2414_);
lean_ctor_set(v___x_2423_, 2, v___y_2412_);
lean_ctor_set(v___x_2423_, 3, v___y_2415_);
lean_ctor_set(v___x_2423_, 4, v___x_2422_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*5, v___y_2410_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*5 + 1, v___y_2413_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*5 + 2, v_isSilent_2403_);
v___x_2424_ = lean_st_ref_take(v___y_2418_);
v_env_2425_ = lean_ctor_get(v___x_2424_, 0);
v_nextMacroScope_2426_ = lean_ctor_get(v___x_2424_, 1);
v_ngen_2427_ = lean_ctor_get(v___x_2424_, 2);
v_auxDeclNGen_2428_ = lean_ctor_get(v___x_2424_, 3);
v_traceState_2429_ = lean_ctor_get(v___x_2424_, 4);
v_cache_2430_ = lean_ctor_get(v___x_2424_, 5);
v_recordedDeps_2431_ = lean_ctor_get(v___x_2424_, 6);
v_messages_2432_ = lean_ctor_get(v___x_2424_, 7);
v_infoState_2433_ = lean_ctor_get(v___x_2424_, 8);
v_snapshotTasks_2434_ = lean_ctor_get(v___x_2424_, 9);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2436_ = v___x_2424_;
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_snapshotTasks_2434_);
lean_inc(v_infoState_2433_);
lean_inc(v_messages_2432_);
lean_inc(v_recordedDeps_2431_);
lean_inc(v_cache_2430_);
lean_inc(v_traceState_2429_);
lean_inc(v_auxDeclNGen_2428_);
lean_inc(v_ngen_2427_);
lean_inc(v_nextMacroScope_2426_);
lean_inc(v_env_2425_);
lean_dec(v___x_2424_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2438_ = lean_box(0);
v___x_2439_ = l_Lean_MessageLog_add(v___x_2423_, v_messages_2432_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 7, v___x_2439_);
v___x_2441_ = v___x_2436_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_env_2425_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_nextMacroScope_2426_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_ngen_2427_);
lean_ctor_set(v_reuseFailAlloc_2444_, 3, v_auxDeclNGen_2428_);
lean_ctor_set(v_reuseFailAlloc_2444_, 4, v_traceState_2429_);
lean_ctor_set(v_reuseFailAlloc_2444_, 5, v_cache_2430_);
lean_ctor_set(v_reuseFailAlloc_2444_, 6, v_recordedDeps_2431_);
lean_ctor_set(v_reuseFailAlloc_2444_, 7, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2444_, 8, v_infoState_2433_);
lean_ctor_set(v_reuseFailAlloc_2444_, 9, v_snapshotTasks_2434_);
v___x_2441_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_st_ref_put(v___y_2418_, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2438_);
return v___x_2443_;
}
}
}
v___jp_2446_:
{
lean_object* v_fileName_2455_; lean_object* v_fileMap_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2472_; 
v_fileName_2455_ = lean_ctor_get(v___y_2450_, 0);
v_fileMap_2456_ = lean_ctor_get(v___y_2450_, 1);
v___x_2457_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2401_);
v___x_2458_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_2457_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2472_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2472_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_inc_ref_n(v_fileMap_2456_, 2);
v___x_2463_ = l_Lean_FileMap_toPosition(v_fileMap_2456_, v___y_2453_);
lean_dec(v___y_2453_);
v___x_2464_ = l_Lean_FileMap_toPosition(v_fileMap_2456_, v___y_2454_);
lean_dec(v___y_2454_);
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
v___x_2466_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
if (v___y_2452_ == 0)
{
lean_del_object(v___x_2461_);
lean_dec_ref(v___y_2448_);
v___y_2410_ = v___y_2449_;
v___y_2411_ = v_a_2459_;
v___y_2412_ = v___x_2465_;
v___y_2413_ = v___y_2451_;
v___y_2414_ = v___x_2463_;
v___y_2415_ = v___x_2466_;
v___y_2416_ = v_fileName_2455_;
v_toCold_2417_ = v___y_2447_;
v___y_2418_ = v___y_2407_;
goto v___jp_2409_;
}
else
{
uint8_t v___x_2467_; 
lean_inc(v_a_2459_);
v___x_2467_ = l_Lean_MessageData_hasTag(v___y_2448_, v_a_2459_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_dec_ref_known(v___x_2465_, 1);
lean_dec_ref(v___x_2463_);
lean_dec(v_a_2459_);
v___x_2468_ = lean_box(0);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2468_);
v___x_2470_ = v___x_2461_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
lean_del_object(v___x_2461_);
v___y_2410_ = v___y_2449_;
v___y_2411_ = v_a_2459_;
v___y_2412_ = v___x_2465_;
v___y_2413_ = v___y_2451_;
v___y_2414_ = v___x_2463_;
v___y_2415_ = v___x_2466_;
v___y_2416_ = v_fileName_2455_;
v_toCold_2417_ = v___y_2447_;
v___y_2418_ = v___y_2407_;
goto v___jp_2409_;
}
}
}
}
v___jp_2473_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Syntax_getTailPos_x3f(v___y_2477_, v___y_2478_);
lean_dec(v___y_2477_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_inc(v___y_2480_);
v___y_2447_ = v___y_2474_;
v___y_2448_ = v___y_2475_;
v___y_2449_ = v___y_2478_;
v___y_2450_ = v___y_2474_;
v___y_2451_ = v___y_2479_;
v___y_2452_ = v___y_2476_;
v___y_2453_ = v___y_2480_;
v___y_2454_ = v___y_2480_;
goto v___jp_2446_;
}
else
{
lean_object* v_val_2482_; 
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___y_2447_ = v___y_2474_;
v___y_2448_ = v___y_2475_;
v___y_2449_ = v___y_2478_;
v___y_2450_ = v___y_2474_;
v___y_2451_ = v___y_2479_;
v___y_2452_ = v___y_2476_;
v___y_2453_ = v___y_2480_;
v___y_2454_ = v_val_2482_;
goto v___jp_2446_;
}
}
v___jp_2483_:
{
lean_object* v_toCold_2487_; lean_object* v_ref_2488_; uint8_t v_suppressElabErrors_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v_ref_2493_; lean_object* v___x_2494_; 
v_toCold_2487_ = lean_ctor_get(v___y_2406_, 0);
v_ref_2488_ = lean_ctor_get(v___y_2406_, 2);
v_suppressElabErrors_2489_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*3 + 2);
v___x_2490_ = lean_box(v_suppressElabErrors_2489_);
v___x_2491_ = lean_box(v___y_2484_);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2492_, 0, v___x_2490_);
lean_closure_set(v___f_2492_, 1, v___x_2491_);
v_ref_2493_ = l_Lean_replaceRef(v_ref_2400_, v_ref_2488_);
v___x_2494_ = l_Lean_Syntax_getPos_x3f(v_ref_2493_, v___y_2485_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
v___y_2474_ = v_toCold_2487_;
v___y_2475_ = v___f_2492_;
v___y_2476_ = v_suppressElabErrors_2489_;
v___y_2477_ = v_ref_2493_;
v___y_2478_ = v___y_2485_;
v___y_2479_ = v___y_2486_;
v___y_2480_ = v___x_2495_;
goto v___jp_2473_;
}
else
{
lean_object* v_val_2496_; 
v_val_2496_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v___x_2494_, 1);
v___y_2474_ = v_toCold_2487_;
v___y_2475_ = v___f_2492_;
v___y_2476_ = v_suppressElabErrors_2489_;
v___y_2477_ = v_ref_2493_;
v___y_2478_ = v___y_2485_;
v___y_2479_ = v___y_2486_;
v___y_2480_ = v_val_2496_;
goto v___jp_2473_;
}
}
v___jp_2498_:
{
if (v___y_2501_ == 0)
{
v___y_2484_ = v___y_2499_;
v___y_2485_ = v___y_2500_;
v___y_2486_ = v_severity_2402_;
goto v___jp_2483_;
}
else
{
v___y_2484_ = v___y_2499_;
v___y_2485_ = v___y_2500_;
v___y_2486_ = v___x_2497_;
goto v___jp_2483_;
}
}
v___jp_2502_:
{
if (v___y_2503_ == 0)
{
uint8_t v___x_2504_; uint8_t v___x_2505_; 
v___x_2504_ = 1;
v___x_2505_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2402_, v___x_2504_);
if (v___x_2505_ == 0)
{
v___y_2499_ = v___y_2503_;
v___y_2500_ = v___y_2503_;
v___y_2501_ = v___x_2505_;
goto v___jp_2498_;
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2506_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2406_);
v___x_2507_ = l_Lean_warningAsError;
v___x_2508_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_2506_, v___x_2507_);
lean_dec_ref(v___x_2506_);
v___y_2499_ = v___y_2503_;
v___y_2500_ = v___y_2503_;
v___y_2501_ = v___x_2508_;
goto v___jp_2498_;
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec_ref(v_msgData_2401_);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2400_ = stack[0].m_obj;
lean_object* v_msgData_2401_ = stack[1].m_obj;
uint8_t v_severity_2402_ = stack[2].m_num;
uint8_t v_isSilent_2403_ = stack[3].m_num;
lean_object* v___y_2404_ = stack[4].m_obj;
lean_object* v___y_2405_ = stack[5].m_obj;
lean_object* v___y_2406_ = stack[6].m_obj;
lean_object* v___y_2407_ = stack[7].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2400_, v_msgData_2401_, v_severity_2402_, v_isSilent_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2514_, lean_object* v_msgData_2515_, lean_object* v_severity_2516_, lean_object* v_isSilent_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
uint8_t v_severity_boxed_2523_; uint8_t v_isSilent_boxed_2524_; lean_object* v_res_2525_; 
v_severity_boxed_2523_ = lean_unbox(v_severity_2516_);
v_isSilent_boxed_2524_ = lean_unbox(v_isSilent_2517_);
v_res_2525_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2514_, v_msgData_2515_, v_severity_boxed_2523_, v_isSilent_boxed_2524_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v_ref_2514_);
return v_res_2525_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object* v_msgData_2526_, uint8_t v_severity_2527_, uint8_t v_isSilent_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_ref_2536_; lean_object* v___x_2537_; 
v_ref_2536_ = lean_ctor_get(v___y_2533_, 2);
v___x_2537_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2536_, v_msgData_2526_, v_severity_2527_, v_isSilent_2528_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2537_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2526_ = stack[0].m_obj;
uint8_t v_severity_2527_ = stack[1].m_num;
uint8_t v_isSilent_2528_ = stack[2].m_num;
lean_object* v___y_2529_ = stack[3].m_obj;
lean_object* v___y_2530_ = stack[4].m_obj;
lean_object* v___y_2531_ = stack[5].m_obj;
lean_object* v___y_2532_ = stack[6].m_obj;
lean_object* v___y_2533_ = stack[7].m_obj;
lean_object* v___y_2534_ = stack[8].m_obj;
lean_object* v_res_2538_;
v_res_2538_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2526_, v_severity_2527_, v_isSilent_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
stack->m_obj
 = v_res_2538_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2539_, lean_object* v_severity_2540_, lean_object* v_isSilent_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
uint8_t v_severity_boxed_2549_; uint8_t v_isSilent_boxed_2550_; lean_object* v_res_2551_; 
v_severity_boxed_2549_ = lean_unbox(v_severity_2540_);
v_isSilent_boxed_2550_ = lean_unbox(v_isSilent_2541_);
v_res_2551_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2539_, v_severity_boxed_2549_, v_isSilent_boxed_2550_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2551_;
}
}
lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object* v_msgData_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v___x_2560_; uint8_t v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = 2;
v___x_2561_ = 0;
v___x_2562_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2552_, v___x_2560_, v___x_2561_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
return v___x_2562_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2552_ = stack[0].m_obj;
lean_object* v___y_2553_ = stack[1].m_obj;
lean_object* v___y_2554_ = stack[2].m_obj;
lean_object* v___y_2555_ = stack[3].m_obj;
lean_object* v___y_2556_ = stack[4].m_obj;
lean_object* v___y_2557_ = stack[5].m_obj;
lean_object* v___y_2558_ = stack[6].m_obj;
lean_object* v_res_2563_;
v_res_2563_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(lean_object* v_msgData_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2572_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object* v_ref_2573_, lean_object* v_msgData_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
uint8_t v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = 2;
v___x_2583_ = 0;
v___x_2584_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2573_, v_msgData_2574_, v___x_2582_, v___x_2583_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2584_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2573_ = stack[0].m_obj;
lean_object* v_msgData_2574_ = stack[1].m_obj;
lean_object* v___y_2575_ = stack[2].m_obj;
lean_object* v___y_2576_ = stack[3].m_obj;
lean_object* v___y_2577_ = stack[4].m_obj;
lean_object* v___y_2578_ = stack[5].m_obj;
lean_object* v___y_2579_ = stack[6].m_obj;
lean_object* v___y_2580_ = stack[7].m_obj;
lean_object* v_res_2585_;
v_res_2585_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2573_, v_msgData_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
stack->m_obj
 = v_res_2585_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object* v_ref_2586_, lean_object* v_msgData_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2586_, v_msgData_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v_ref_2586_);
return v_res_2595_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0));
v___x_2598_ = l_Lean_stringToMessageData(v___x_2597_);
return v___x_2598_;
}
}
lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object* v_ex_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
if (lean_obj_tag(v_ex_2599_) == 0)
{
lean_object* v_ref_2607_; lean_object* v_msg_2608_; lean_object* v___x_2609_; 
v_ref_2607_ = lean_ctor_get(v_ex_2599_, 0);
lean_inc(v_ref_2607_);
v_msg_2608_ = lean_ctor_get(v_ex_2599_, 1);
lean_inc_ref(v_msg_2608_);
lean_dec_ref_known(v_ex_2599_, 2);
v___x_2609_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2607_, v_msg_2608_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v_ref_2607_);
return v___x_2609_;
}
else
{
lean_object* v_id_2610_; uint8_t v___y_2612_; uint8_t v___x_2634_; 
v_id_2610_ = lean_ctor_get(v_ex_2599_, 0);
lean_inc(v_id_2610_);
v___x_2634_ = l_Lean_Elab_isAbortExceptionId(v_id_2610_);
if (v___x_2634_ == 0)
{
uint8_t v___x_2635_; 
v___x_2635_ = l_Lean_Exception_isInterrupt(v_ex_2599_);
lean_dec_ref_known(v_ex_2599_, 2);
v___y_2612_ = v___x_2635_;
goto v___jp_2611_;
}
else
{
lean_dec_ref_known(v_ex_2599_, 2);
v___y_2612_ = v___x_2634_;
goto v___jp_2611_;
}
v___jp_2611_:
{
if (v___y_2612_ == 0)
{
lean_object* v_ref_2613_; lean_object* v___x_2614_; 
v_ref_2613_ = lean_ctor_get(v___y_2604_, 2);
v___x_2614_ = l_Lean_InternalExceptionId_getName(v_id_2610_);
lean_dec(v_id_2610_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
v___x_2617_ = l_Lean_MessageData_ofName(v_a_2615_);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2616_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_2618_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v___x_2619_;
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2631_; 
v_a_2620_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2622_ = v___x_2614_;
v_isShared_2623_ = v_isSharedCheck_2631_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2614_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2631_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2624_ = lean_io_error_to_string(v_a_2620_);
v___x_2625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v___x_2626_ = l_Lean_MessageData_ofFormat(v___x_2625_);
lean_inc(v_ref_2613_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_ref_2613_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2627_);
v___x_2629_ = v___x_2622_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec(v_id_2610_);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
return v___x_2633_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_2599_ = stack[0].m_obj;
lean_object* v___y_2600_ = stack[1].m_obj;
lean_object* v___y_2601_ = stack[2].m_obj;
lean_object* v___y_2602_ = stack[3].m_obj;
lean_object* v___y_2603_ = stack[4].m_obj;
lean_object* v___y_2604_ = stack[5].m_obj;
lean_object* v___y_2605_ = stack[6].m_obj;
lean_object* v_res_2636_;
v_res_2636_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
stack->m_obj
 = v_res_2636_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object* v_ex_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2645_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object* v_a_2646_, lean_object* v_config_2647_, lean_object* v_____r_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_2646_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2664_; 
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2656_, 0);
lean_dec(v_unused_2665_);
v___x_2658_ = v___x_2656_;
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
else
{
lean_dec(v___x_2656_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_config_2647_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2660_);
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v_config_2647_);
v_a_2666_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2656_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2656_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2646_ = stack[0].m_obj;
lean_object* v_config_2647_ = stack[1].m_obj;
lean_object* v_____r_2648_ = stack[2].m_obj;
lean_object* v___y_2649_ = stack[3].m_obj;
lean_object* v___y_2650_ = stack[4].m_obj;
lean_object* v___y_2651_ = stack[5].m_obj;
lean_object* v___y_2652_ = stack[6].m_obj;
lean_object* v___y_2653_ = stack[7].m_obj;
lean_object* v___y_2654_ = stack[8].m_obj;
lean_object* v_res_2674_;
v_res_2674_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2646_, v_config_2647_, v_____r_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
stack->m_obj
 = v_res_2674_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object* v_a_2675_, lean_object* v_config_2676_, lean_object* v_____r_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2675_, v_config_2676_, v_____r_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2685_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object* v___f_2686_, lean_object* v_x_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_box(0);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v___y_2689_);
lean_inc_ref(v___y_2688_);
v___x_2696_ = lean_apply_8(v___f_2686_, v___x_2695_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, lean_box(0));
return v___x_2696_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2686_ = stack[0].m_obj;
lean_object* v_x_2687_ = stack[1].m_obj;
lean_object* v___y_2688_ = stack[2].m_obj;
lean_object* v___y_2689_ = stack[3].m_obj;
lean_object* v___y_2690_ = stack[4].m_obj;
lean_object* v___y_2691_ = stack[5].m_obj;
lean_object* v___y_2692_ = stack[6].m_obj;
lean_object* v___y_2693_ = stack[7].m_obj;
lean_object* v_res_2697_;
v_res_2697_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2686_, v_x_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
stack->m_obj
 = v_res_2697_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(lean_object* v___f_2698_, lean_object* v_x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2698_, v_x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec_ref(v_x_2699_);
return v_res_2707_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object* v_eval_2708_, lean_object* v_config_2709_, lean_object* v_item_2710_, uint8_t v_logExceptions_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___y_2720_; lean_object* v___x_2738_; 
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
lean_inc(v_a_2715_);
lean_inc_ref(v_a_2714_);
lean_inc(v_a_2713_);
lean_inc_ref(v_a_2712_);
lean_inc(v_config_2709_);
v___x_2738_ = lean_apply_9(v_eval_2708_, v_config_2709_, v_item_2710_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, lean_box(0));
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_dec(v_config_2709_);
return v___x_2738_;
}
else
{
lean_object* v_a_2739_; lean_object* v___f_2740_; uint8_t v___y_2742_; uint8_t v___x_2759_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_n(v_a_2739_, 2);
lean_inc(v_config_2709_);
v___f_2740_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2740_, 0, v_a_2739_);
lean_closure_set(v___f_2740_, 1, v_config_2709_);
v___x_2759_ = l_Lean_Exception_isInterrupt(v_a_2739_);
if (v___x_2759_ == 0)
{
uint8_t v___x_2760_; 
lean_inc(v_a_2739_);
v___x_2760_ = l_Lean_Exception_isRuntime(v_a_2739_);
v___y_2742_ = v___x_2760_;
goto v___jp_2741_;
}
else
{
v___y_2742_ = v___x_2759_;
goto v___jp_2741_;
}
v___jp_2741_:
{
if (v___y_2742_ == 0)
{
if (v_logExceptions_2711_ == 0)
{
lean_dec_ref(v___f_2740_);
lean_dec(v_a_2739_);
lean_dec(v_config_2709_);
return v___x_2738_;
}
else
{
lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2757_; 
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; 
v_unused_2758_ = lean_ctor_get(v___x_2738_, 0);
lean_dec(v_unused_2758_);
v___x_2744_ = v___x_2738_;
v_isShared_2745_ = v_isSharedCheck_2757_;
goto v_resetjp_2743_;
}
else
{
lean_dec(v___x_2738_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2757_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
if (lean_obj_tag(v_a_2739_) == 1)
{
lean_object* v_extra_2746_; 
v_extra_2746_ = lean_ctor_get(v_a_2739_, 1);
if (lean_obj_tag(v_extra_2746_) == 0)
{
lean_object* v_id_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
lean_dec_ref(v___f_2740_);
v_id_2747_ = lean_ctor_get(v_a_2739_, 0);
v___x_2748_ = l_Lean_Elab_abortTermExceptionId;
v___x_2749_ = l_Lean_instBEqInternalExceptionId_beq(v_id_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_del_object(v___x_2744_);
v___x_2750_ = lean_box(0);
v___x_2751_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2739_, v_config_2709_, v___x_2750_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
v___y_2720_ = v___x_2751_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2753_; 
lean_dec_ref_known(v_a_2739_, 2);
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 0);
lean_ctor_set(v___x_2744_, 0, v_config_2709_);
v___x_2753_ = v___x_2744_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_config_2709_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
lean_object* v___x_2755_; 
lean_del_object(v___x_2744_);
lean_dec(v_config_2709_);
v___x_2755_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2740_, v_a_2739_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec_ref_known(v_a_2739_, 2);
v___y_2720_ = v___x_2755_;
goto v___jp_2719_;
}
}
else
{
lean_object* v___x_2756_; 
lean_del_object(v___x_2744_);
lean_dec(v_config_2709_);
v___x_2756_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2740_, v_a_2739_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2739_);
v___y_2720_ = v___x_2756_;
goto v___jp_2719_;
}
}
}
}
else
{
lean_dec_ref(v___f_2740_);
lean_dec(v_a_2739_);
lean_dec(v_config_2709_);
return v___x_2738_;
}
}
}
v___jp_2719_:
{
if (lean_obj_tag(v___y_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2729_; 
v_a_2721_ = lean_ctor_get(v___y_2720_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___y_2720_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2723_ = v___y_2720_;
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___y_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v_a_2725_; lean_object* v___x_2727_; 
v_a_2725_ = lean_ctor_get(v_a_2721_, 0);
lean_inc(v_a_2725_);
lean_dec(v_a_2721_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v_a_2725_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
v_a_2730_ = lean_ctor_get(v___y_2720_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___y_2720_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___y_2720_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___y_2720_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_2708_ = stack[0].m_obj;
lean_object* v_config_2709_ = stack[1].m_obj;
lean_object* v_item_2710_ = stack[2].m_obj;
uint8_t v_logExceptions_2711_ = stack[3].m_num;
lean_object* v_a_2712_ = stack[4].m_obj;
lean_object* v_a_2713_ = stack[5].m_obj;
lean_object* v_a_2714_ = stack[6].m_obj;
lean_object* v_a_2715_ = stack[7].m_obj;
lean_object* v_a_2716_ = stack[8].m_obj;
lean_object* v_a_2717_ = stack[9].m_obj;
lean_object* v_res_2761_;
v_res_2761_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2708_, v_config_2709_, v_item_2710_, v_logExceptions_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
stack->m_obj
 = v_res_2761_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object* v_eval_2762_, lean_object* v_config_2763_, lean_object* v_item_2764_, lean_object* v_logExceptions_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
uint8_t v_logExceptions_boxed_2773_; lean_object* v_res_2774_; 
v_logExceptions_boxed_2773_ = lean_unbox(v_logExceptions_2765_);
v_res_2774_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2762_, v_config_2763_, v_item_2764_, v_logExceptions_boxed_2773_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2774_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object* v_00_u03b1_2775_, lean_object* v_eval_2776_, lean_object* v_config_2777_, lean_object* v_item_2778_, uint8_t v_logExceptions_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2776_, v_config_2777_, v_item_2778_, v_logExceptions_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
return v___x_2787_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_trySet_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_2776_ = stack[1].m_obj;
lean_object* v_config_2777_ = stack[2].m_obj;
lean_object* v_item_2778_ = stack[3].m_obj;
uint8_t v_logExceptions_2779_ = stack[4].m_num;
lean_object* v_a_2780_ = stack[5].m_obj;
lean_object* v_a_2781_ = stack[6].m_obj;
lean_object* v_a_2782_ = stack[7].m_obj;
lean_object* v_a_2783_ = stack[8].m_obj;
lean_object* v_a_2784_ = stack[9].m_obj;
lean_object* v_a_2785_ = stack[10].m_obj;
lean_object* v_res_2788_;
v_res_2788_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_box(0), v_eval_2776_, v_config_2777_, v_item_2778_, v_logExceptions_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
stack->m_obj
 = v_res_2788_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_eval_2790_, lean_object* v_config_2791_, lean_object* v_item_2792_, lean_object* v_logExceptions_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
uint8_t v_logExceptions_boxed_2801_; lean_object* v_res_2802_; 
v_logExceptions_boxed_2801_ = lean_unbox(v_logExceptions_2793_);
v_res_2802_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(v_00_u03b1_2789_, v_eval_2790_, v_config_2791_, v_item_2792_, v_logExceptions_boxed_2801_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
return v_res_2802_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object* v_ref_2803_, lean_object* v_msgData_2804_, uint8_t v_severity_2805_, uint8_t v_isSilent_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2803_, v_msgData_2804_, v_severity_2805_, v_isSilent_2806_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2803_ = stack[0].m_obj;
lean_object* v_msgData_2804_ = stack[1].m_obj;
uint8_t v_severity_2805_ = stack[2].m_num;
uint8_t v_isSilent_2806_ = stack[3].m_num;
lean_object* v___y_2807_ = stack[4].m_obj;
lean_object* v___y_2808_ = stack[5].m_obj;
lean_object* v___y_2809_ = stack[6].m_obj;
lean_object* v___y_2810_ = stack[7].m_obj;
lean_object* v___y_2811_ = stack[8].m_obj;
lean_object* v___y_2812_ = stack[9].m_obj;
lean_object* v_res_2815_;
v_res_2815_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2803_, v_msgData_2804_, v_severity_2805_, v_isSilent_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
stack->m_obj
 = v_res_2815_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2816_, lean_object* v_msgData_2817_, lean_object* v_severity_2818_, lean_object* v_isSilent_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
uint8_t v_severity_boxed_2827_; uint8_t v_isSilent_boxed_2828_; lean_object* v_res_2829_; 
v_severity_boxed_2827_ = lean_unbox(v_severity_2818_);
v_isSilent_boxed_2828_ = lean_unbox(v_isSilent_2819_);
v_res_2829_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2816_, v_msgData_2817_, v_severity_boxed_2827_, v_isSilent_boxed_2828_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_ref_2816_);
return v_res_2829_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = lean_box(0);
v___x_2831_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v___x_2830_);
return v___x_2832_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg(){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2836_;
v_res_2836_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
stack->m_obj
 = v_res_2836_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v_res_2838_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object* v_00_u03b1_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2847_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2840_ = stack[1].m_obj;
lean_object* v___y_2841_ = stack[2].m_obj;
lean_object* v___y_2842_ = stack[3].m_obj;
lean_object* v___y_2843_ = stack[4].m_obj;
lean_object* v___y_2844_ = stack[5].m_obj;
lean_object* v___y_2845_ = stack[6].m_obj;
lean_object* v_res_2848_;
v_res_2848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_box(0), v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
stack->m_obj
 = v_res_2848_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object* v_00_u03b1_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
return v_res_2857_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = l_Lean_Level_ofNat(v___x_2861_);
return v___x_2862_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2);
v___x_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
lean_ctor_set(v___x_2865_, 1, v___x_2863_);
return v___x_2865_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2866_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3);
v___x_2867_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1));
v___x_2868_ = l_Lean_Expr_const___override(v___x_2867_, v___x_2866_);
return v___x_2868_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_box(0);
v___x_2873_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6));
v___x_2874_ = l_Lean_Expr_const___override(v___x_2873_, v___x_2872_);
return v___x_2874_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object* v_cfg_2878_, lean_object* v_cfgItem_2879_, lean_object* v_cfgType_x3f_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; 
if (lean_obj_tag(v_cfgType_x3f_2880_) == 1)
{
lean_object* v_val_2898_; lean_object* v___x_2899_; lean_object* v_infoState_2900_; uint8_t v_enabled_2901_; 
v_val_2898_ = lean_ctor_get(v_cfgType_x3f_2880_, 0);
lean_inc(v_val_2898_);
lean_dec_ref_known(v_cfgType_x3f_2880_, 1);
v___x_2899_ = lean_st_ref_get(v_a_2886_);
v_infoState_2900_ = lean_ctor_get(v___x_2899_, 8);
lean_inc_ref(v_infoState_2900_);
lean_dec(v___x_2899_);
v_enabled_2901_ = lean_ctor_get_uint8(v_infoState_2900_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2900_);
if (v_enabled_2901_ == 0)
{
lean_dec(v_val_2898_);
v___y_2889_ = v_a_2881_;
v___y_2890_ = v_a_2882_;
v___y_2891_ = v_a_2883_;
v___y_2892_ = v_a_2884_;
v___y_2893_ = v_a_2885_;
v___y_2894_ = v_a_2886_;
goto v___jp_2888_;
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___y_2905_; uint8_t v___x_2917_; 
v___x_2902_ = lean_unsigned_to_nat(0u);
v___x_2903_ = l_Lean_Syntax_getArg(v_cfgItem_2879_, v___x_2902_);
v___x_2917_ = l_Lean_Syntax_isAtom(v___x_2903_);
if (v___x_2917_ == 0)
{
v___y_2905_ = v___x_2917_;
goto v___jp_2904_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2918_ = lean_unsigned_to_nat(1u);
v___x_2919_ = l_Lean_Syntax_getArg(v_cfgItem_2879_, v___x_2918_);
v___x_2920_ = l_Lean_Syntax_isMissing(v___x_2919_);
lean_dec(v___x_2919_);
v___y_2905_ = v___x_2920_;
goto v___jp_2904_;
}
v___jp_2904_:
{
if (v___y_2905_ == 0)
{
lean_dec(v___x_2903_);
lean_dec(v_val_2898_);
v___y_2889_ = v_a_2881_;
v___y_2890_ = v_a_2882_;
v___y_2891_ = v_a_2883_;
v___y_2892_ = v_a_2884_;
v___y_2893_ = v_a_2885_;
v___y_2894_ = v_a_2886_;
goto v___jp_2888_;
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2906_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
v___x_2907_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
v___x_2908_ = l_Lean_mkAppB(v___x_2906_, v_val_2898_, v___x_2907_);
v___x_2909_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9));
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2903_);
v___x_2911_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2912_ = lean_box(0);
v___x_2913_ = 0;
v___x_2914_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2914_, 0, v___x_2910_);
lean_ctor_set(v___x_2914_, 1, v___x_2911_);
lean_ctor_set(v___x_2914_, 2, v___x_2912_);
lean_ctor_set(v___x_2914_, 3, v___x_2908_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*4, v___x_2913_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*4 + 1, v___x_2913_);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v___x_2912_);
v___x_2916_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2915_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec_ref(v___x_2916_);
v___y_2889_ = v_a_2881_;
v___y_2890_ = v_a_2882_;
v___y_2891_ = v_a_2883_;
v___y_2892_ = v_a_2884_;
v___y_2893_ = v_a_2885_;
v___y_2894_ = v_a_2886_;
goto v___jp_2888_;
}
}
}
}
else
{
lean_dec(v_cfgType_x3f_2880_);
v___y_2889_ = v_a_2881_;
v___y_2890_ = v_a_2882_;
v___y_2891_ = v_a_2883_;
v___y_2892_ = v_a_2884_;
v___y_2893_ = v_a_2885_;
v___y_2894_ = v_a_2886_;
goto v___jp_2888_;
}
v___jp_2888_:
{
uint8_t v___x_2895_; 
v___x_2895_ = l_Lean_Syntax_hasMissing(v_cfgItem_2879_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v_cfg_2878_);
v___x_2896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_cfg_2878_);
return v___x_2897_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2878_ = stack[0].m_obj;
lean_object* v_cfgItem_2879_ = stack[1].m_obj;
lean_object* v_cfgType_x3f_2880_ = stack[2].m_obj;
lean_object* v_a_2881_ = stack[3].m_obj;
lean_object* v_a_2882_ = stack[4].m_obj;
lean_object* v_a_2883_ = stack[5].m_obj;
lean_object* v_a_2884_ = stack[6].m_obj;
lean_object* v_a_2885_ = stack[7].m_obj;
lean_object* v_a_2886_ = stack[8].m_obj;
lean_object* v_res_2921_;
v_res_2921_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2878_, v_cfgItem_2879_, v_cfgType_x3f_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
stack->m_obj
 = v_res_2921_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object* v_cfg_2922_, lean_object* v_cfgItem_2923_, lean_object* v_cfgType_x3f_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2922_, v_cfgItem_2923_, v_cfgType_x3f_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_cfgItem_2923_);
return v_res_2932_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object* v_00_u03b1_2933_, lean_object* v_cfg_2934_, lean_object* v_cfgItem_2935_, lean_object* v_cfgType_x3f_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2934_, v_cfgItem_2935_, v_cfgType_x3f_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2934_ = stack[1].m_obj;
lean_object* v_cfgItem_2935_ = stack[2].m_obj;
lean_object* v_cfgType_x3f_2936_ = stack[3].m_obj;
lean_object* v_a_2937_ = stack[4].m_obj;
lean_object* v_a_2938_ = stack[5].m_obj;
lean_object* v_a_2939_ = stack[6].m_obj;
lean_object* v_a_2940_ = stack[7].m_obj;
lean_object* v_a_2941_ = stack[8].m_obj;
lean_object* v_a_2942_ = stack[9].m_obj;
lean_object* v_res_2945_;
v_res_2945_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_box(0), v_cfg_2934_, v_cfgItem_2935_, v_cfgType_x3f_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
stack->m_obj
 = v_res_2945_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object* v_00_u03b1_2946_, lean_object* v_cfg_2947_, lean_object* v_cfgItem_2948_, lean_object* v_cfgType_x3f_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(v_00_u03b1_2946_, v_cfg_2947_, v_cfgItem_2948_, v_cfgType_x3f_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_cfgItem_2948_);
return v_res_2957_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_s_2958_, lean_object* v_a_2959_, uint8_t v_b_2960_){
_start:
{
lean_object* v_str_2961_; lean_object* v_startInclusive_2962_; lean_object* v_endExclusive_2963_; lean_object* v___x_2964_; uint8_t v_decide_2965_; 
v_str_2961_ = lean_ctor_get(v_s_2958_, 0);
v_startInclusive_2962_ = lean_ctor_get(v_s_2958_, 1);
v_endExclusive_2963_ = lean_ctor_get(v_s_2958_, 2);
v___x_2964_ = lean_nat_sub(v_endExclusive_2963_, v_startInclusive_2962_);
v_decide_2965_ = lean_nat_dec_eq(v_a_2959_, v___x_2964_);
lean_dec(v___x_2964_);
if (v_decide_2965_ == 0)
{
lean_object* v___x_2966_; uint32_t v___x_2967_; uint32_t v___x_2968_; uint8_t v___x_2969_; 
v___x_2966_ = lean_nat_add(v_startInclusive_2962_, v_a_2959_);
lean_dec(v_a_2959_);
v___x_2967_ = lean_string_utf8_get_fast(v_str_2961_, v___x_2966_);
v___x_2968_ = 46;
v___x_2969_ = lean_uint32_dec_eq(v___x_2967_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_string_utf8_next_fast(v_str_2961_, v___x_2966_);
lean_dec(v___x_2966_);
v___x_2971_ = lean_nat_sub(v___x_2970_, v_startInclusive_2962_);
v_a_2959_ = v___x_2971_;
v_b_2960_ = v___x_2969_;
goto _start;
}
else
{
lean_dec(v___x_2966_);
return v___x_2969_;
}
}
else
{
lean_dec(v_a_2959_);
return v_b_2960_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2958_ = stack[0].m_obj;
lean_object* v_a_2959_ = stack[1].m_obj;
uint8_t v_b_2960_ = stack[2].m_num;
uint8_t v_res_2973_;
v_res_2973_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2958_, v_a_2959_, v_b_2960_);
stack->m_num = v_res_2973_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_s_2974_, lean_object* v_a_2975_, lean_object* v_b_2976_){
_start:
{
uint8_t v_b_boxed_2977_; uint8_t v_res_2978_; lean_object* v_r_2979_; 
v_b_boxed_2977_ = lean_unbox(v_b_2976_);
v_res_2978_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2974_, v_a_2975_, v_b_boxed_2977_);
lean_dec_ref(v_s_2974_);
v_r_2979_ = lean_box(v_res_2978_);
return v_r_2979_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object* v_s_2980_){
_start:
{
lean_object* v_searcher_2981_; uint8_t v___x_2982_; uint8_t v___x_2983_; 
v_searcher_2981_ = lean_unsigned_to_nat(0u);
v___x_2982_ = 0;
v___x_2983_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2980_, v_searcher_2981_, v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2980_ = stack[0].m_obj;
uint8_t v_res_2984_;
v_res_2984_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2980_);
stack->m_num = v_res_2984_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object* v_s_2985_){
_start:
{
uint8_t v_res_2986_; lean_object* v_r_2987_; 
v_res_2986_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2985_);
lean_dec_ref(v_s_2985_);
v_r_2987_ = lean_box(v_res_2986_);
return v_r_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object* v_si_2988_, lean_object* v_val_2989_){
_start:
{
lean_object* v___y_2991_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_string_utf8_byte_size(v_val_2989_);
lean_inc_ref(v_val_2989_);
v___x_2999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2999_, 0, v_val_2989_);
lean_ctor_set(v___x_2999_, 1, v___x_2997_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
v___x_3000_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_2999_);
lean_dec_ref_known(v___x_2999_, 3);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_box(0);
lean_inc_ref(v_val_2989_);
v___x_3002_ = l_Lean_Name_str___override(v___x_3001_, v_val_2989_);
v___y_2991_ = v___x_3002_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3003_; 
lean_inc_ref(v_val_2989_);
v___x_3003_ = l_String_toName(v_val_2989_);
v___y_2991_ = v___x_3003_;
goto v___jp_2990_;
}
v___jp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2992_ = lean_unsigned_to_nat(0u);
v___x_2993_ = lean_string_utf8_byte_size(v_val_2989_);
v___x_2994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2994_, 0, v_val_2989_);
lean_ctor_set(v___x_2994_, 1, v___x_2992_);
lean_ctor_set(v___x_2994_, 2, v___x_2993_);
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2996_, 0, v_si_2988_);
lean_ctor_set(v___x_2996_, 1, v___x_2994_);
lean_ctor_set(v___x_2996_, 2, v___y_2991_);
lean_ctor_set(v___x_2996_, 3, v___x_2995_);
return v___x_2996_;
}
}
}
lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object* v_eval_3005_, uint8_t v_logExceptions_3006_, lean_object* v_onErr_3007_, lean_object* v_init_3008_, lean_object* v_cfg_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_3009_);
v___x_3039_ = l_Lean_Syntax_isOfKind(v_cfg_3009_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3040_ = l_Lean_Syntax_getNumArgs(v_cfg_3009_);
v___x_3041_ = lean_unsigned_to_nat(1u);
v___x_3042_ = lean_nat_dec_eq(v___x_3040_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_object* v_atomAsIdent_3043_; uint8_t v___x_3044_; 
v_atomAsIdent_3043_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0));
v___x_3044_ = lean_nat_dec_le(v___x_3041_, v___x_3040_);
if (v___x_3044_ == 0)
{
lean_dec(v___x_3040_);
if (lean_obj_tag(v_cfg_3009_) == 2)
{
lean_object* v_info_3045_; lean_object* v_val_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_dec_ref(v_onErr_3007_);
v_info_3045_ = lean_ctor_get(v_cfg_3009_, 0);
v_val_3046_ = lean_ctor_get(v_cfg_3009_, 1);
lean_inc_ref(v_val_3046_);
lean_inc(v_info_3045_);
v___x_3047_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_3045_, v_val_3046_);
v___x_3048_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_3049_ = l_Lean_mkCIdentFrom(v_cfg_3009_, v___x_3048_, v___x_3044_);
v___x_3050_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_3051_ = l_Lean_TSyntax_getId(v___x_3047_);
v___x_3052_ = l_Lean_Name_eraseMacroScopes(v___x_3051_);
lean_dec(v___x_3051_);
v___x_3053_ = lean_box(0);
lean_inc(v___x_3047_);
v___x_3054_ = l_Lean_Syntax_identComponents(v___x_3047_, v___x_3053_);
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3056_, 0, v_cfg_3009_);
lean_ctor_set(v___x_3056_, 1, v___x_3047_);
lean_ctor_set(v___x_3056_, 2, v___x_3049_);
lean_ctor_set(v___x_3056_, 3, v___x_3050_);
lean_ctor_set(v___x_3056_, 4, v___x_3052_);
lean_ctor_set(v___x_3056_, 5, v___x_3054_);
lean_ctor_set(v___x_3056_, 6, v___x_3055_);
v___x_3057_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3005_, v_init_3008_, v___x_3056_, v_logExceptions_3006_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3057_;
}
else
{
lean_dec_ref(v_eval_3005_);
goto v___jp_3028_;
}
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = l_Lean_Syntax_getArg(v_cfg_3009_, v___x_3058_);
if (lean_obj_tag(v___x_3059_) == 2)
{
lean_object* v_val_3060_; lean_object* v___y_3062_; uint8_t v_val_3063_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_val_3060_ = lean_ctor_get(v___x_3059_, 1);
v___x_3074_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_3075_ = lean_string_dec_eq(v_val_3060_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_3077_ = lean_string_dec_eq(v_val_3060_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; uint8_t v___x_3079_; 
lean_inc_ref(v_val_3060_);
lean_dec_ref_known(v___x_3059_, 2);
v___x_3078_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_3079_ = lean_string_dec_eq(v_val_3060_, v___x_3078_);
lean_dec_ref(v_val_3060_);
if (v___x_3079_ == 0)
{
lean_dec(v___x_3040_);
lean_dec_ref(v_eval_3005_);
goto v___jp_3028_;
}
else
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = lean_unsigned_to_nat(5u);
v___x_3081_ = lean_nat_dec_le(v___x_3040_, v___x_3080_);
lean_dec(v___x_3040_);
if (v___x_3081_ == 0)
{
lean_dec_ref(v_eval_3005_);
goto v___jp_3028_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = l_Lean_Syntax_getArg(v_cfg_3009_, v___x_3041_);
v___x_3083_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_3043_, v___x_3082_);
if (lean_obj_tag(v___x_3083_) == 1)
{
lean_object* v_val_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec_ref(v_onErr_3007_);
v_val_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc_n(v_val_3084_, 2);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = lean_unsigned_to_nat(3u);
v___x_3086_ = l_Lean_Syntax_getArg(v_cfg_3009_, v___x_3085_);
v___x_3087_ = lean_box(0);
v___x_3088_ = l_Lean_TSyntax_getId(v_val_3084_);
v___x_3089_ = l_Lean_Name_eraseMacroScopes(v___x_3088_);
lean_dec(v___x_3088_);
v___x_3090_ = l_Lean_Syntax_identComponents(v_val_3084_, v___x_3087_);
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3092_, 0, v_cfg_3009_);
lean_ctor_set(v___x_3092_, 1, v_val_3084_);
lean_ctor_set(v___x_3092_, 2, v___x_3086_);
lean_ctor_set(v___x_3092_, 3, v___x_3087_);
lean_ctor_set(v___x_3092_, 4, v___x_3089_);
lean_ctor_set(v___x_3092_, 5, v___x_3090_);
lean_ctor_set(v___x_3092_, 6, v___x_3091_);
v___x_3093_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3005_, v_init_3008_, v___x_3092_, v_logExceptions_3006_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3093_;
}
else
{
lean_dec(v___x_3083_);
lean_dec_ref(v_eval_3005_);
goto v___jp_3028_;
}
}
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_box(v___x_3075_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
v___y_3062_ = v___x_3095_;
v_val_3063_ = v___x_3075_;
goto v___jp_3061_;
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_box(v___x_3044_);
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
v___y_3062_ = v___x_3097_;
v_val_3063_ = v___x_3044_;
goto v___jp_3061_;
}
v___jp_3061_:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = lean_unsigned_to_nat(2u);
v___x_3065_ = lean_nat_dec_eq(v___x_3040_, v___x_3064_);
lean_dec(v___x_3040_);
if (v___x_3065_ == 0)
{
lean_dec(v___y_3062_);
lean_dec_ref_known(v___x_3059_, 2);
lean_dec_ref(v_eval_3005_);
goto v___jp_3028_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = l_Lean_Syntax_getArg(v_cfg_3009_, v___x_3041_);
v___x_3067_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_3043_, v___x_3066_);
if (lean_obj_tag(v___x_3067_) == 1)
{
lean_dec_ref(v_onErr_3007_);
if (v_val_3063_ == 0)
{
lean_object* v_val_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_3070_ = l_Lean_mkCIdentFrom(v___x_3059_, v___x_3069_, v_val_3063_);
lean_dec_ref_known(v___x_3059_, 2);
v___y_3018_ = v_val_3068_;
v___y_3019_ = v___y_3062_;
v___y_3020_ = v___x_3070_;
goto v___jp_3017_;
}
else
{
lean_object* v_val_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_val_3071_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3071_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3072_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_3073_ = l_Lean_mkCIdentFrom(v___x_3059_, v___x_3072_, v___x_3042_);
lean_dec_ref_known(v___x_3059_, 2);
v___y_3018_ = v_val_3071_;
v___y_3019_ = v___y_3062_;
v___y_3020_ = v___x_3073_;
goto v___jp_3017_;
}
}
else
{
lean_dec(v___x_3067_);
lean_dec(v___y_3062_);
lean_dec_ref_known(v___x_3059_, 2);
lean_dec_ref(v_eval_3005_);
goto v___jp_3028_;
}
}
}
}
else
{
lean_dec(v___x_3059_);
lean_dec(v___x_3040_);
lean_dec_ref(v_eval_3005_);
goto v___jp_3028_;
}
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec(v___x_3040_);
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = l_Lean_Syntax_getArg(v_cfg_3009_, v___x_3098_);
lean_dec(v_cfg_3009_);
v_cfg_3009_ = v___x_3099_;
goto _start;
}
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = l_Lean_Syntax_getArgs(v_cfg_3009_);
lean_dec(v_cfg_3009_);
v___x_3102_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3005_, v_logExceptions_3006_, v_onErr_3007_, v_init_3008_, v___x_3101_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
lean_dec_ref(v___x_3101_);
return v___x_3102_;
}
v___jp_3017_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3021_ = l_Lean_TSyntax_getId(v___y_3018_);
v___x_3022_ = l_Lean_Name_eraseMacroScopes(v___x_3021_);
lean_dec(v___x_3021_);
v___x_3023_ = lean_box(0);
lean_inc(v___y_3018_);
v___x_3024_ = l_Lean_Syntax_identComponents(v___y_3018_, v___x_3023_);
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3026_, 0, v_cfg_3009_);
lean_ctor_set(v___x_3026_, 1, v___y_3018_);
lean_ctor_set(v___x_3026_, 2, v___y_3020_);
lean_ctor_set(v___x_3026_, 3, v___y_3019_);
lean_ctor_set(v___x_3026_, 4, v___x_3022_);
lean_ctor_set(v___x_3026_, 5, v___x_3024_);
lean_ctor_set(v___x_3026_, 6, v___x_3025_);
v___x_3027_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3005_, v_init_3008_, v___x_3026_, v_logExceptions_3006_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3027_;
}
v___jp_3028_:
{
lean_object* v_toCold_3029_; lean_object* v_currRecDepth_3030_; lean_object* v_ref_3031_; uint16_t v_optionFlags_3032_; uint8_t v_suppressElabErrors_3033_; uint8_t v_isRecordingDeps_3034_; lean_object* v_ref_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_toCold_3029_ = lean_ctor_get(v___y_3014_, 0);
v_currRecDepth_3030_ = lean_ctor_get(v___y_3014_, 1);
v_ref_3031_ = lean_ctor_get(v___y_3014_, 2);
v_optionFlags_3032_ = lean_ctor_get_uint16(v___y_3014_, sizeof(void*)*3);
v_suppressElabErrors_3033_ = lean_ctor_get_uint8(v___y_3014_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3034_ = lean_ctor_get_uint8(v___y_3014_, sizeof(void*)*3 + 3);
v_ref_3035_ = l_Lean_replaceRef(v_cfg_3009_, v_ref_3031_);
lean_inc(v_currRecDepth_3030_);
lean_inc_ref(v_toCold_3029_);
v___x_3036_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3036_, 0, v_toCold_3029_);
lean_ctor_set(v___x_3036_, 1, v_currRecDepth_3030_);
lean_ctor_set(v___x_3036_, 2, v_ref_3035_);
lean_ctor_set_uint16(v___x_3036_, sizeof(void*)*3, v_optionFlags_3032_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*3 + 2, v_suppressElabErrors_3033_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*3 + 3, v_isRecordingDeps_3034_);
lean_inc(v___y_3015_);
lean_inc(v___y_3013_);
lean_inc_ref(v___y_3012_);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
v___x_3037_ = lean_apply_9(v_onErr_3007_, v_init_3008_, v_cfg_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___x_3036_, v___y_3015_, lean_box(0));
return v___x_3037_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3005_ = stack[0].m_obj;
uint8_t v_logExceptions_3006_ = stack[1].m_num;
lean_object* v_onErr_3007_ = stack[2].m_obj;
lean_object* v_init_3008_ = stack[3].m_obj;
lean_object* v_cfg_3009_ = stack[4].m_obj;
lean_object* v___y_3010_ = stack[5].m_obj;
lean_object* v___y_3011_ = stack[6].m_obj;
lean_object* v___y_3012_ = stack[7].m_obj;
lean_object* v___y_3013_ = stack[8].m_obj;
lean_object* v___y_3014_ = stack[9].m_obj;
lean_object* v___y_3015_ = stack[10].m_obj;
lean_object* v_res_3103_;
v_res_3103_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3005_, v_logExceptions_3006_, v_onErr_3007_, v_init_3008_, v_cfg_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
stack->m_obj
 = v_res_3103_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object* v_eval_3104_, uint8_t v_logExceptions_3105_, lean_object* v_onErr_3106_, lean_object* v_as_3107_, size_t v_i_3108_, size_t v_stop_3109_, lean_object* v_b_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
uint8_t v___x_3118_; 
v___x_3118_ = lean_usize_dec_eq(v_i_3108_, v_stop_3109_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_array_uget_borrowed(v_as_3107_, v_i_3108_);
lean_inc(v___x_3119_);
lean_inc_ref(v_onErr_3106_);
lean_inc_ref(v_eval_3104_);
v___x_3120_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3104_, v_logExceptions_3105_, v_onErr_3106_, v_b_3110_, v___x_3119_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; size_t v___x_3122_; size_t v___x_3123_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = ((size_t)1ULL);
v___x_3123_ = lean_usize_add(v_i_3108_, v___x_3122_);
v_i_3108_ = v___x_3123_;
v_b_3110_ = v_a_3121_;
goto _start;
}
else
{
lean_dec_ref(v_onErr_3106_);
lean_dec_ref(v_eval_3104_);
return v___x_3120_;
}
}
else
{
lean_object* v___x_3125_; 
lean_dec_ref(v_onErr_3106_);
lean_dec_ref(v_eval_3104_);
v___x_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_b_3110_);
return v___x_3125_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3104_ = stack[0].m_obj;
uint8_t v_logExceptions_3105_ = stack[1].m_num;
lean_object* v_onErr_3106_ = stack[2].m_obj;
lean_object* v_as_3107_ = stack[3].m_obj;
size_t v_i_3108_ = stack[4].m_num;
size_t v_stop_3109_ = stack[5].m_num;
lean_object* v_b_3110_ = stack[6].m_obj;
lean_object* v___y_3111_ = stack[7].m_obj;
lean_object* v___y_3112_ = stack[8].m_obj;
lean_object* v___y_3113_ = stack[9].m_obj;
lean_object* v___y_3114_ = stack[10].m_obj;
lean_object* v___y_3115_ = stack[11].m_obj;
lean_object* v___y_3116_ = stack[12].m_obj;
lean_object* v_res_3126_;
v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3104_, v_logExceptions_3105_, v_onErr_3106_, v_as_3107_, v_i_3108_, v_stop_3109_, v_b_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
stack->m_obj
 = v_res_3126_;
}
lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object* v_eval_3127_, uint8_t v_logExceptions_3128_, lean_object* v_onErr_3129_, lean_object* v_init_3130_, lean_object* v_cfgs_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3139_ = lean_unsigned_to_nat(0u);
v___x_3140_ = lean_array_get_size(v_cfgs_3131_);
v___x_3141_ = lean_nat_dec_lt(v___x_3139_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
lean_dec_ref(v_onErr_3129_);
lean_dec_ref(v_eval_3127_);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_init_3130_);
return v___x_3142_;
}
else
{
size_t v___x_3143_; size_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = ((size_t)0ULL);
v___x_3144_ = lean_usize_of_nat(v___x_3140_);
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3127_, v_logExceptions_3128_, v_onErr_3129_, v_cfgs_3131_, v___x_3143_, v___x_3144_, v_init_3130_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
return v___x_3145_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3127_ = stack[0].m_obj;
uint8_t v_logExceptions_3128_ = stack[1].m_num;
lean_object* v_onErr_3129_ = stack[2].m_obj;
lean_object* v_init_3130_ = stack[3].m_obj;
lean_object* v_cfgs_3131_ = stack[4].m_obj;
lean_object* v___y_3132_ = stack[5].m_obj;
lean_object* v___y_3133_ = stack[6].m_obj;
lean_object* v___y_3134_ = stack[7].m_obj;
lean_object* v___y_3135_ = stack[8].m_obj;
lean_object* v___y_3136_ = stack[9].m_obj;
lean_object* v___y_3137_ = stack[10].m_obj;
lean_object* v_res_3146_;
v_res_3146_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3127_, v_logExceptions_3128_, v_onErr_3129_, v_init_3130_, v_cfgs_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
stack->m_obj
 = v_res_3146_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object* v_eval_3147_, lean_object* v_logExceptions_3148_, lean_object* v_onErr_3149_, lean_object* v_init_3150_, lean_object* v_cfgs_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
uint8_t v_logExceptions_boxed_3159_; lean_object* v_res_3160_; 
v_logExceptions_boxed_3159_ = lean_unbox(v_logExceptions_3148_);
v_res_3160_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3147_, v_logExceptions_boxed_3159_, v_onErr_3149_, v_init_3150_, v_cfgs_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v_cfgs_3151_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_eval_3161_, lean_object* v_logExceptions_3162_, lean_object* v_onErr_3163_, lean_object* v_as_3164_, lean_object* v_i_3165_, lean_object* v_stop_3166_, lean_object* v_b_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
uint8_t v_logExceptions_boxed_3175_; size_t v_i_boxed_3176_; size_t v_stop_boxed_3177_; lean_object* v_res_3178_; 
v_logExceptions_boxed_3175_ = lean_unbox(v_logExceptions_3162_);
v_i_boxed_3176_ = lean_unbox_usize(v_i_3165_);
lean_dec(v_i_3165_);
v_stop_boxed_3177_ = lean_unbox_usize(v_stop_3166_);
lean_dec(v_stop_3166_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3161_, v_logExceptions_boxed_3175_, v_onErr_3163_, v_as_3164_, v_i_boxed_3176_, v_stop_boxed_3177_, v_b_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v_as_3164_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object* v_eval_3179_, lean_object* v_logExceptions_3180_, lean_object* v_onErr_3181_, lean_object* v_init_3182_, lean_object* v_cfg_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
uint8_t v_logExceptions_boxed_3191_; lean_object* v_res_3192_; 
v_logExceptions_boxed_3191_ = lean_unbox(v_logExceptions_3180_);
v_res_3192_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3179_, v_logExceptions_boxed_3191_, v_onErr_3181_, v_init_3182_, v_cfg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3192_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object* v_eval_3193_, lean_object* v_init_3194_, lean_object* v_cfg_3195_, lean_object* v_onErr_3196_, uint8_t v_logExceptions_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3193_, v_logExceptions_3197_, v_onErr_3196_, v_init_3194_, v_cfg_3195_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3193_ = stack[0].m_obj;
lean_object* v_init_3194_ = stack[1].m_obj;
lean_object* v_cfg_3195_ = stack[2].m_obj;
lean_object* v_onErr_3196_ = stack[3].m_obj;
uint8_t v_logExceptions_3197_ = stack[4].m_num;
lean_object* v_a_3198_ = stack[5].m_obj;
lean_object* v_a_3199_ = stack[6].m_obj;
lean_object* v_a_3200_ = stack[7].m_obj;
lean_object* v_a_3201_ = stack[8].m_obj;
lean_object* v_a_3202_ = stack[9].m_obj;
lean_object* v_a_3203_ = stack[10].m_obj;
lean_object* v_res_3206_;
v_res_3206_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3193_, v_init_3194_, v_cfg_3195_, v_onErr_3196_, v_logExceptions_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
stack->m_obj
 = v_res_3206_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object* v_eval_3207_, lean_object* v_init_3208_, lean_object* v_cfg_3209_, lean_object* v_onErr_3210_, lean_object* v_logExceptions_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_){
_start:
{
uint8_t v_logExceptions_boxed_3219_; lean_object* v_res_3220_; 
v_logExceptions_boxed_3219_ = lean_unbox(v_logExceptions_3211_);
v_res_3220_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3207_, v_init_3208_, v_cfg_3209_, v_onErr_3210_, v_logExceptions_boxed_3219_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
return v_res_3220_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object* v_00_u03b1_3221_, lean_object* v_eval_3222_, lean_object* v_init_3223_, lean_object* v_cfg_3224_, lean_object* v_onErr_3225_, uint8_t v_logExceptions_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3222_, v_logExceptions_3226_, v_onErr_3225_, v_init_3223_, v_cfg_3224_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3222_ = stack[1].m_obj;
lean_object* v_init_3223_ = stack[2].m_obj;
lean_object* v_cfg_3224_ = stack[3].m_obj;
lean_object* v_onErr_3225_ = stack[4].m_obj;
uint8_t v_logExceptions_3226_ = stack[5].m_num;
lean_object* v_a_3227_ = stack[6].m_obj;
lean_object* v_a_3228_ = stack[7].m_obj;
lean_object* v_a_3229_ = stack[8].m_obj;
lean_object* v_a_3230_ = stack[9].m_obj;
lean_object* v_a_3231_ = stack[10].m_obj;
lean_object* v_a_3232_ = stack[11].m_obj;
lean_object* v_res_3235_;
v_res_3235_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_box(0), v_eval_3222_, v_init_3223_, v_cfg_3224_, v_onErr_3225_, v_logExceptions_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
stack->m_obj
 = v_res_3235_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object* v_00_u03b1_3236_, lean_object* v_eval_3237_, lean_object* v_init_3238_, lean_object* v_cfg_3239_, lean_object* v_onErr_3240_, lean_object* v_logExceptions_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_){
_start:
{
uint8_t v_logExceptions_boxed_3249_; lean_object* v_res_3250_; 
v_logExceptions_boxed_3249_ = lean_unbox(v_logExceptions_3241_);
v_res_3250_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(v_00_u03b1_3236_, v_eval_3237_, v_init_3238_, v_cfg_3239_, v_onErr_3240_, v_logExceptions_boxed_3249_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
return v_res_3250_;
}
}
lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object* v_00_u03b1_3251_, lean_object* v_eval_3252_, uint8_t v_logExceptions_3253_, lean_object* v_onErr_3254_, lean_object* v_init_3255_, lean_object* v_cfg_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3252_, v_logExceptions_3253_, v_onErr_3254_, v_init_3255_, v_cfg_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3252_ = stack[1].m_obj;
uint8_t v_logExceptions_3253_ = stack[2].m_num;
lean_object* v_onErr_3254_ = stack[3].m_obj;
lean_object* v_init_3255_ = stack[4].m_obj;
lean_object* v_cfg_3256_ = stack[5].m_obj;
lean_object* v___y_3257_ = stack[6].m_obj;
lean_object* v___y_3258_ = stack[7].m_obj;
lean_object* v___y_3259_ = stack[8].m_obj;
lean_object* v___y_3260_ = stack[9].m_obj;
lean_object* v___y_3261_ = stack[10].m_obj;
lean_object* v___y_3262_ = stack[11].m_obj;
lean_object* v_res_3265_;
v_res_3265_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_box(0), v_eval_3252_, v_logExceptions_3253_, v_onErr_3254_, v_init_3255_, v_cfg_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(lean_object* v_00_u03b1_3266_, lean_object* v_eval_3267_, lean_object* v_logExceptions_3268_, lean_object* v_onErr_3269_, lean_object* v_init_3270_, lean_object* v_cfg_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v_logExceptions_boxed_3279_; lean_object* v_res_3280_; 
v_logExceptions_boxed_3279_ = lean_unbox(v_logExceptions_3268_);
v_res_3280_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_3266_, v_eval_3267_, v_logExceptions_boxed_3279_, v_onErr_3269_, v_init_3270_, v_cfg_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
return v_res_3280_;
}
}
lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object* v_00_u03b1_3281_, lean_object* v_eval_3282_, uint8_t v_logExceptions_3283_, lean_object* v_onErr_3284_, lean_object* v_init_3285_, lean_object* v_cfgs_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3282_, v_logExceptions_3283_, v_onErr_3284_, v_init_3285_, v_cfgs_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3282_ = stack[1].m_obj;
uint8_t v_logExceptions_3283_ = stack[2].m_num;
lean_object* v_onErr_3284_ = stack[3].m_obj;
lean_object* v_init_3285_ = stack[4].m_obj;
lean_object* v_cfgs_3286_ = stack[5].m_obj;
lean_object* v___y_3287_ = stack[6].m_obj;
lean_object* v___y_3288_ = stack[7].m_obj;
lean_object* v___y_3289_ = stack[8].m_obj;
lean_object* v___y_3290_ = stack[9].m_obj;
lean_object* v___y_3291_ = stack[10].m_obj;
lean_object* v___y_3292_ = stack[11].m_obj;
lean_object* v_res_3295_;
v_res_3295_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_box(0), v_eval_3282_, v_logExceptions_3283_, v_onErr_3284_, v_init_3285_, v_cfgs_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
stack->m_obj
 = v_res_3295_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3296_, lean_object* v_eval_3297_, lean_object* v_logExceptions_3298_, lean_object* v_onErr_3299_, lean_object* v_init_3300_, lean_object* v_cfgs_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
uint8_t v_logExceptions_boxed_3309_; lean_object* v_res_3310_; 
v_logExceptions_boxed_3309_ = lean_unbox(v_logExceptions_3298_);
v_res_3310_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_3296_, v_eval_3297_, v_logExceptions_boxed_3309_, v_onErr_3299_, v_init_3300_, v_cfgs_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec_ref(v_cfgs_3301_);
return v_res_3310_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object* v_s_3311_, lean_object* v_inst_3312_, lean_object* v_R_3313_, lean_object* v_a_3314_, uint8_t v_b_3315_, lean_object* v_c_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_3311_, v_a_3314_, v_b_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3311_ = stack[0].m_obj;
lean_object* v_a_3314_ = stack[3].m_obj;
uint8_t v_b_3315_ = stack[4].m_num;
uint8_t v_res_3318_;
v_res_3318_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3311_, lean_box(0), lean_box(0), v_a_3314_, v_b_3315_, lean_box(0));
stack->m_num = v_res_3318_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_s_3319_, lean_object* v_inst_3320_, lean_object* v_R_3321_, lean_object* v_a_3322_, lean_object* v_b_3323_, lean_object* v_c_3324_){
_start:
{
uint8_t v_b_boxed_3325_; uint8_t v_res_3326_; lean_object* v_r_3327_; 
v_b_boxed_3325_ = lean_unbox(v_b_3323_);
v_res_3326_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3319_, v_inst_3320_, v_R_3321_, v_a_3322_, v_b_boxed_3325_, v_c_3324_);
lean_dec_ref(v_s_3319_);
v_r_3327_ = lean_box(v_res_3326_);
return v_r_3327_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3328_, lean_object* v_eval_3329_, uint8_t v_logExceptions_3330_, lean_object* v_onErr_3331_, lean_object* v_as_3332_, size_t v_i_3333_, size_t v_stop_3334_, lean_object* v_b_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3329_, v_logExceptions_3330_, v_onErr_3331_, v_as_3332_, v_i_3333_, v_stop_3334_, v_b_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3329_ = stack[1].m_obj;
uint8_t v_logExceptions_3330_ = stack[2].m_num;
lean_object* v_onErr_3331_ = stack[3].m_obj;
lean_object* v_as_3332_ = stack[4].m_obj;
size_t v_i_3333_ = stack[5].m_num;
size_t v_stop_3334_ = stack[6].m_num;
lean_object* v_b_3335_ = stack[7].m_obj;
lean_object* v___y_3336_ = stack[8].m_obj;
lean_object* v___y_3337_ = stack[9].m_obj;
lean_object* v___y_3338_ = stack[10].m_obj;
lean_object* v___y_3339_ = stack[11].m_obj;
lean_object* v___y_3340_ = stack[12].m_obj;
lean_object* v___y_3341_ = stack[13].m_obj;
lean_object* v_res_3344_;
v_res_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_box(0), v_eval_3329_, v_logExceptions_3330_, v_onErr_3331_, v_as_3332_, v_i_3333_, v_stop_3334_, v_b_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
stack->m_obj
 = v_res_3344_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3345_, lean_object* v_eval_3346_, lean_object* v_logExceptions_3347_, lean_object* v_onErr_3348_, lean_object* v_as_3349_, lean_object* v_i_3350_, lean_object* v_stop_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
uint8_t v_logExceptions_boxed_3360_; size_t v_i_boxed_3361_; size_t v_stop_boxed_3362_; lean_object* v_res_3363_; 
v_logExceptions_boxed_3360_ = lean_unbox(v_logExceptions_3347_);
v_i_boxed_3361_ = lean_unbox_usize(v_i_3350_);
lean_dec(v_i_3350_);
v_stop_boxed_3362_ = lean_unbox_usize(v_stop_3351_);
lean_dec(v_stop_3351_);
v_res_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_3345_, v_eval_3346_, v_logExceptions_boxed_3360_, v_onErr_3348_, v_as_3349_, v_i_boxed_3361_, v_stop_boxed_3362_, v_b_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec_ref(v_as_3349_);
return v_res_3363_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object* v_eval_3364_, lean_object* v_init_3365_, lean_object* v_cfgs_3366_, lean_object* v_onErr_3367_, uint8_t v_logExceptions_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3364_, v_logExceptions_3368_, v_onErr_3367_, v_init_3365_, v_cfgs_3366_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3376_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3364_ = stack[0].m_obj;
lean_object* v_init_3365_ = stack[1].m_obj;
lean_object* v_cfgs_3366_ = stack[2].m_obj;
lean_object* v_onErr_3367_ = stack[3].m_obj;
uint8_t v_logExceptions_3368_ = stack[4].m_num;
lean_object* v_a_3369_ = stack[5].m_obj;
lean_object* v_a_3370_ = stack[6].m_obj;
lean_object* v_a_3371_ = stack[7].m_obj;
lean_object* v_a_3372_ = stack[8].m_obj;
lean_object* v_a_3373_ = stack[9].m_obj;
lean_object* v_a_3374_ = stack[10].m_obj;
lean_object* v_res_3377_;
v_res_3377_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3364_, v_init_3365_, v_cfgs_3366_, v_onErr_3367_, v_logExceptions_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
stack->m_obj
 = v_res_3377_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object* v_eval_3378_, lean_object* v_init_3379_, lean_object* v_cfgs_3380_, lean_object* v_onErr_3381_, lean_object* v_logExceptions_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
uint8_t v_logExceptions_boxed_3390_; lean_object* v_res_3391_; 
v_logExceptions_boxed_3390_ = lean_unbox(v_logExceptions_3382_);
v_res_3391_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3378_, v_init_3379_, v_cfgs_3380_, v_onErr_3381_, v_logExceptions_boxed_3390_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec_ref(v_cfgs_3380_);
return v_res_3391_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object* v_00_u03b1_3392_, lean_object* v_eval_3393_, lean_object* v_init_3394_, lean_object* v_cfgs_3395_, lean_object* v_onErr_3396_, uint8_t v_logExceptions_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3393_, v_logExceptions_3397_, v_onErr_3396_, v_init_3394_, v_cfgs_3395_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_3393_ = stack[1].m_obj;
lean_object* v_init_3394_ = stack[2].m_obj;
lean_object* v_cfgs_3395_ = stack[3].m_obj;
lean_object* v_onErr_3396_ = stack[4].m_obj;
uint8_t v_logExceptions_3397_ = stack[5].m_num;
lean_object* v_a_3398_ = stack[6].m_obj;
lean_object* v_a_3399_ = stack[7].m_obj;
lean_object* v_a_3400_ = stack[8].m_obj;
lean_object* v_a_3401_ = stack[9].m_obj;
lean_object* v_a_3402_ = stack[10].m_obj;
lean_object* v_a_3403_ = stack[11].m_obj;
lean_object* v_res_3406_;
v_res_3406_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_box(0), v_eval_3393_, v_init_3394_, v_cfgs_3395_, v_onErr_3396_, v_logExceptions_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
stack->m_obj
 = v_res_3406_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object* v_00_u03b1_3407_, lean_object* v_eval_3408_, lean_object* v_init_3409_, lean_object* v_cfgs_3410_, lean_object* v_onErr_3411_, lean_object* v_logExceptions_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
uint8_t v_logExceptions_boxed_3420_; lean_object* v_res_3421_; 
v_logExceptions_boxed_3420_ = lean_unbox(v_logExceptions_3412_);
v_res_3421_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(v_00_u03b1_3407_, v_eval_3408_, v_init_3409_, v_cfgs_3410_, v_onErr_3411_, v_logExceptions_boxed_3420_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec_ref(v_cfgs_3410_);
return v_res_3421_;
}
}
uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object* v_x_3422_){
_start:
{
uint8_t v___x_3423_; 
v___x_3423_ = 0;
return v___x_3423_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3422_ = stack[0].m_obj;
uint8_t v_res_3424_;
v_res_3424_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3422_);
stack->m_num = v_res_3424_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object* v_x_3425_){
_start:
{
uint8_t v_res_3426_; lean_object* v_r_3427_; 
v_res_3426_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3425_);
lean_dec(v_x_3425_);
v_r_3427_ = lean_box(v_res_3426_);
return v_r_3427_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(lean_object* v___x_3428_, lean_object* v_ctx_x3f_3429_, size_t v_sz_3430_, size_t v_i_3431_, lean_object* v_bs_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_usize_dec_lt(v_i_3431_, v_sz_3430_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v_ctx_x3f_3429_);
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v_bs_3432_);
return v___x_3441_;
}
else
{
lean_object* v_assignment_3442_; lean_object* v_v_3443_; lean_object* v___x_3444_; lean_object* v_bs_x27_3445_; lean_object* v_a_3447_; lean_object* v_tree_3452_; lean_object* v___x_3453_; 
v_assignment_3442_ = lean_ctor_get(v___x_3428_, 0);
v_v_3443_ = lean_array_uget(v_bs_3432_, v_i_3431_);
v___x_3444_ = lean_unsigned_to_nat(0u);
v_bs_x27_3445_ = lean_array_uset(v_bs_3432_, v_i_3431_, v___x_3444_);
v_tree_3452_ = l_Lean_Elab_InfoTree_substitute(v_v_3443_, v_assignment_3442_);
lean_inc_ref(v_ctx_x3f_3429_);
lean_inc(v___y_3438_);
lean_inc_ref(v___y_3437_);
lean_inc(v___y_3436_);
lean_inc_ref(v___y_3435_);
lean_inc(v___y_3434_);
lean_inc_ref(v___y_3433_);
v___x_3453_ = lean_apply_7(v_ctx_x3f_3429_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, lean_box(0));
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
if (lean_obj_tag(v_a_3454_) == 0)
{
v_a_3447_ = v_tree_3452_;
goto v___jp_3446_;
}
else
{
lean_object* v_val_3455_; lean_object* v___x_3456_; 
v_val_3455_ = lean_ctor_get(v_a_3454_, 0);
lean_inc(v_val_3455_);
lean_dec_ref_known(v_a_3454_, 1);
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_val_3455_);
lean_ctor_set(v___x_3456_, 1, v_tree_3452_);
v_a_3447_ = v___x_3456_;
goto v___jp_3446_;
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec_ref(v_tree_3452_);
lean_dec_ref(v_bs_x27_3445_);
lean_dec_ref(v_ctx_x3f_3429_);
v_a_3457_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3453_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3453_);
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
v___jp_3446_:
{
size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = ((size_t)1ULL);
v___x_3449_ = lean_usize_add(v_i_3431_, v___x_3448_);
v___x_3450_ = lean_array_uset(v_bs_x27_3445_, v_i_3431_, v_a_3447_);
v_i_3431_ = v___x_3449_;
v_bs_3432_ = v___x_3450_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3428_ = stack[0].m_obj;
lean_object* v_ctx_x3f_3429_ = stack[1].m_obj;
size_t v_sz_3430_ = stack[2].m_num;
size_t v_i_3431_ = stack[3].m_num;
lean_object* v_bs_3432_ = stack[4].m_obj;
lean_object* v___y_3433_ = stack[5].m_obj;
lean_object* v___y_3434_ = stack[6].m_obj;
lean_object* v___y_3435_ = stack[7].m_obj;
lean_object* v___y_3436_ = stack[8].m_obj;
lean_object* v___y_3437_ = stack[9].m_obj;
lean_object* v___y_3438_ = stack[10].m_obj;
lean_object* v_res_3465_;
v_res_3465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3428_, v_ctx_x3f_3429_, v_sz_3430_, v_i_3431_, v_bs_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
stack->m_obj
 = v_res_3465_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v___x_3466_, lean_object* v_ctx_x3f_3467_, lean_object* v_sz_3468_, lean_object* v_i_3469_, lean_object* v_bs_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3468_);
lean_dec(v_sz_3468_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3466_, v_ctx_x3f_3467_, v_sz_boxed_3478_, v_i_boxed_3479_, v_bs_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec_ref(v___x_3466_);
return v_res_3480_;
}
}
lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(lean_object* v___x_3481_, lean_object* v_ctx_x3f_3482_, lean_object* v_x_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
if (lean_obj_tag(v_x_3483_) == 0)
{
lean_object* v_cs_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3517_; 
v_cs_3491_ = lean_ctor_get(v_x_3483_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_x_3483_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3493_ = v_x_3483_;
v_isShared_3494_ = v_isSharedCheck_3517_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_cs_3491_);
lean_dec(v_x_3483_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3517_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
size_t v_sz_3495_; size_t v___x_3496_; lean_object* v___x_3497_; 
v_sz_3495_ = lean_array_size(v_cs_3491_);
v___x_3496_ = ((size_t)0ULL);
v___x_3497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3481_, v_ctx_x3f_3482_, v_sz_3495_, v___x_3496_, v_cs_3491_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3508_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3508_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3508_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_a_3498_);
v___x_3503_ = v___x_3493_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3505_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3503_);
v___x_3505_ = v___x_3500_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_del_object(v___x_3493_);
v_a_3509_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3497_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3497_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
else
{
lean_object* v_vs_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3544_; 
v_vs_3518_ = lean_ctor_get(v_x_3483_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_x_3483_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3520_ = v_x_3483_;
v_isShared_3521_ = v_isSharedCheck_3544_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_vs_3518_);
lean_dec(v_x_3483_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3544_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
size_t v_sz_3522_; size_t v___x_3523_; lean_object* v___x_3524_; 
v_sz_3522_ = lean_array_size(v_vs_3518_);
v___x_3523_ = ((size_t)0ULL);
v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3481_, v_ctx_x3f_3482_, v_sz_3522_, v___x_3523_, v_vs_3518_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3535_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3535_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3535_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v_a_3525_);
v___x_3530_ = v___x_3520_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3530_);
v___x_3532_ = v___x_3527_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_del_object(v___x_3520_);
v_a_3536_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3524_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3524_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3481_ = stack[0].m_obj;
lean_object* v_ctx_x3f_3482_ = stack[1].m_obj;
lean_object* v_x_3483_ = stack[2].m_obj;
lean_object* v___y_3484_ = stack[3].m_obj;
lean_object* v___y_3485_ = stack[4].m_obj;
lean_object* v___y_3486_ = stack[5].m_obj;
lean_object* v___y_3487_ = stack[6].m_obj;
lean_object* v___y_3488_ = stack[7].m_obj;
lean_object* v___y_3489_ = stack[8].m_obj;
lean_object* v_res_3545_;
v_res_3545_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3481_, v_ctx_x3f_3482_, v_x_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
stack->m_obj
 = v_res_3545_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v___x_3546_, lean_object* v_ctx_x3f_3547_, size_t v_sz_3548_, size_t v_i_3549_, lean_object* v_bs_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
uint8_t v___x_3558_; 
v___x_3558_ = lean_usize_dec_lt(v_i_3549_, v_sz_3548_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; 
lean_dec_ref(v_ctx_x3f_3547_);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_bs_3550_);
return v___x_3559_;
}
else
{
lean_object* v_v_3560_; lean_object* v___x_3561_; lean_object* v_bs_x27_3562_; lean_object* v___x_3563_; 
v_v_3560_ = lean_array_uget(v_bs_3550_, v_i_3549_);
v___x_3561_ = lean_unsigned_to_nat(0u);
v_bs_x27_3562_ = lean_array_uset(v_bs_3550_, v_i_3549_, v___x_3561_);
lean_inc_ref(v_ctx_x3f_3547_);
v___x_3563_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3546_, v_ctx_x3f_3547_, v_v_3560_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; size_t v___x_3565_; size_t v___x_3566_; lean_object* v___x_3567_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v___x_3565_ = ((size_t)1ULL);
v___x_3566_ = lean_usize_add(v_i_3549_, v___x_3565_);
v___x_3567_ = lean_array_uset(v_bs_x27_3562_, v_i_3549_, v_a_3564_);
v_i_3549_ = v___x_3566_;
v_bs_3550_ = v___x_3567_;
goto _start;
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_bs_x27_3562_);
lean_dec_ref(v_ctx_x3f_3547_);
v_a_3569_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3563_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3563_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3546_ = stack[0].m_obj;
lean_object* v_ctx_x3f_3547_ = stack[1].m_obj;
size_t v_sz_3548_ = stack[2].m_num;
size_t v_i_3549_ = stack[3].m_num;
lean_object* v_bs_3550_ = stack[4].m_obj;
lean_object* v___y_3551_ = stack[5].m_obj;
lean_object* v___y_3552_ = stack[6].m_obj;
lean_object* v___y_3553_ = stack[7].m_obj;
lean_object* v___y_3554_ = stack[8].m_obj;
lean_object* v___y_3555_ = stack[9].m_obj;
lean_object* v___y_3556_ = stack[10].m_obj;
lean_object* v_res_3577_;
v_res_3577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3546_, v_ctx_x3f_3547_, v_sz_3548_, v_i_3549_, v_bs_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
stack->m_obj
 = v_res_3577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v___x_3578_, lean_object* v_ctx_x3f_3579_, lean_object* v_sz_3580_, lean_object* v_i_3581_, lean_object* v_bs_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
size_t v_sz_boxed_3590_; size_t v_i_boxed_3591_; lean_object* v_res_3592_; 
v_sz_boxed_3590_ = lean_unbox_usize(v_sz_3580_);
lean_dec(v_sz_3580_);
v_i_boxed_3591_ = lean_unbox_usize(v_i_3581_);
lean_dec(v_i_3581_);
v_res_3592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3578_, v_ctx_x3f_3579_, v_sz_boxed_3590_, v_i_boxed_3591_, v_bs_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v___x_3578_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v___x_3593_, lean_object* v_ctx_x3f_3594_, lean_object* v_x_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3593_, v_ctx_x3f_3594_, v_x_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___x_3593_);
return v_res_3603_;
}
}
lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object* v___x_3604_, lean_object* v_ctx_x3f_3605_, lean_object* v_t_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_root_3614_; lean_object* v_tail_3615_; lean_object* v_size_3616_; size_t v_shift_3617_; lean_object* v_tailOff_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3654_; 
v_root_3614_ = lean_ctor_get(v_t_3606_, 0);
v_tail_3615_ = lean_ctor_get(v_t_3606_, 1);
v_size_3616_ = lean_ctor_get(v_t_3606_, 2);
v_shift_3617_ = lean_ctor_get_usize(v_t_3606_, 4);
v_tailOff_3618_ = lean_ctor_get(v_t_3606_, 3);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_t_3606_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3620_ = v_t_3606_;
v_isShared_3621_ = v_isSharedCheck_3654_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_tailOff_3618_);
lean_inc(v_size_3616_);
lean_inc(v_tail_3615_);
lean_inc(v_root_3614_);
lean_dec(v_t_3606_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3654_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; 
lean_inc_ref(v_ctx_x3f_3605_);
v___x_3622_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3604_, v_ctx_x3f_3605_, v_root_3614_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; size_t v_sz_3624_; size_t v___x_3625_; lean_object* v___x_3626_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v_sz_3624_ = lean_array_size(v_tail_3615_);
v___x_3625_ = ((size_t)0ULL);
v___x_3626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3604_, v_ctx_x3f_3605_, v_sz_3624_, v___x_3625_, v_tail_3615_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3637_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 1, v_a_3627_);
lean_ctor_set(v___x_3620_, 0, v_a_3623_);
v___x_3632_ = v___x_3620_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3623_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_a_3627_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_size_3616_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_tailOff_3618_);
lean_ctor_set_usize(v_reuseFailAlloc_3636_, 4, v_shift_3617_);
v___x_3632_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3634_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3632_);
v___x_3634_ = v___x_3629_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v_a_3623_);
lean_del_object(v___x_3620_);
lean_dec(v_tailOff_3618_);
lean_dec(v_size_3616_);
v_a_3638_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3626_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3626_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_del_object(v___x_3620_);
lean_dec(v_tailOff_3618_);
lean_dec(v_size_3616_);
lean_dec_ref(v_tail_3615_);
lean_dec_ref(v_ctx_x3f_3605_);
v_a_3646_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3622_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3622_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3604_ = stack[0].m_obj;
lean_object* v_ctx_x3f_3605_ = stack[1].m_obj;
lean_object* v_t_3606_ = stack[2].m_obj;
lean_object* v___y_3607_ = stack[3].m_obj;
lean_object* v___y_3608_ = stack[4].m_obj;
lean_object* v___y_3609_ = stack[5].m_obj;
lean_object* v___y_3610_ = stack[6].m_obj;
lean_object* v___y_3611_ = stack[7].m_obj;
lean_object* v___y_3612_ = stack[8].m_obj;
lean_object* v_res_3655_;
v_res_3655_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3604_, v_ctx_x3f_3605_, v_t_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
stack->m_obj
 = v_res_3655_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object* v___x_3656_, lean_object* v_ctx_x3f_3657_, lean_object* v_t_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3656_, v_ctx_x3f_3657_, v_t_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec_ref(v___x_3656_);
return v_res_3666_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3667_, lean_object* v_ctx_x3f_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v_a_3674_, lean_object* v_a_x3f_3675_){
_start:
{
lean_object* v___x_3677_; lean_object* v_infoState_3678_; lean_object* v_trees_3679_; lean_object* v___x_3680_; 
v___x_3677_ = lean_st_ref_get(v___y_3667_);
v_infoState_3678_ = lean_ctor_get(v___x_3677_, 8);
lean_inc_ref(v_infoState_3678_);
lean_dec(v___x_3677_);
v_trees_3679_ = lean_ctor_get(v_infoState_3678_, 2);
lean_inc_ref(v_trees_3679_);
v___x_3680_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_3678_, v_ctx_x3f_3668_, v_trees_3679_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3667_);
lean_dec_ref(v_infoState_3678_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3720_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3720_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3720_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v_infoState_3686_; lean_object* v_env_3687_; lean_object* v_nextMacroScope_3688_; lean_object* v_ngen_3689_; lean_object* v_auxDeclNGen_3690_; lean_object* v_traceState_3691_; lean_object* v_cache_3692_; lean_object* v_recordedDeps_3693_; lean_object* v_messages_3694_; lean_object* v_snapshotTasks_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3719_; 
v___x_3685_ = lean_st_ref_take(v___y_3667_);
v_infoState_3686_ = lean_ctor_get(v___x_3685_, 8);
v_env_3687_ = lean_ctor_get(v___x_3685_, 0);
v_nextMacroScope_3688_ = lean_ctor_get(v___x_3685_, 1);
v_ngen_3689_ = lean_ctor_get(v___x_3685_, 2);
v_auxDeclNGen_3690_ = lean_ctor_get(v___x_3685_, 3);
v_traceState_3691_ = lean_ctor_get(v___x_3685_, 4);
v_cache_3692_ = lean_ctor_get(v___x_3685_, 5);
v_recordedDeps_3693_ = lean_ctor_get(v___x_3685_, 6);
v_messages_3694_ = lean_ctor_get(v___x_3685_, 7);
v_snapshotTasks_3695_ = lean_ctor_get(v___x_3685_, 9);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3697_ = v___x_3685_;
v_isShared_3698_ = v_isSharedCheck_3719_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_snapshotTasks_3695_);
lean_inc(v_infoState_3686_);
lean_inc(v_messages_3694_);
lean_inc(v_recordedDeps_3693_);
lean_inc(v_cache_3692_);
lean_inc(v_traceState_3691_);
lean_inc(v_auxDeclNGen_3690_);
lean_inc(v_ngen_3689_);
lean_inc(v_nextMacroScope_3688_);
lean_inc(v_env_3687_);
lean_dec(v___x_3685_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3719_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
uint8_t v_enabled_3699_; lean_object* v_assignment_3700_; lean_object* v_lazyAssignment_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3717_; 
v_enabled_3699_ = lean_ctor_get_uint8(v_infoState_3686_, sizeof(void*)*3);
v_assignment_3700_ = lean_ctor_get(v_infoState_3686_, 0);
v_lazyAssignment_3701_ = lean_ctor_get(v_infoState_3686_, 1);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_infoState_3686_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; 
v_unused_3718_ = lean_ctor_get(v_infoState_3686_, 2);
lean_dec(v_unused_3718_);
v___x_3703_ = v_infoState_3686_;
v_isShared_3704_ = v_isSharedCheck_3717_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_lazyAssignment_3701_);
lean_inc(v_assignment_3700_);
lean_dec(v_infoState_3686_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3717_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3705_ = lean_box(0);
v___x_3706_ = l_Lean_PersistentArray_append___redArg(v_a_3674_, v_a_3681_);
lean_dec(v_a_3681_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 2, v___x_3706_);
v___x_3708_ = v___x_3703_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_assignment_3700_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_lazyAssignment_3701_);
lean_ctor_set(v_reuseFailAlloc_3716_, 2, v___x_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3716_, sizeof(void*)*3, v_enabled_3699_);
v___x_3708_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 8, v___x_3708_);
v___x_3710_ = v___x_3697_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_env_3687_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_nextMacroScope_3688_);
lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_ngen_3689_);
lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_auxDeclNGen_3690_);
lean_ctor_set(v_reuseFailAlloc_3715_, 4, v_traceState_3691_);
lean_ctor_set(v_reuseFailAlloc_3715_, 5, v_cache_3692_);
lean_ctor_set(v_reuseFailAlloc_3715_, 6, v_recordedDeps_3693_);
lean_ctor_set(v_reuseFailAlloc_3715_, 7, v_messages_3694_);
lean_ctor_set(v_reuseFailAlloc_3715_, 8, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3715_, 9, v_snapshotTasks_3695_);
v___x_3710_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3711_; lean_object* v___x_3713_; 
v___x_3711_ = lean_st_ref_put(v___y_3667_, v___x_3710_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3705_);
v___x_3713_ = v___x_3683_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3705_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref(v_a_3674_);
v_a_3721_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3680_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3680_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3667_ = stack[0].m_obj;
lean_object* v_ctx_x3f_3668_ = stack[1].m_obj;
lean_object* v___y_3669_ = stack[2].m_obj;
lean_object* v___y_3670_ = stack[3].m_obj;
lean_object* v___y_3671_ = stack[4].m_obj;
lean_object* v___y_3672_ = stack[5].m_obj;
lean_object* v___y_3673_ = stack[6].m_obj;
lean_object* v_a_3674_ = stack[7].m_obj;
lean_object* v_a_x3f_3675_ = stack[8].m_obj;
lean_object* v_res_3729_;
v_res_3729_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3667_, v_ctx_x3f_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v_a_3674_, v_a_x3f_3675_);
stack->m_obj
 = v_res_3729_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3730_, lean_object* v_ctx_x3f_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v_a_3737_, lean_object* v_a_x3f_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3730_, v_ctx_x3f_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v_a_3737_, v_a_x3f_3738_);
lean_dec(v_a_x3f_3738_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3730_);
return v_res_3740_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3743_; lean_object* v_infoState_3744_; lean_object* v_trees_3745_; lean_object* v___x_3746_; lean_object* v_infoState_3747_; lean_object* v_env_3748_; lean_object* v_nextMacroScope_3749_; lean_object* v_ngen_3750_; lean_object* v_auxDeclNGen_3751_; lean_object* v_traceState_3752_; lean_object* v_cache_3753_; lean_object* v_recordedDeps_3754_; lean_object* v_messages_3755_; lean_object* v_snapshotTasks_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3779_; 
v___x_3743_ = lean_st_ref_get(v___y_3741_);
v_infoState_3744_ = lean_ctor_get(v___x_3743_, 8);
lean_inc_ref(v_infoState_3744_);
lean_dec(v___x_3743_);
v_trees_3745_ = lean_ctor_get(v_infoState_3744_, 2);
lean_inc_ref(v_trees_3745_);
lean_dec_ref(v_infoState_3744_);
v___x_3746_ = lean_st_ref_take(v___y_3741_);
v_infoState_3747_ = lean_ctor_get(v___x_3746_, 8);
v_env_3748_ = lean_ctor_get(v___x_3746_, 0);
v_nextMacroScope_3749_ = lean_ctor_get(v___x_3746_, 1);
v_ngen_3750_ = lean_ctor_get(v___x_3746_, 2);
v_auxDeclNGen_3751_ = lean_ctor_get(v___x_3746_, 3);
v_traceState_3752_ = lean_ctor_get(v___x_3746_, 4);
v_cache_3753_ = lean_ctor_get(v___x_3746_, 5);
v_recordedDeps_3754_ = lean_ctor_get(v___x_3746_, 6);
v_messages_3755_ = lean_ctor_get(v___x_3746_, 7);
v_snapshotTasks_3756_ = lean_ctor_get(v___x_3746_, 9);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3758_ = v___x_3746_;
v_isShared_3759_ = v_isSharedCheck_3779_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_snapshotTasks_3756_);
lean_inc(v_infoState_3747_);
lean_inc(v_messages_3755_);
lean_inc(v_recordedDeps_3754_);
lean_inc(v_cache_3753_);
lean_inc(v_traceState_3752_);
lean_inc(v_auxDeclNGen_3751_);
lean_inc(v_ngen_3750_);
lean_inc(v_nextMacroScope_3749_);
lean_inc(v_env_3748_);
lean_dec(v___x_3746_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3779_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
uint8_t v_enabled_3760_; lean_object* v_assignment_3761_; lean_object* v_lazyAssignment_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3777_; 
v_enabled_3760_ = lean_ctor_get_uint8(v_infoState_3747_, sizeof(void*)*3);
v_assignment_3761_ = lean_ctor_get(v_infoState_3747_, 0);
v_lazyAssignment_3762_ = lean_ctor_get(v_infoState_3747_, 1);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_infoState_3747_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v_infoState_3747_, 2);
lean_dec(v_unused_3778_);
v___x_3764_ = v_infoState_3747_;
v_isShared_3765_ = v_isSharedCheck_3777_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_lazyAssignment_3762_);
lean_inc(v_assignment_3761_);
lean_dec(v_infoState_3747_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3777_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3766_ = lean_unsigned_to_nat(32u);
v___x_3767_ = lean_mk_empty_array_with_capacity(v___x_3766_);
lean_dec_ref(v___x_3767_);
v___x_3768_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 2, v___x_3768_);
v___x_3770_ = v___x_3764_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_assignment_3761_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_lazyAssignment_3762_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v___x_3768_);
lean_ctor_set_uint8(v_reuseFailAlloc_3776_, sizeof(void*)*3, v_enabled_3760_);
v___x_3770_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 8, v___x_3770_);
v___x_3772_ = v___x_3758_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_env_3748_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_nextMacroScope_3749_);
lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_ngen_3750_);
lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_auxDeclNGen_3751_);
lean_ctor_set(v_reuseFailAlloc_3775_, 4, v_traceState_3752_);
lean_ctor_set(v_reuseFailAlloc_3775_, 5, v_cache_3753_);
lean_ctor_set(v_reuseFailAlloc_3775_, 6, v_recordedDeps_3754_);
lean_ctor_set(v_reuseFailAlloc_3775_, 7, v_messages_3755_);
lean_ctor_set(v_reuseFailAlloc_3775_, 8, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3775_, 9, v_snapshotTasks_3756_);
v___x_3772_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = lean_st_ref_put(v___y_3741_, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v_trees_3745_);
return v___x_3774_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3741_ = stack[0].m_obj;
lean_object* v_res_3780_;
v_res_3780_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3741_);
stack->m_obj
 = v_res_3780_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3781_);
lean_dec(v___y_3781_);
return v_res_3783_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object* v_x_3784_, lean_object* v_ctx_x3f_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; lean_object* v_infoState_3794_; uint8_t v_enabled_3795_; 
v___x_3793_ = lean_st_ref_get(v___y_3791_);
v_infoState_3794_ = lean_ctor_get(v___x_3793_, 8);
lean_inc_ref(v_infoState_3794_);
lean_dec(v___x_3793_);
v_enabled_3795_ = lean_ctor_get_uint8(v_infoState_3794_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3794_);
if (v_enabled_3795_ == 0)
{
lean_object* v___x_3796_; 
lean_dec_ref(v_ctx_x3f_3785_);
lean_inc(v___y_3791_);
lean_inc_ref(v___y_3790_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
v___x_3796_ = lean_apply_7(v_x_3784_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, lean_box(0));
return v___x_3796_;
}
else
{
lean_object* v___x_3797_; lean_object* v_a_3798_; lean_object* v_r_3799_; 
v___x_3797_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3791_);
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
lean_inc(v___y_3791_);
lean_inc_ref(v___y_3790_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
v_r_3799_ = lean_apply_7(v_x_3784_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, lean_box(0));
if (lean_obj_tag(v_r_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3824_; 
v_a_3800_ = lean_ctor_get(v_r_3799_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_r_3799_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3802_ = v_r_3799_;
v_isShared_3803_ = v_isSharedCheck_3824_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v_r_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3824_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
lean_inc(v_a_3800_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 1);
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; 
v___x_3806_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3791_, v_ctx_x3f_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v_a_3798_, v___x_3805_);
lean_dec_ref(v___x_3805_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v___x_3806_, 0);
lean_dec(v_unused_3814_);
v___x_3808_ = v___x_3806_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_dec(v___x_3806_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v_a_3800_);
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3800_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec(v_a_3800_);
v_a_3815_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3806_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3806_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v_a_3825_ = lean_ctor_get(v_r_3799_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v_r_3799_, 1);
v___x_3826_ = lean_box(0);
v___x_3827_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3791_, v_ctx_x3f_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v_a_3798_, v___x_3826_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; 
v_unused_3835_ = lean_ctor_get(v___x_3827_, 0);
lean_dec(v_unused_3835_);
v___x_3829_ = v___x_3827_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v___x_3827_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set_tag(v___x_3829_, 1);
lean_ctor_set(v___x_3829_, 0, v_a_3825_);
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3825_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec(v_a_3825_);
v_a_3836_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3827_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3827_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3784_ = stack[0].m_obj;
lean_object* v_ctx_x3f_3785_ = stack[1].m_obj;
lean_object* v___y_3786_ = stack[2].m_obj;
lean_object* v___y_3787_ = stack[3].m_obj;
lean_object* v___y_3788_ = stack[4].m_obj;
lean_object* v___y_3789_ = stack[5].m_obj;
lean_object* v___y_3790_ = stack[6].m_obj;
lean_object* v___y_3791_ = stack[7].m_obj;
lean_object* v_res_3844_;
v_res_3844_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3784_, v_ctx_x3f_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
stack->m_obj
 = v_res_3844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_3845_, lean_object* v_ctx_x3f_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3845_, v_ctx_x3f_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
return v_res_3854_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; lean_object* v_env_3860_; lean_object* v___x_3861_; lean_object* v_toCold_3862_; lean_object* v_mctx_3863_; lean_object* v_currNamespace_3864_; lean_object* v_openDecls_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v_ngen_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3859_ = lean_st_ref_get(v___y_3857_);
v_env_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc_ref(v_env_3860_);
lean_dec(v___x_3859_);
v___x_3861_ = lean_st_ref_get(v___y_3855_);
v_toCold_3862_ = lean_ctor_get(v___y_3856_, 0);
v_mctx_3863_ = lean_ctor_get(v___x_3861_, 0);
lean_inc_ref(v_mctx_3863_);
lean_dec(v___x_3861_);
v_currNamespace_3864_ = lean_ctor_get(v_toCold_3862_, 4);
v_openDecls_3865_ = lean_ctor_get(v_toCold_3862_, 5);
v___x_3866_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3856_);
v___x_3867_ = lean_st_ref_get(v___y_3857_);
v_ngen_3868_ = lean_ctor_get(v___x_3867_, 2);
lean_inc_ref(v_ngen_3868_);
lean_dec(v___x_3867_);
v___x_3869_ = lean_box(0);
v___x_3870_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_3865_);
lean_inc(v_currNamespace_3864_);
v___x_3871_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3871_, 0, v_env_3860_);
lean_ctor_set(v___x_3871_, 1, v___x_3869_);
lean_ctor_set(v___x_3871_, 2, v___x_3870_);
lean_ctor_set(v___x_3871_, 3, v_mctx_3863_);
lean_ctor_set(v___x_3871_, 4, v___x_3866_);
lean_ctor_set(v___x_3871_, 5, v_currNamespace_3864_);
lean_ctor_set(v___x_3871_, 6, v_openDecls_3865_);
lean_ctor_set(v___x_3871_, 7, v_ngen_3868_);
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3855_ = stack[0].m_obj;
lean_object* v___y_3856_ = stack[1].m_obj;
lean_object* v___y_3857_ = stack[2].m_obj;
lean_object* v_res_3873_;
v_res_3873_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3855_, v___y_3856_, v___y_3857_);
stack->m_obj
 = v_res_3873_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
return v_res_3878_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; lean_object* v_toCold_3887_; lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3912_; 
v___x_3886_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3882_, v___y_3883_, v___y_3884_);
v_toCold_3887_ = lean_ctor_get(v___y_3883_, 0);
v_a_3888_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3890_ = v___x_3886_;
v_isShared_3891_ = v_isSharedCheck_3912_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3886_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3912_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v_fileMap_3892_; lean_object* v_env_3893_; lean_object* v_mctx_3894_; lean_object* v_options_3895_; lean_object* v_currNamespace_3896_; lean_object* v_openDecls_3897_; lean_object* v_ngen_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3909_; 
v_fileMap_3892_ = lean_ctor_get(v_toCold_3887_, 1);
v_env_3893_ = lean_ctor_get(v_a_3888_, 0);
v_mctx_3894_ = lean_ctor_get(v_a_3888_, 3);
v_options_3895_ = lean_ctor_get(v_a_3888_, 4);
v_currNamespace_3896_ = lean_ctor_get(v_a_3888_, 5);
v_openDecls_3897_ = lean_ctor_get(v_a_3888_, 6);
v_ngen_3898_ = lean_ctor_get(v_a_3888_, 7);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_a_3888_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; lean_object* v_unused_3911_; 
v_unused_3910_ = lean_ctor_get(v_a_3888_, 2);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_a_3888_, 1);
lean_dec(v_unused_3911_);
v___x_3900_ = v_a_3888_;
v_isShared_3901_ = v_isSharedCheck_3909_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_ngen_3898_);
lean_inc(v_openDecls_3897_);
lean_inc(v_currNamespace_3896_);
lean_inc(v_options_3895_);
lean_inc(v_mctx_3894_);
lean_inc(v_env_3893_);
lean_dec(v_a_3888_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3909_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3902_ = lean_box(0);
lean_inc_ref(v_fileMap_3892_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 2, v_fileMap_3892_);
lean_ctor_set(v___x_3900_, 1, v___x_3902_);
v___x_3904_ = v___x_3900_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_env_3893_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_fileMap_3892_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_mctx_3894_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v_options_3895_);
lean_ctor_set(v_reuseFailAlloc_3908_, 5, v_currNamespace_3896_);
lean_ctor_set(v_reuseFailAlloc_3908_, 6, v_openDecls_3897_);
lean_ctor_set(v_reuseFailAlloc_3908_, 7, v_ngen_3898_);
v___x_3904_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3906_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 0, v___x_3904_);
v___x_3906_ = v___x_3890_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3879_ = stack[0].m_obj;
lean_object* v___y_3880_ = stack[1].m_obj;
lean_object* v___y_3881_ = stack[2].m_obj;
lean_object* v___y_3882_ = stack[3].m_obj;
lean_object* v___y_3883_ = stack[4].m_obj;
lean_object* v___y_3884_ = stack[5].m_obj;
lean_object* v_res_3913_;
v_res_3913_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
stack->m_obj
 = v_res_3913_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
return v_res_3921_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v___x_3929_; lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3939_; 
v___x_3929_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3939_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3939_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_a_3930_);
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3935_);
v___x_3937_ = v___x_3932_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3922_ = stack[0].m_obj;
lean_object* v___y_3923_ = stack[1].m_obj;
lean_object* v___y_3924_ = stack[2].m_obj;
lean_object* v___y_3925_ = stack[3].m_obj;
lean_object* v___y_3926_ = stack[4].m_obj;
lean_object* v___y_3927_ = stack[5].m_obj;
lean_object* v_res_3940_;
v_res_3940_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
stack->m_obj
 = v_res_3940_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
return v_res_3948_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object* v_x_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v___f_3958_; lean_object* v___x_3959_; 
v___f_3958_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0));
v___x_3959_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3950_, v___f_3958_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
return v___x_3959_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3950_ = stack[0].m_obj;
lean_object* v___y_3951_ = stack[1].m_obj;
lean_object* v___y_3952_ = stack[2].m_obj;
lean_object* v___y_3953_ = stack[3].m_obj;
lean_object* v___y_3954_ = stack[4].m_obj;
lean_object* v___y_3955_ = stack[5].m_obj;
lean_object* v___y_3956_ = stack[6].m_obj;
lean_object* v_res_3960_;
v_res_3960_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
stack->m_obj
 = v_res_3960_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object* v_x_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
return v_res_3969_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object* v_00_u03b1_3970_, lean_object* v_x_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3971_ = stack[1].m_obj;
lean_object* v___y_3972_ = stack[2].m_obj;
lean_object* v___y_3973_ = stack[3].m_obj;
lean_object* v___y_3974_ = stack[4].m_obj;
lean_object* v___y_3975_ = stack[5].m_obj;
lean_object* v___y_3976_ = stack[6].m_obj;
lean_object* v___y_3977_ = stack[7].m_obj;
lean_object* v_res_3980_;
v_res_3980_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_box(0), v_x_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
stack->m_obj
 = v_res_3980_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object* v_00_u03b1_3981_, lean_object* v_x_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(v_00_u03b1_3981_, v_x_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
return v_res_3990_;
}
}
static uint64_t _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_4011_; uint64_t v___x_4012_; 
v___x_4011_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_4012_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4011_);
return v___x_4012_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6(void){
_start:
{
uint64_t v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4013_ = lean_uint64_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5);
v___x_4014_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_4015_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
lean_ctor_set_uint64(v___x_4015_, sizeof(void*)*1, v___x_4013_);
return v___x_4015_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7(void){
_start:
{
uint8_t v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4016_ = 1;
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = lean_box(0);
v___x_4019_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1));
v___x_4020_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_4021_ = lean_box(1);
v___x_4022_ = 0;
v___x_4023_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6);
v___x_4024_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
lean_ctor_set(v___x_4024_, 1, v___x_4021_);
lean_ctor_set(v___x_4024_, 2, v___x_4020_);
lean_ctor_set(v___x_4024_, 3, v___x_4019_);
lean_ctor_set(v___x_4024_, 4, v___x_4018_);
lean_ctor_set(v___x_4024_, 5, v___x_4017_);
lean_ctor_set(v___x_4024_, 6, v___x_4018_);
lean_ctor_set_uint8(v___x_4024_, sizeof(void*)*7, v___x_4022_);
lean_ctor_set_uint8(v___x_4024_, sizeof(void*)*7 + 1, v___x_4022_);
lean_ctor_set_uint8(v___x_4024_, sizeof(void*)*7 + 2, v___x_4022_);
lean_ctor_set_uint8(v___x_4024_, sizeof(void*)*7 + 3, v___x_4016_);
return v___x_4024_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8(void){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4025_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4026_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
lean_ctor_set(v___x_4028_, 2, v___x_4027_);
lean_ctor_set(v___x_4028_, 3, v___x_4027_);
lean_ctor_set(v___x_4028_, 4, v___x_4026_);
lean_ctor_set(v___x_4028_, 5, v___x_4026_);
lean_ctor_set(v___x_4028_, 6, v___x_4026_);
lean_ctor_set(v___x_4028_, 7, v___x_4026_);
lean_ctor_set(v___x_4028_, 8, v___x_4026_);
lean_ctor_set(v___x_4028_, 9, v___x_4026_);
lean_ctor_set(v___x_4028_, 10, v___x_4026_);
lean_ctor_set(v___x_4028_, 11, v___x_4025_);
return v___x_4028_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_4030_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
lean_ctor_set(v___x_4030_, 2, v___x_4029_);
lean_ctor_set(v___x_4030_, 3, v___x_4029_);
lean_ctor_set(v___x_4030_, 4, v___x_4029_);
lean_ctor_set(v___x_4030_, 5, v___x_4029_);
return v___x_4030_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_4032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
lean_ctor_set(v___x_4032_, 2, v___x_4031_);
lean_ctor_set(v___x_4032_, 3, v___x_4031_);
lean_ctor_set(v___x_4032_, 4, v___x_4031_);
return v___x_4032_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4033_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10);
v___x_4034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_4035_ = lean_box(1);
v___x_4036_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
v___x_4037_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8);
v___x_4038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
lean_ctor_set(v___x_4038_, 1, v___x_4036_);
lean_ctor_set(v___x_4038_, 2, v___x_4035_);
lean_ctor_set(v___x_4038_, 3, v___x_4034_);
lean_ctor_set(v___x_4038_, 4, v___x_4033_);
return v___x_4038_;
}
}
lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object* v_mx_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4043_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4043_, 0, lean_box(0));
lean_closure_set(v___x_4043_, 1, v_mx_4039_);
v___x_4044_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2));
v___x_4045_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_4046_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7);
v___x_4047_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11);
v___x_4048_ = lean_st_mk_ref(v___x_4047_);
v___x_4049_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_4043_, v___x_4044_, v___x_4045_, v___x_4046_, v___x_4048_, v_a_4040_, v_a_4041_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4059_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v_fst_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
v_fst_4054_ = lean_ctor_get(v_a_4050_, 0);
lean_inc(v_fst_4054_);
lean_dec(v_a_4050_);
v___x_4055_ = lean_st_ref_get(v___x_4048_);
lean_dec(v___x_4048_);
lean_dec(v___x_4055_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v_fst_4054_);
v___x_4057_ = v___x_4052_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_fst_4054_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec(v___x_4048_);
v_a_4060_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4049_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4049_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_runConfigElab___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mx_4039_ = stack[0].m_obj;
lean_object* v_a_4040_ = stack[1].m_obj;
lean_object* v_a_4041_ = stack[2].m_obj;
lean_object* v_res_4068_;
v_res_4068_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_4039_, v_a_4040_, v_a_4041_);
stack->m_obj
 = v_res_4068_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object* v_mx_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_4069_, v_a_4070_, v_a_4071_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
return v_res_4073_;
}
}
lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object* v_00_u03b1_4074_, lean_object* v_mx_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_4075_, v_a_4076_, v_a_4077_);
return v___x_4079_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_runConfigElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_mx_4075_ = stack[1].m_obj;
lean_object* v_a_4076_ = stack[2].m_obj;
lean_object* v_a_4077_ = stack[3].m_obj;
lean_object* v_res_4080_;
v_res_4080_ = l_Lean_Elab_ConfigEval_runConfigElab(lean_box(0), v_mx_4075_, v_a_4076_, v_a_4077_);
stack->m_obj
 = v_res_4080_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object* v_00_u03b1_4081_, lean_object* v_mx_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_4081_, v_mx_4082_, v_a_4083_, v_a_4084_);
lean_dec(v_a_4084_);
lean_dec_ref(v_a_4083_);
return v_res_4086_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_4090_, v___y_4091_, v___y_4092_);
return v___x_4094_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4087_ = stack[0].m_obj;
lean_object* v___y_4088_ = stack[1].m_obj;
lean_object* v___y_4089_ = stack[2].m_obj;
lean_object* v___y_4090_ = stack[3].m_obj;
lean_object* v___y_4091_ = stack[4].m_obj;
lean_object* v___y_4092_ = stack[5].m_obj;
lean_object* v_res_4095_;
v_res_4095_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
stack->m_obj
 = v_res_4095_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
return v_res_4103_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4104_ = stack[0].m_obj;
lean_object* v___y_4105_ = stack[1].m_obj;
lean_object* v___y_4106_ = stack[2].m_obj;
lean_object* v___y_4107_ = stack[3].m_obj;
lean_object* v___y_4108_ = stack[4].m_obj;
lean_object* v___y_4109_ = stack[5].m_obj;
lean_object* v_res_4112_;
v_res_4112_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
stack->m_obj
 = v_res_4112_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4120_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object* v_00_u03b1_4121_, lean_object* v_x_4122_, lean_object* v_ctx_x3f_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_4122_, v_ctx_x3f_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
return v___x_4131_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4122_ = stack[1].m_obj;
lean_object* v_ctx_x3f_4123_ = stack[2].m_obj;
lean_object* v___y_4124_ = stack[3].m_obj;
lean_object* v___y_4125_ = stack[4].m_obj;
lean_object* v___y_4126_ = stack[5].m_obj;
lean_object* v___y_4127_ = stack[6].m_obj;
lean_object* v___y_4128_ = stack[7].m_obj;
lean_object* v___y_4129_ = stack[8].m_obj;
lean_object* v_res_4132_;
v_res_4132_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_box(0), v_x_4122_, v_ctx_x3f_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
stack->m_obj
 = v_res_4132_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4133_, lean_object* v_x_4134_, lean_object* v_ctx_x3f_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_4133_, v_x_4134_, v_ctx_x3f_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
return v_res_4143_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object* v_eval_4144_, uint8_t v_logExceptions_4145_, lean_object* v_onErr_4146_, lean_object* v_init_4147_, lean_object* v_cfg_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_4144_, v_logExceptions_4145_, v_onErr_4146_, v_init_4147_, v_cfg_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4156_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_4144_ = stack[0].m_obj;
uint8_t v_logExceptions_4145_ = stack[1].m_num;
lean_object* v_onErr_4146_ = stack[2].m_obj;
lean_object* v_init_4147_ = stack[3].m_obj;
lean_object* v_cfg_4148_ = stack[4].m_obj;
lean_object* v___y_4149_ = stack[5].m_obj;
lean_object* v___y_4150_ = stack[6].m_obj;
lean_object* v___y_4151_ = stack[7].m_obj;
lean_object* v___y_4152_ = stack[8].m_obj;
lean_object* v___y_4153_ = stack[9].m_obj;
lean_object* v___y_4154_ = stack[10].m_obj;
lean_object* v_res_4157_;
v_res_4157_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4144_, v_logExceptions_4145_, v_onErr_4146_, v_init_4147_, v_cfg_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
stack->m_obj
 = v_res_4157_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object* v_eval_4158_, lean_object* v_logExceptions_4159_, lean_object* v_onErr_4160_, lean_object* v_init_4161_, lean_object* v_cfg_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
uint8_t v_logExceptions_boxed_4170_; lean_object* v_res_4171_; 
v_logExceptions_boxed_4170_ = lean_unbox(v_logExceptions_4159_);
v_res_4171_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4158_, v_logExceptions_boxed_4170_, v_onErr_4160_, v_init_4161_, v_cfg_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
return v_res_4171_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object* v_eval_4172_, lean_object* v_init_4173_, lean_object* v_cfg_4174_, lean_object* v_onErr_4175_, uint8_t v_logExceptions_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v___x_4180_; lean_object* v___f_4181_; uint8_t v___y_4183_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
v___x_4180_ = lean_box(v_logExceptions_4176_);
lean_inc_n(v_cfg_4174_, 2);
lean_inc(v_init_4173_);
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4181_, 0, v_eval_4172_);
lean_closure_set(v___f_4181_, 1, v___x_4180_);
lean_closure_set(v___f_4181_, 2, v_onErr_4175_);
lean_closure_set(v___f_4181_, 3, v_init_4173_);
lean_closure_set(v___f_4181_, 4, v_cfg_4174_);
v___x_4186_ = lean_unsigned_to_nat(0u);
v___x_4187_ = l_Lean_Syntax_matchesNull(v_cfg_4174_, v___x_4186_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4188_ = l_Lean_Syntax_getNumArgs(v_cfg_4174_);
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = lean_nat_dec_eq(v___x_4188_, v___x_4189_);
lean_dec(v___x_4188_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; 
lean_dec(v_cfg_4174_);
lean_dec(v_init_4173_);
v___x_4191_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4181_, v_a_4177_, v_a_4178_);
return v___x_4191_;
}
else
{
lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4192_ = l_Lean_Syntax_getArg(v_cfg_4174_, v___x_4186_);
lean_dec(v_cfg_4174_);
v___x_4193_ = l_Lean_Syntax_matchesNull(v___x_4192_, v___x_4186_);
v___y_4183_ = v___x_4193_;
goto v___jp_4182_;
}
}
else
{
lean_dec(v_cfg_4174_);
v___y_4183_ = v___x_4187_;
goto v___jp_4182_;
}
v___jp_4182_:
{
if (v___y_4183_ == 0)
{
lean_object* v___x_4184_; 
lean_dec(v_init_4173_);
v___x_4184_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4181_, v_a_4177_, v_a_4178_);
return v___x_4184_;
}
else
{
lean_object* v___x_4185_; 
lean_dec_ref(v___f_4181_);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v_init_4173_);
return v___x_4185_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_4172_ = stack[0].m_obj;
lean_object* v_init_4173_ = stack[1].m_obj;
lean_object* v_cfg_4174_ = stack[2].m_obj;
lean_object* v_onErr_4175_ = stack[3].m_obj;
uint8_t v_logExceptions_4176_ = stack[4].m_num;
lean_object* v_a_4177_ = stack[5].m_obj;
lean_object* v_a_4178_ = stack[6].m_obj;
lean_object* v_res_4194_;
v_res_4194_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4172_, v_init_4173_, v_cfg_4174_, v_onErr_4175_, v_logExceptions_4176_, v_a_4177_, v_a_4178_);
stack->m_obj
 = v_res_4194_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object* v_eval_4195_, lean_object* v_init_4196_, lean_object* v_cfg_4197_, lean_object* v_onErr_4198_, lean_object* v_logExceptions_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
uint8_t v_logExceptions_boxed_4203_; lean_object* v_res_4204_; 
v_logExceptions_boxed_4203_ = lean_unbox(v_logExceptions_4199_);
v_res_4204_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4195_, v_init_4196_, v_cfg_4197_, v_onErr_4198_, v_logExceptions_boxed_4203_, v_a_4200_, v_a_4201_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
return v_res_4204_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object* v_00_u03b1_4205_, lean_object* v_eval_4206_, lean_object* v_init_4207_, lean_object* v_cfg_4208_, lean_object* v_onErr_4209_, uint8_t v_logExceptions_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4206_, v_init_4207_, v_cfg_4208_, v_onErr_4209_, v_logExceptions_4210_, v_a_4211_, v_a_4212_);
return v___x_4214_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_4206_ = stack[1].m_obj;
lean_object* v_init_4207_ = stack[2].m_obj;
lean_object* v_cfg_4208_ = stack[3].m_obj;
lean_object* v_onErr_4209_ = stack[4].m_obj;
uint8_t v_logExceptions_4210_ = stack[5].m_num;
lean_object* v_a_4211_ = stack[6].m_obj;
lean_object* v_a_4212_ = stack[7].m_obj;
lean_object* v_res_4215_;
v_res_4215_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_box(0), v_eval_4206_, v_init_4207_, v_cfg_4208_, v_onErr_4209_, v_logExceptions_4210_, v_a_4211_, v_a_4212_);
stack->m_obj
 = v_res_4215_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object* v_00_u03b1_4216_, lean_object* v_eval_4217_, lean_object* v_init_4218_, lean_object* v_cfg_4219_, lean_object* v_onErr_4220_, lean_object* v_logExceptions_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
uint8_t v_logExceptions_boxed_4225_; lean_object* v_res_4226_; 
v_logExceptions_boxed_4225_ = lean_unbox(v_logExceptions_4221_);
v_res_4226_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(v_00_u03b1_4216_, v_eval_4217_, v_init_4218_, v_cfg_4219_, v_onErr_4220_, v_logExceptions_boxed_4225_, v_a_4222_, v_a_4223_);
lean_dec(v_a_4223_);
lean_dec_ref(v_a_4222_);
return v_res_4226_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object* v_eval_4227_, uint8_t v_logExceptions_4228_, lean_object* v_onErr_4229_, lean_object* v_init_4230_, lean_object* v_cfgs_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_4227_, v_logExceptions_4228_, v_onErr_4229_, v_init_4230_, v_cfgs_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
return v___x_4239_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_4227_ = stack[0].m_obj;
uint8_t v_logExceptions_4228_ = stack[1].m_num;
lean_object* v_onErr_4229_ = stack[2].m_obj;
lean_object* v_init_4230_ = stack[3].m_obj;
lean_object* v_cfgs_4231_ = stack[4].m_obj;
lean_object* v___y_4232_ = stack[5].m_obj;
lean_object* v___y_4233_ = stack[6].m_obj;
lean_object* v___y_4234_ = stack[7].m_obj;
lean_object* v___y_4235_ = stack[8].m_obj;
lean_object* v___y_4236_ = stack[9].m_obj;
lean_object* v___y_4237_ = stack[10].m_obj;
lean_object* v_res_4240_;
v_res_4240_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4227_, v_logExceptions_4228_, v_onErr_4229_, v_init_4230_, v_cfgs_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
stack->m_obj
 = v_res_4240_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object* v_eval_4241_, lean_object* v_logExceptions_4242_, lean_object* v_onErr_4243_, lean_object* v_init_4244_, lean_object* v_cfgs_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
uint8_t v_logExceptions_boxed_4253_; lean_object* v_res_4254_; 
v_logExceptions_boxed_4253_ = lean_unbox(v_logExceptions_4242_);
v_res_4254_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4241_, v_logExceptions_boxed_4253_, v_onErr_4243_, v_init_4244_, v_cfgs_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec_ref(v_cfgs_4245_);
return v_res_4254_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object* v_eval_4255_, lean_object* v_init_4256_, lean_object* v_cfgs_4257_, lean_object* v_onErr_4258_, uint8_t v_logExceptions_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v___x_4263_ = lean_array_get_size(v_cfgs_4257_);
v___x_4264_ = lean_unsigned_to_nat(0u);
v___x_4265_ = lean_nat_dec_eq(v___x_4263_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v___f_4267_; lean_object* v___x_4268_; 
v___x_4266_ = lean_box(v_logExceptions_4259_);
v___f_4267_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4267_, 0, v_eval_4255_);
lean_closure_set(v___f_4267_, 1, v___x_4266_);
lean_closure_set(v___f_4267_, 2, v_onErr_4258_);
lean_closure_set(v___f_4267_, 3, v_init_4256_);
lean_closure_set(v___f_4267_, 4, v_cfgs_4257_);
v___x_4268_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4267_, v_a_4260_, v_a_4261_);
return v___x_4268_;
}
else
{
lean_object* v___x_4269_; 
lean_dec_ref(v_onErr_4258_);
lean_dec_ref(v_cfgs_4257_);
lean_dec_ref(v_eval_4255_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v_init_4256_);
return v___x_4269_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_4255_ = stack[0].m_obj;
lean_object* v_init_4256_ = stack[1].m_obj;
lean_object* v_cfgs_4257_ = stack[2].m_obj;
lean_object* v_onErr_4258_ = stack[3].m_obj;
uint8_t v_logExceptions_4259_ = stack[4].m_num;
lean_object* v_a_4260_ = stack[5].m_obj;
lean_object* v_a_4261_ = stack[6].m_obj;
lean_object* v_res_4270_;
v_res_4270_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4255_, v_init_4256_, v_cfgs_4257_, v_onErr_4258_, v_logExceptions_4259_, v_a_4260_, v_a_4261_);
stack->m_obj
 = v_res_4270_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object* v_eval_4271_, lean_object* v_init_4272_, lean_object* v_cfgs_4273_, lean_object* v_onErr_4274_, lean_object* v_logExceptions_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
uint8_t v_logExceptions_boxed_4279_; lean_object* v_res_4280_; 
v_logExceptions_boxed_4279_ = lean_unbox(v_logExceptions_4275_);
v_res_4280_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4271_, v_init_4272_, v_cfgs_4273_, v_onErr_4274_, v_logExceptions_boxed_4279_, v_a_4276_, v_a_4277_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
return v_res_4280_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object* v_00_u03b1_4281_, lean_object* v_eval_4282_, lean_object* v_init_4283_, lean_object* v_cfgs_4284_, lean_object* v_onErr_4285_, uint8_t v_logExceptions_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4282_, v_init_4283_, v_cfgs_4284_, v_onErr_4285_, v_logExceptions_4286_, v_a_4287_, v_a_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_eval_4282_ = stack[1].m_obj;
lean_object* v_init_4283_ = stack[2].m_obj;
lean_object* v_cfgs_4284_ = stack[3].m_obj;
lean_object* v_onErr_4285_ = stack[4].m_obj;
uint8_t v_logExceptions_4286_ = stack[5].m_num;
lean_object* v_a_4287_ = stack[6].m_obj;
lean_object* v_a_4288_ = stack[7].m_obj;
lean_object* v_res_4291_;
v_res_4291_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_box(0), v_eval_4282_, v_init_4283_, v_cfgs_4284_, v_onErr_4285_, v_logExceptions_4286_, v_a_4287_, v_a_4288_);
stack->m_obj
 = v_res_4291_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object* v_00_u03b1_4292_, lean_object* v_eval_4293_, lean_object* v_init_4294_, lean_object* v_cfgs_4295_, lean_object* v_onErr_4296_, lean_object* v_logExceptions_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
uint8_t v_logExceptions_boxed_4301_; lean_object* v_res_4302_; 
v_logExceptions_boxed_4301_ = lean_unbox(v_logExceptions_4297_);
v_res_4302_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(v_00_u03b1_4292_, v_eval_4293_, v_init_4294_, v_cfgs_4295_, v_onErr_4296_, v_logExceptions_boxed_4301_, v_a_4298_, v_a_4299_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
return v_res_4302_;
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

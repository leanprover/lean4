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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__26));
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
v___x_1527_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1514_, v_declHint_1509_);
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
lean_object* v_val_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1591_; 
v_val_1535_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1537_ = v___x_1527_;
v_isShared_1538_ = v_isSharedCheck_1591_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_val_1535_);
lean_dec(v___x_1527_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1591_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v_modules_1540_; lean_object* v_moduleNames_1541_; lean_object* v_mod_1542_; uint8_t v___y_1544_; uint8_t v___x_1574_; 
v___x_1539_ = l_Lean_Environment_header(v_env_1514_);
lean_dec_ref(v_env_1514_);
v_modules_1540_ = lean_ctor_get(v___x_1539_, 3);
lean_inc_ref(v_modules_1540_);
v_moduleNames_1541_ = lean_ctor_get(v___x_1539_, 4);
lean_inc_ref(v_moduleNames_1541_);
lean_dec_ref(v___x_1539_);
v_mod_1542_ = lean_array_get(v___x_1512_, v_moduleNames_1541_, v_val_1535_);
lean_dec_ref(v_moduleNames_1541_);
v___x_1574_ = l_Lean_isPrivateName(v_declHint_1509_);
lean_dec(v_declHint_1509_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = lean_array_get_size(v_modules_1540_);
v___x_1576_ = lean_nat_dec_lt(v_val_1535_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_dec_ref(v_modules_1540_);
lean_dec(v_val_1535_);
v___y_1544_ = v___x_1574_;
goto v___jp_1543_;
}
else
{
lean_object* v___x_1577_; lean_object* v_toImport_1578_; uint8_t v_isExported_1579_; 
v___x_1577_ = lean_array_fget(v_modules_1540_, v_val_1535_);
lean_dec(v_val_1535_);
lean_dec_ref(v_modules_1540_);
v_toImport_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_toImport_1578_);
lean_dec(v___x_1577_);
v_isExported_1579_ = lean_ctor_get_uint8(v_toImport_1578_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1578_);
v___y_1544_ = v_isExported_1579_;
goto v___jp_1543_;
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v_modules_1540_);
lean_del_object(v___x_1537_);
lean_dec(v_val_1535_);
v___x_1580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v_c_1526_);
v___x_1582_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__25);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = l_Lean_MessageData_ofName(v_mod_1542_);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__27);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_MessageData_note(v___x_1587_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_msg_1508_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
v___jp_1543_:
{
if (v___y_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v_c_1526_);
v___x_1547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_MessageData_ofName(v_mod_1542_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = l_Lean_MessageData_note(v___x_1552_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_msg_1508_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1554_);
v___x_1556_ = v___x_1537_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_c_1526_);
v___x_1560_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_MessageData_ofName(v_mod_1542_);
lean_inc_ref(v___x_1562_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1562_);
v___x_1567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_MessageData_note(v___x_1568_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_msg_1508_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1570_);
v___x_1572_ = v___x_1537_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
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
lean_object* v___x_1592_; 
lean_dec_ref(v_env_1514_);
lean_dec(v_declHint_1509_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_msg_1508_);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1593_, lean_object* v_declHint_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1593_, v_declHint_1594_, v___y_1595_);
lean_dec(v___y_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_1598_, lean_object* v_declHint_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1617_; 
v___x_1607_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1598_, v_declHint_1599_, v___y_1605_);
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1612_ = l_Lean_unknownIdentifierMessageTag;
v___x_1613_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v_a_1608_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1613_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_1618_, lean_object* v_declHint_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1618_, v_declHint_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1628_, lean_object* v_msg_1629_, lean_object* v_declHint_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1640_; 
v___x_1638_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1629_, v_declHint_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v___x_1638_);
v___x_1640_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1628_, v_a_1639_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1641_, lean_object* v_msg_1642_, lean_object* v_declHint_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1641_, v_msg_1642_, v_declHint_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_ref_1641_);
return v_res_1651_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1654_ = l_Lean_stringToMessageData(v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_1655_, lean_object* v_constName_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1664_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1665_ = 0;
lean_inc(v_constName_1656_);
v___x_1666_ = l_Lean_MessageData_ofConstName(v_constName_1656_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1664_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1655_, v___x_1669_, v_constName_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1671_, lean_object* v_constName_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1671_, v_constName_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_ref_1671_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_ref_1689_; lean_object* v___x_1690_; 
v_ref_1689_ = lean_ctor_get(v___y_1686_, 2);
v___x_1690_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1689_, v_constName_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object* v_constName_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v_env_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; 
v___x_1708_ = lean_st_ref_get(v___y_1706_);
v_env_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc_ref(v_env_1709_);
lean_dec(v___x_1708_);
v___x_1710_ = 0;
lean_inc(v_constName_1700_);
v___x_1711_ = l_Lean_Environment_findConstVal_x3f(v_env_1709_, v_constName_1700_, v___x_1710_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
return v___x_1712_;
}
else
{
lean_object* v_val_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_constName_1700_);
v_val_1713_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1711_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_val_1713_);
lean_dec(v___x_1711_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 0);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_val_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
if (lean_obj_tag(v_a_1730_) == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = l_List_reverse___redArg(v_a_1731_);
return v___x_1732_;
}
else
{
lean_object* v_head_1733_; lean_object* v_tail_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1743_; 
v_head_1733_ = lean_ctor_get(v_a_1730_, 0);
v_tail_1734_ = lean_ctor_get(v_a_1730_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_a_1730_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1736_ = v_a_1730_;
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_tail_1734_);
lean_inc(v_head_1733_);
lean_dec(v_a_1730_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l_Lean_mkLevelParam(v_head_1733_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v_a_1731_);
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_a_1731_);
v___x_1740_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
v_a_1730_ = v_tail_1734_;
v_a_1731_ = v___x_1740_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object* v_constName_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
lean_inc(v_constName_1744_);
v___x_1752_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1764_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1764_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1764_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_levelParams_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v_levelParams_1757_ = lean_ctor_get(v_a_1753_, 1);
lean_inc(v_levelParams_1757_);
lean_dec(v_a_1753_);
v___x_1758_ = lean_box(0);
v___x_1759_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_1757_, v___x_1758_);
v___x_1760_ = l_Lean_mkConst(v_constName_1744_, v___x_1759_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1760_);
v___x_1762_ = v___x_1755_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_constName_1744_);
v_a_1765_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1752_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1752_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object* v_constName_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v_infoState_1786_; uint8_t v_enabled_1787_; 
v___x_1785_ = lean_st_ref_get(v___y_1783_);
v_infoState_1786_ = lean_ctor_get(v___x_1785_, 8);
lean_inc_ref(v_infoState_1786_);
lean_dec(v___x_1785_);
v_enabled_1787_ = lean_ctor_get_uint8(v_infoState_1786_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1786_);
if (v_enabled_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec_ref(v_t_1782_);
v___x_1788_ = lean_box(0);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; lean_object* v_infoState_1791_; lean_object* v_env_1792_; lean_object* v_nextMacroScope_1793_; lean_object* v_ngen_1794_; lean_object* v_auxDeclNGen_1795_; lean_object* v_traceState_1796_; lean_object* v_cache_1797_; lean_object* v_recordedDeps_1798_; lean_object* v_messages_1799_; lean_object* v_snapshotTasks_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1822_; 
v___x_1790_ = lean_st_ref_take(v___y_1783_);
v_infoState_1791_ = lean_ctor_get(v___x_1790_, 8);
v_env_1792_ = lean_ctor_get(v___x_1790_, 0);
v_nextMacroScope_1793_ = lean_ctor_get(v___x_1790_, 1);
v_ngen_1794_ = lean_ctor_get(v___x_1790_, 2);
v_auxDeclNGen_1795_ = lean_ctor_get(v___x_1790_, 3);
v_traceState_1796_ = lean_ctor_get(v___x_1790_, 4);
v_cache_1797_ = lean_ctor_get(v___x_1790_, 5);
v_recordedDeps_1798_ = lean_ctor_get(v___x_1790_, 6);
v_messages_1799_ = lean_ctor_get(v___x_1790_, 7);
v_snapshotTasks_1800_ = lean_ctor_get(v___x_1790_, 9);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1802_ = v___x_1790_;
v_isShared_1803_ = v_isSharedCheck_1822_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_snapshotTasks_1800_);
lean_inc(v_infoState_1791_);
lean_inc(v_messages_1799_);
lean_inc(v_recordedDeps_1798_);
lean_inc(v_cache_1797_);
lean_inc(v_traceState_1796_);
lean_inc(v_auxDeclNGen_1795_);
lean_inc(v_ngen_1794_);
lean_inc(v_nextMacroScope_1793_);
lean_inc(v_env_1792_);
lean_dec(v___x_1790_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1822_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
uint8_t v_enabled_1804_; lean_object* v_assignment_1805_; lean_object* v_lazyAssignment_1806_; lean_object* v_trees_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1821_; 
v_enabled_1804_ = lean_ctor_get_uint8(v_infoState_1791_, sizeof(void*)*3);
v_assignment_1805_ = lean_ctor_get(v_infoState_1791_, 0);
v_lazyAssignment_1806_ = lean_ctor_get(v_infoState_1791_, 1);
v_trees_1807_ = lean_ctor_get(v_infoState_1791_, 2);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_infoState_1791_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1809_ = v_infoState_1791_;
v_isShared_1810_ = v_isSharedCheck_1821_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_trees_1807_);
lean_inc(v_lazyAssignment_1806_);
lean_inc(v_assignment_1805_);
lean_dec(v_infoState_1791_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1821_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = l_Lean_PersistentArray_push___redArg(v_trees_1807_, v_t_1782_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 2, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_assignment_1805_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_lazyAssignment_1806_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v___x_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*3, v_enabled_1804_);
v___x_1814_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 8, v___x_1814_);
v___x_1816_ = v___x_1802_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_env_1792_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_nextMacroScope_1793_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_ngen_1794_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_auxDeclNGen_1795_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_traceState_1796_);
lean_ctor_set(v_reuseFailAlloc_1819_, 5, v_cache_1797_);
lean_ctor_set(v_reuseFailAlloc_1819_, 6, v_recordedDeps_1798_);
lean_ctor_set(v_reuseFailAlloc_1819_, 7, v_messages_1799_);
lean_ctor_set(v_reuseFailAlloc_1819_, 8, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1819_, 9, v_snapshotTasks_1800_);
v___x_1816_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_st_ref_put(v___y_1783_, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1811_);
return v___x_1818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1823_, v___y_1824_);
lean_dec(v___y_1824_);
return v_res_1826_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_unsigned_to_nat(32u);
v___x_1828_ = lean_mk_empty_array_with_capacity(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1830_ = ((size_t)5ULL);
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_unsigned_to_nat(32u);
v___x_1833_ = lean_mk_empty_array_with_capacity(v___x_1832_);
v___x_1834_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
v___x_1835_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___x_1833_);
lean_ctor_set(v___x_1835_, 2, v___x_1831_);
lean_ctor_set(v___x_1835_, 3, v___x_1831_);
lean_ctor_set_usize(v___x_1835_, 4, v___x_1830_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object* v_t_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v_infoState_1845_; uint8_t v_enabled_1846_; 
v___x_1844_ = lean_st_ref_get(v___y_1842_);
v_infoState_1845_ = lean_ctor_get(v___x_1844_, 8);
lean_inc_ref(v_infoState_1845_);
lean_dec(v___x_1844_);
v_enabled_1846_ = lean_ctor_get_uint8(v_infoState_1845_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1845_);
if (v_enabled_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref(v_t_1836_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
v___x_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_t_1836_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_1850_, v___y_1842_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object* v_t_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object* v_stx_1861_, lean_object* v_n_1862_, lean_object* v_expectedType_x3f_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_1862_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = lean_box(0);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_stx_1861_);
v___x_1875_ = l_Lean_LocalContext_empty;
v___x_1876_ = 0;
v___x_1877_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1877_, 0, v___x_1874_);
lean_ctor_set(v___x_1877_, 1, v___x_1875_);
lean_ctor_set(v___x_1877_, 2, v_expectedType_x3f_1863_);
lean_ctor_set(v___x_1877_, 3, v_a_1872_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*4, v___x_1876_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*4 + 1, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1878_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1879_;
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_expectedType_x3f_1863_);
lean_dec(v_stx_1861_);
v_a_1880_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1871_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1871_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object* v_stx_1888_, lean_object* v_n_1889_, lean_object* v_expectedType_x3f_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1888_, v_n_1889_, v_expectedType_x3f_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object* v_item_1899_, lean_object* v_projFn_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v_infoState_1909_; uint8_t v_enabled_1910_; 
v___x_1908_ = lean_st_ref_get(v_a_1906_);
v_infoState_1909_ = lean_ctor_get(v___x_1908_, 8);
lean_inc_ref(v_infoState_1909_);
lean_dec(v___x_1908_);
v_enabled_1910_ = lean_ctor_get_uint8(v_infoState_1909_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1909_);
if (v_enabled_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec(v_projFn_1900_);
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; lean_object* v_env_1914_; uint8_t v___x_1915_; 
v___x_1913_ = lean_st_ref_get(v_a_1906_);
v_env_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_env_1914_);
lean_dec(v___x_1913_);
lean_inc(v_projFn_1900_);
v___x_1915_ = l_Lean_Environment_contains(v_env_1914_, v_projFn_1900_, v_enabled_1910_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_projFn_1900_);
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1899_);
v___x_1919_ = lean_box(0);
v___x_1920_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_1918_, v_projFn_1900_, v___x_1919_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object* v_item_1921_, lean_object* v_projFn_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1921_, v_projFn_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec_ref(v_item_1921_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object* v_t_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1931_, v___y_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1949_, lean_object* v_constName_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_constName_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1959_, v_constName_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_1969_, lean_object* v_ref_1970_, lean_object* v_constName_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1970_, v_constName_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_1980_, lean_object* v_ref_1981_, lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_1980_, v_ref_1981_, v_constName_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v_ref_1981_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1991_, lean_object* v_ref_1992_, lean_object* v_msg_1993_, lean_object* v_declHint_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1992_, v_msg_1993_, v_declHint_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_ref_2004_, lean_object* v_msg_2005_, lean_object* v_declHint_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2003_, v_ref_2004_, v_msg_2005_, v_declHint_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v_ref_2004_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2015_, lean_object* v_declHint_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2015_, v_declHint_2016_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2025_, lean_object* v_declHint_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2025_, v_declHint_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object* v_info_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_info_2035_);
v___x_2044_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_2043_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(lean_object* v_info_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2053_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2056_ = lean_box(1);
v___x_2057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2058_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_2059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___x_2057_);
lean_ctor_set(v___x_2059_, 2, v___x_2056_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object* v_item_2060_, lean_object* v_structName_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2069_; lean_object* v_infoState_2070_; uint8_t v_enabled_2071_; 
v___x_2069_ = lean_st_ref_get(v_a_2067_);
v_infoState_2070_ = lean_ctor_get(v___x_2069_, 8);
lean_inc_ref(v_infoState_2070_);
lean_dec(v___x_2069_);
v_enabled_2071_ = lean_ctor_get_uint8(v_infoState_2070_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2070_);
if (v_enabled_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_structName_2061_);
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; lean_object* v_env_2075_; uint8_t v___x_2076_; 
v___x_2074_ = lean_st_ref_get(v_a_2067_);
v_env_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc_ref(v_env_2075_);
lean_dec(v___x_2074_);
lean_inc(v_structName_2061_);
v___x_2076_ = l_Lean_Environment_contains(v_env_2075_, v_structName_2061_, v_enabled_2071_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v_structName_2061_);
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2079_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_2060_);
v___x_2080_ = l_Lean_Syntax_getId(v___x_2079_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
v___x_2082_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2079_);
lean_ctor_set(v___x_2083_, 1, v___x_2081_);
lean_ctor_set(v___x_2083_, 2, v___x_2082_);
lean_ctor_set(v___x_2083_, 3, v_structName_2061_);
v___x_2084_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2083_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object* v_item_2085_, lean_object* v_structName_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2085_, v_structName_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec_ref(v_item_2085_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object* v_cfg_2095_, lean_object* v_withRef_2096_, lean_object* v___x_2097_, lean_object* v_oldRef_2098_){
_start:
{
lean_object* v_ref_2099_; lean_object* v___x_2100_; 
v_ref_2099_ = l_Lean_replaceRef(v_cfg_2095_, v_oldRef_2098_);
v___x_2100_ = lean_apply_3(v_withRef_2096_, lean_box(0), v_ref_2099_, v___x_2097_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object* v_cfg_2101_, lean_object* v_withRef_2102_, lean_object* v___x_2103_, lean_object* v_oldRef_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(v_cfg_2101_, v_withRef_2102_, v___x_2103_, v_oldRef_2104_);
lean_dec(v_oldRef_2104_);
lean_dec(v_cfg_2101_);
return v_res_2105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t v_x_2106_){
_start:
{
uint32_t v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = 46;
v___x_2108_ = lean_uint32_dec_eq(v_x_2106_, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object* v_x_2109_){
_start:
{
uint32_t v_x_877__boxed_2110_; uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_x_877__boxed_2110_ = lean_unbox_uint32(v_x_2109_);
lean_dec(v_x_2109_);
v_res_2111_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_877__boxed_2110_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object* v___f_2113_, lean_object* v_s_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2113_);
v___x_2122_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2114_, v___x_2121_, v___y_2115_, lean_box(0), lean_box(0), v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object* v___f_2124_, lean_object* v_si_2125_, lean_object* v_val_2126_){
_start:
{
lean_object* v___y_2128_; lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___f_2134_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0));
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = lean_string_utf8_byte_size(v_val_2126_);
lean_inc_ref(v_val_2126_);
v___x_2137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2137_, 0, v_val_2126_);
lean_ctor_set(v___x_2137_, 1, v___x_2135_);
lean_ctor_set(v___x_2137_, 2, v___x_2136_);
v___x_2138_ = l_String_Slice_contains___redArg(v___f_2124_, v___x_2137_, v___f_2134_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_box(0);
lean_inc_ref(v_val_2126_);
v___x_2140_ = l_Lean_Name_str___override(v___x_2139_, v_val_2126_);
v___y_2128_ = v___x_2140_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2141_; 
lean_inc_ref(v_val_2126_);
v___x_2141_ = l_String_toName(v_val_2126_);
v___y_2128_ = v___x_2141_;
goto v___jp_2127_;
}
v___jp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_string_utf8_byte_size(v_val_2126_);
v___x_2131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2131_, 0, v_val_2126_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
lean_ctor_set(v___x_2131_, 2, v___x_2130_);
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2133_, 0, v_si_2125_);
lean_ctor_set(v___x_2133_, 1, v___x_2131_);
lean_ctor_set(v___x_2133_, 2, v___y_2128_);
lean_ctor_set(v___x_2133_, 3, v___x_2132_);
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object* v_atomAsIdent_2142_, lean_object* v_stx_2143_){
_start:
{
switch(lean_obj_tag(v_stx_2143_))
{
case 3:
{
lean_object* v___x_2144_; 
lean_dec_ref(v_atomAsIdent_2142_);
v___x_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_stx_2143_);
return v___x_2144_;
}
case 2:
{
lean_object* v_info_2145_; lean_object* v_val_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_info_2145_ = lean_ctor_get(v_stx_2143_, 0);
lean_inc(v_info_2145_);
v_val_2146_ = lean_ctor_get(v_stx_2143_, 1);
lean_inc_ref(v_val_2146_);
lean_dec_ref_known(v_stx_2143_, 2);
v___x_2147_ = lean_apply_2(v_atomAsIdent_2142_, v_info_2145_, v_val_2146_);
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
default: 
{
lean_object* v___x_2149_; 
lean_dec(v_stx_2143_);
lean_dec_ref(v_atomAsIdent_2142_);
v___x_2149_ = lean_box(0);
return v___x_2149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_init_2175_, lean_object* v_cfgs_2176_, lean_object* v_k_2177_, lean_object* v_onErr_2178_){
_start:
{
lean_object* v_toApplicative_2179_; lean_object* v_toPure_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_toApplicative_2179_ = lean_ctor_get(v_inst_2173_, 0);
v_toPure_2180_ = lean_ctor_get(v_toApplicative_2179_, 1);
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_array_get_size(v_cfgs_2176_);
v___x_2183_ = lean_nat_dec_lt(v___x_2181_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
lean_inc(v_toPure_2180_);
lean_dec(v_onErr_2178_);
lean_dec(v_k_2177_);
lean_dec_ref(v_cfgs_2176_);
lean_dec_ref(v_inst_2174_);
lean_dec_ref(v_inst_2173_);
v___x_2184_ = lean_apply_2(v_toPure_2180_, lean_box(0), v_init_2175_);
return v___x_2184_;
}
else
{
lean_object* v___f_2185_; uint8_t v___x_2186_; 
lean_inc_ref(v_inst_2173_);
v___f_2185_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_2185_, 0, v_inst_2173_);
lean_closure_set(v___f_2185_, 1, v_inst_2174_);
lean_closure_set(v___f_2185_, 2, v_k_2177_);
lean_closure_set(v___f_2185_, 3, v_onErr_2178_);
v___x_2186_ = lean_nat_dec_le(v___x_2182_, v___x_2182_);
if (v___x_2186_ == 0)
{
if (v___x_2183_ == 0)
{
lean_object* v___x_2187_; 
lean_inc(v_toPure_2180_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_cfgs_2176_);
lean_dec_ref(v_inst_2173_);
v___x_2187_ = lean_apply_2(v_toPure_2180_, lean_box(0), v_init_2175_);
return v___x_2187_;
}
else
{
size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = lean_usize_of_nat(v___x_2182_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2173_, v___f_2185_, v_cfgs_2176_, v___x_2188_, v___x_2189_, v_init_2175_);
return v___x_2190_;
}
}
else
{
size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = ((size_t)0ULL);
v___x_2192_ = lean_usize_of_nat(v___x_2182_);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2173_, v___f_2185_, v_cfgs_2176_, v___x_2191_, v___x_2192_, v_init_2175_);
return v___x_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object* v_inst_2194_, lean_object* v_inst_2195_, lean_object* v_init_2196_, lean_object* v_cfg_2197_, lean_object* v_k_2198_, lean_object* v_onErr_2199_){
_start:
{
lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2197_);
v___x_2219_ = l_Lean_Syntax_isOfKind(v_cfg_2197_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = l_Lean_Syntax_getNumArgs(v_cfg_2197_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_nat_dec_eq(v___x_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___f_2223_; lean_object* v_atomAsIdent_2224_; uint8_t v___x_2225_; 
v___f_2223_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3));
v_atomAsIdent_2224_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4));
v___x_2225_ = lean_nat_dec_le(v___x_2221_, v___x_2220_);
if (v___x_2225_ == 0)
{
lean_dec(v___x_2220_);
if (lean_obj_tag(v_cfg_2197_) == 2)
{
lean_object* v_info_2226_; lean_object* v_val_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v_onErr_2199_);
lean_dec_ref(v_inst_2195_);
lean_dec_ref(v_inst_2194_);
v_info_2226_ = lean_ctor_get(v_cfg_2197_, 0);
v_val_2227_ = lean_ctor_get(v_cfg_2197_, 1);
lean_inc_ref(v_val_2227_);
lean_inc(v_info_2226_);
v___x_2228_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(v___f_2223_, v_info_2226_, v_val_2227_);
v___x_2229_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2230_ = l_Lean_mkCIdentFrom(v_cfg_2197_, v___x_2229_, v___x_2225_);
v___x_2231_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2232_ = l_Lean_TSyntax_getId(v___x_2228_);
v___x_2233_ = l_Lean_Name_eraseMacroScopes(v___x_2232_);
lean_dec(v___x_2232_);
v___x_2234_ = lean_box(0);
lean_inc(v___x_2228_);
v___x_2235_ = l_Lean_Syntax_identComponents(v___x_2228_, v___x_2234_);
v___x_2236_ = lean_box(0);
v___x_2237_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2237_, 0, v_cfg_2197_);
lean_ctor_set(v___x_2237_, 1, v___x_2228_);
lean_ctor_set(v___x_2237_, 2, v___x_2230_);
lean_ctor_set(v___x_2237_, 3, v___x_2231_);
lean_ctor_set(v___x_2237_, 4, v___x_2233_);
lean_ctor_set(v___x_2237_, 5, v___x_2235_);
lean_ctor_set(v___x_2237_, 6, v___x_2236_);
v___x_2238_ = lean_apply_2(v_k_2198_, v_init_2196_, v___x_2237_);
return v___x_2238_;
}
else
{
lean_dec(v_k_2198_);
goto v___jp_2211_;
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = l_Lean_Syntax_getArg(v_cfg_2197_, v___x_2239_);
if (lean_obj_tag(v___x_2240_) == 2)
{
lean_object* v_val_2241_; lean_object* v___y_2243_; uint8_t v_val_2244_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_val_2241_ = lean_ctor_get(v___x_2240_, 1);
v___x_2255_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2256_ = lean_string_dec_eq(v_val_2241_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2258_ = lean_string_dec_eq(v_val_2241_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
lean_inc_ref(v_val_2241_);
lean_dec_ref_known(v___x_2240_, 2);
v___x_2259_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2260_ = lean_string_dec_eq(v_val_2241_, v___x_2259_);
lean_dec_ref(v_val_2241_);
if (v___x_2260_ == 0)
{
lean_dec(v___x_2220_);
lean_dec(v_k_2198_);
goto v___jp_2211_;
}
else
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = lean_unsigned_to_nat(5u);
v___x_2262_ = lean_nat_dec_le(v___x_2220_, v___x_2261_);
lean_dec(v___x_2220_);
if (v___x_2262_ == 0)
{
lean_dec(v_k_2198_);
goto v___jp_2211_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = l_Lean_Syntax_getArg(v_cfg_2197_, v___x_2221_);
v___x_2264_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2224_, v___x_2263_);
if (lean_obj_tag(v___x_2264_) == 1)
{
lean_object* v_val_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec(v_onErr_2199_);
lean_dec_ref(v_inst_2195_);
lean_dec_ref(v_inst_2194_);
v_val_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc_n(v_val_2265_, 2);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = lean_unsigned_to_nat(3u);
v___x_2267_ = l_Lean_Syntax_getArg(v_cfg_2197_, v___x_2266_);
v___x_2268_ = lean_box(0);
v___x_2269_ = l_Lean_TSyntax_getId(v_val_2265_);
v___x_2270_ = l_Lean_Name_eraseMacroScopes(v___x_2269_);
lean_dec(v___x_2269_);
v___x_2271_ = l_Lean_Syntax_identComponents(v_val_2265_, v___x_2268_);
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2273_, 0, v_cfg_2197_);
lean_ctor_set(v___x_2273_, 1, v_val_2265_);
lean_ctor_set(v___x_2273_, 2, v___x_2267_);
lean_ctor_set(v___x_2273_, 3, v___x_2268_);
lean_ctor_set(v___x_2273_, 4, v___x_2270_);
lean_ctor_set(v___x_2273_, 5, v___x_2271_);
lean_ctor_set(v___x_2273_, 6, v___x_2272_);
v___x_2274_ = lean_apply_2(v_k_2198_, v_init_2196_, v___x_2273_);
return v___x_2274_;
}
else
{
lean_dec(v___x_2264_);
lean_dec(v_k_2198_);
goto v___jp_2211_;
}
}
}
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_box(v___x_2256_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
v___y_2243_ = v___x_2276_;
v_val_2244_ = v___x_2256_;
goto v___jp_2242_;
}
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_box(v___x_2225_);
v___x_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
v___y_2243_ = v___x_2278_;
v_val_2244_ = v___x_2225_;
goto v___jp_2242_;
}
v___jp_2242_:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(2u);
v___x_2246_ = lean_nat_dec_eq(v___x_2220_, v___x_2245_);
lean_dec(v___x_2220_);
if (v___x_2246_ == 0)
{
lean_dec(v___y_2243_);
lean_dec_ref_known(v___x_2240_, 2);
lean_dec(v_k_2198_);
goto v___jp_2211_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = l_Lean_Syntax_getArg(v_cfg_2197_, v___x_2221_);
v___x_2248_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2224_, v___x_2247_);
if (lean_obj_tag(v___x_2248_) == 1)
{
lean_dec(v_onErr_2199_);
lean_dec_ref(v_inst_2195_);
lean_dec_ref(v_inst_2194_);
if (v_val_2244_ == 0)
{
lean_object* v_val_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_val_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2250_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2251_ = l_Lean_mkCIdentFrom(v___x_2240_, v___x_2250_, v_val_2244_);
lean_dec_ref_known(v___x_2240_, 2);
v___y_2201_ = v_val_2249_;
v___y_2202_ = v___y_2243_;
v___y_2203_ = v___x_2251_;
goto v___jp_2200_;
}
else
{
lean_object* v_val_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_val_2252_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_val_2252_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2253_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2254_ = l_Lean_mkCIdentFrom(v___x_2240_, v___x_2253_, v___x_2222_);
lean_dec_ref_known(v___x_2240_, 2);
v___y_2201_ = v_val_2252_;
v___y_2202_ = v___y_2243_;
v___y_2203_ = v___x_2254_;
goto v___jp_2200_;
}
}
else
{
lean_dec(v___x_2248_);
lean_dec(v___y_2243_);
lean_dec_ref_known(v___x_2240_, 2);
lean_dec(v_k_2198_);
goto v___jp_2211_;
}
}
}
}
else
{
lean_dec(v___x_2240_);
lean_dec(v___x_2220_);
lean_dec(v_k_2198_);
goto v___jp_2211_;
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec(v___x_2220_);
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = l_Lean_Syntax_getArg(v_cfg_2197_, v___x_2279_);
lean_dec(v_cfg_2197_);
v_cfg_2197_ = v___x_2280_;
goto _start;
}
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = l_Lean_Syntax_getArgs(v_cfg_2197_);
lean_dec(v_cfg_2197_);
v___x_2283_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2194_, v_inst_2195_, v_init_2196_, v___x_2282_, v_k_2198_, v_onErr_2199_);
return v___x_2283_;
}
v___jp_2200_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2204_ = l_Lean_TSyntax_getId(v___y_2201_);
v___x_2205_ = l_Lean_Name_eraseMacroScopes(v___x_2204_);
lean_dec(v___x_2204_);
v___x_2206_ = lean_box(0);
lean_inc(v___y_2201_);
v___x_2207_ = l_Lean_Syntax_identComponents(v___y_2201_, v___x_2206_);
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2209_, 0, v_cfg_2197_);
lean_ctor_set(v___x_2209_, 1, v___y_2201_);
lean_ctor_set(v___x_2209_, 2, v___y_2203_);
lean_ctor_set(v___x_2209_, 3, v___y_2202_);
lean_ctor_set(v___x_2209_, 4, v___x_2205_);
lean_ctor_set(v___x_2209_, 5, v___x_2207_);
lean_ctor_set(v___x_2209_, 6, v___x_2208_);
v___x_2210_ = lean_apply_2(v_k_2198_, v_init_2196_, v___x_2209_);
return v___x_2210_;
}
v___jp_2211_:
{
lean_object* v_toBind_2212_; lean_object* v_getRef_2213_; lean_object* v_withRef_2214_; lean_object* v___x_2215_; lean_object* v___f_2216_; lean_object* v___x_2217_; 
v_toBind_2212_ = lean_ctor_get(v_inst_2194_, 1);
lean_inc(v_toBind_2212_);
lean_dec_ref(v_inst_2194_);
v_getRef_2213_ = lean_ctor_get(v_inst_2195_, 0);
lean_inc(v_getRef_2213_);
v_withRef_2214_ = lean_ctor_get(v_inst_2195_, 1);
lean_inc(v_withRef_2214_);
lean_dec_ref(v_inst_2195_);
lean_inc(v_cfg_2197_);
v___x_2215_ = lean_apply_2(v_onErr_2199_, v_init_2196_, v_cfg_2197_);
v___f_2216_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2216_, 0, v_cfg_2197_);
lean_closure_set(v___f_2216_, 1, v_withRef_2214_);
lean_closure_set(v___f_2216_, 2, v___x_2215_);
v___x_2217_ = lean_apply_4(v_toBind_2212_, lean_box(0), lean_box(0), v_getRef_2213_, v___f_2216_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_k_2286_, lean_object* v_onErr_2287_, lean_object* v_x_2288_, lean_object* v_cfg_x27_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2284_, v_inst_2285_, v_x_2288_, v_cfg_x27_2289_, v_k_2286_, v_onErr_2287_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object* v_00_u03b1_2291_, lean_object* v_m_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_init_2295_, lean_object* v_cfg_2296_, lean_object* v_k_2297_, lean_object* v_onErr_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2293_, v_inst_2294_, v_init_2295_, v_cfg_2296_, v_k_2297_, v_onErr_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object* v_00_u03b1_2300_, lean_object* v_m_2301_, lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_init_2304_, lean_object* v_cfgs_2305_, lean_object* v_k_2306_, lean_object* v_onErr_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2302_, v_inst_2303_, v_init_2304_, v_cfgs_2305_, v_k_2306_, v_onErr_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_2317_, uint8_t v___y_2318_, lean_object* v_x_2319_){
_start:
{
if (lean_obj_tag(v_x_2319_) == 1)
{
lean_object* v_pre_2320_; 
v_pre_2320_ = lean_ctor_get(v_x_2319_, 0);
switch(lean_obj_tag(v_pre_2320_))
{
case 1:
{
lean_object* v_pre_2321_; 
v_pre_2321_ = lean_ctor_get(v_pre_2320_, 0);
switch(lean_obj_tag(v_pre_2321_))
{
case 0:
{
lean_object* v_str_2322_; lean_object* v_str_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_str_2322_ = lean_ctor_get(v_x_2319_, 1);
v_str_2323_ = lean_ctor_get(v_pre_2320_, 1);
v___x_2324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_2325_ = lean_string_dec_eq(v_str_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_2327_ = lean_string_dec_eq(v_str_2323_, v___x_2326_);
if (v___x_2327_ == 0)
{
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_2329_ = lean_string_dec_eq(v_str_2322_, v___x_2328_);
if (v___x_2329_ == 0)
{
return v___x_2329_;
}
else
{
return v_suppressElabErrors_2317_;
}
}
}
else
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_2331_ = lean_string_dec_eq(v_str_2322_, v___x_2330_);
if (v___x_2331_ == 0)
{
return v___x_2331_;
}
else
{
return v_suppressElabErrors_2317_;
}
}
}
case 1:
{
lean_object* v_pre_2332_; 
v_pre_2332_ = lean_ctor_get(v_pre_2321_, 0);
if (lean_obj_tag(v_pre_2332_) == 0)
{
lean_object* v_str_2333_; lean_object* v_str_2334_; lean_object* v_str_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_str_2333_ = lean_ctor_get(v_x_2319_, 1);
v_str_2334_ = lean_ctor_get(v_pre_2320_, 1);
v_str_2335_ = lean_ctor_get(v_pre_2321_, 1);
v___x_2336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_2337_ = lean_string_dec_eq(v_str_2335_, v___x_2336_);
if (v___x_2337_ == 0)
{
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_2339_ = lean_string_dec_eq(v_str_2334_, v___x_2338_);
if (v___x_2339_ == 0)
{
return v___x_2339_;
}
else
{
lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_2341_ = lean_string_dec_eq(v_str_2333_, v___x_2340_);
if (v___x_2341_ == 0)
{
return v___x_2341_;
}
else
{
return v_suppressElabErrors_2317_;
}
}
}
}
else
{
return v___y_2318_;
}
}
default: 
{
return v___y_2318_;
}
}
}
case 0:
{
lean_object* v_str_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_str_2342_ = lean_ctor_get(v_x_2319_, 1);
v___x_2343_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_2344_ = lean_string_dec_eq(v_str_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
return v___x_2344_;
}
else
{
return v_suppressElabErrors_2317_;
}
}
default: 
{
return v___y_2318_;
}
}
}
else
{
return v___y_2318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2345_, lean_object* v___y_2346_, lean_object* v_x_2347_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2348_; uint8_t v___y_6094__boxed_2349_; uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_suppressElabErrors_boxed_2348_ = lean_unbox(v_suppressElabErrors_2345_);
v___y_6094__boxed_2349_ = lean_unbox(v___y_2346_);
v_res_2350_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_2348_, v___y_6094__boxed_2349_, v_x_2347_);
lean_dec(v_x_2347_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2352_, lean_object* v_msgData_2353_, uint8_t v_severity_2354_, uint8_t v_isSilent_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v_toCold_2369_; lean_object* v___y_2370_; lean_object* v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2402_; uint8_t v___y_2403_; uint8_t v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2426_; lean_object* v___y_2427_; uint8_t v___y_2428_; lean_object* v___y_2429_; uint8_t v___y_2430_; uint8_t v___y_2431_; lean_object* v___y_2432_; uint8_t v___y_2436_; uint8_t v___y_2437_; uint8_t v___y_2438_; uint8_t v___x_2449_; uint8_t v___y_2451_; uint8_t v___y_2452_; uint8_t v___y_2453_; uint8_t v___y_2455_; uint8_t v___x_2463_; 
v___x_2449_ = 2;
v___x_2463_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2354_, v___x_2449_);
if (v___x_2463_ == 0)
{
v___y_2455_ = v___x_2463_;
goto v___jp_2454_;
}
else
{
uint8_t v___x_2464_; 
lean_inc_ref(v_msgData_2353_);
v___x_2464_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2353_);
v___y_2455_ = v___x_2464_;
goto v___jp_2454_;
}
v___jp_2361_:
{
lean_object* v_currNamespace_2371_; lean_object* v_openDecls_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_env_2377_; lean_object* v_nextMacroScope_2378_; lean_object* v_ngen_2379_; lean_object* v_auxDeclNGen_2380_; lean_object* v_traceState_2381_; lean_object* v_cache_2382_; lean_object* v_recordedDeps_2383_; lean_object* v_messages_2384_; lean_object* v_infoState_2385_; lean_object* v_snapshotTasks_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2397_; 
v_currNamespace_2371_ = lean_ctor_get(v_toCold_2369_, 4);
v_openDecls_2372_ = lean_ctor_get(v_toCold_2369_, 5);
lean_inc(v_openDecls_2372_);
lean_inc(v_currNamespace_2371_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_currNamespace_2371_);
lean_ctor_set(v___x_2373_, 1, v_openDecls_2372_);
v___x_2374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v___y_2363_);
lean_inc_ref(v___y_2367_);
lean_inc_ref(v___y_2368_);
v___x_2375_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2375_, 0, v___y_2368_);
lean_ctor_set(v___x_2375_, 1, v___y_2366_);
lean_ctor_set(v___x_2375_, 2, v___y_2364_);
lean_ctor_set(v___x_2375_, 3, v___y_2367_);
lean_ctor_set(v___x_2375_, 4, v___x_2374_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*5, v___y_2362_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*5 + 1, v___y_2365_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*5 + 2, v_isSilent_2355_);
v___x_2376_ = lean_st_ref_take(v___y_2370_);
v_env_2377_ = lean_ctor_get(v___x_2376_, 0);
v_nextMacroScope_2378_ = lean_ctor_get(v___x_2376_, 1);
v_ngen_2379_ = lean_ctor_get(v___x_2376_, 2);
v_auxDeclNGen_2380_ = lean_ctor_get(v___x_2376_, 3);
v_traceState_2381_ = lean_ctor_get(v___x_2376_, 4);
v_cache_2382_ = lean_ctor_get(v___x_2376_, 5);
v_recordedDeps_2383_ = lean_ctor_get(v___x_2376_, 6);
v_messages_2384_ = lean_ctor_get(v___x_2376_, 7);
v_infoState_2385_ = lean_ctor_get(v___x_2376_, 8);
v_snapshotTasks_2386_ = lean_ctor_get(v___x_2376_, 9);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2388_ = v___x_2376_;
v_isShared_2389_ = v_isSharedCheck_2397_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snapshotTasks_2386_);
lean_inc(v_infoState_2385_);
lean_inc(v_messages_2384_);
lean_inc(v_recordedDeps_2383_);
lean_inc(v_cache_2382_);
lean_inc(v_traceState_2381_);
lean_inc(v_auxDeclNGen_2380_);
lean_inc(v_ngen_2379_);
lean_inc(v_nextMacroScope_2378_);
lean_inc(v_env_2377_);
lean_dec(v___x_2376_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2397_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2390_ = lean_box(0);
v___x_2391_ = l_Lean_MessageLog_add(v___x_2375_, v_messages_2384_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 7, v___x_2391_);
v___x_2393_ = v___x_2388_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_env_2377_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_nextMacroScope_2378_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_ngen_2379_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_auxDeclNGen_2380_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v_traceState_2381_);
lean_ctor_set(v_reuseFailAlloc_2396_, 5, v_cache_2382_);
lean_ctor_set(v_reuseFailAlloc_2396_, 6, v_recordedDeps_2383_);
lean_ctor_set(v_reuseFailAlloc_2396_, 7, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2396_, 8, v_infoState_2385_);
lean_ctor_set(v_reuseFailAlloc_2396_, 9, v_snapshotTasks_2386_);
v___x_2393_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_st_ref_put(v___y_2370_, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2390_);
return v___x_2395_;
}
}
}
v___jp_2398_:
{
lean_object* v_fileName_2407_; lean_object* v_fileMap_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2424_; 
v_fileName_2407_ = lean_ctor_get(v___y_2402_, 0);
v_fileMap_2408_ = lean_ctor_get(v___y_2402_, 1);
v___x_2409_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2353_);
v___x_2410_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_2409_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2424_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2424_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_inc_ref_n(v_fileMap_2408_, 2);
v___x_2415_ = l_Lean_FileMap_toPosition(v_fileMap_2408_, v___y_2405_);
lean_dec(v___y_2405_);
v___x_2416_ = l_Lean_FileMap_toPosition(v_fileMap_2408_, v___y_2406_);
lean_dec(v___y_2406_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
v___x_2418_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
if (v___y_2404_ == 0)
{
lean_del_object(v___x_2413_);
lean_dec_ref(v___y_2400_);
v___y_2362_ = v___y_2401_;
v___y_2363_ = v_a_2411_;
v___y_2364_ = v___x_2417_;
v___y_2365_ = v___y_2403_;
v___y_2366_ = v___x_2415_;
v___y_2367_ = v___x_2418_;
v___y_2368_ = v_fileName_2407_;
v_toCold_2369_ = v___y_2399_;
v___y_2370_ = v___y_2359_;
goto v___jp_2361_;
}
else
{
uint8_t v___x_2419_; 
lean_inc(v_a_2411_);
v___x_2419_ = l_Lean_MessageData_hasTag(v___y_2400_, v_a_2411_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
lean_dec_ref_known(v___x_2417_, 1);
lean_dec_ref(v___x_2415_);
lean_dec(v_a_2411_);
v___x_2420_ = lean_box(0);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2420_);
v___x_2422_ = v___x_2413_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
else
{
lean_del_object(v___x_2413_);
v___y_2362_ = v___y_2401_;
v___y_2363_ = v_a_2411_;
v___y_2364_ = v___x_2417_;
v___y_2365_ = v___y_2403_;
v___y_2366_ = v___x_2415_;
v___y_2367_ = v___x_2418_;
v___y_2368_ = v_fileName_2407_;
v_toCold_2369_ = v___y_2399_;
v___y_2370_ = v___y_2359_;
goto v___jp_2361_;
}
}
}
}
v___jp_2425_:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Syntax_getTailPos_x3f(v___y_2429_, v___y_2430_);
lean_dec(v___y_2429_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_inc(v___y_2432_);
v___y_2399_ = v___y_2426_;
v___y_2400_ = v___y_2427_;
v___y_2401_ = v___y_2430_;
v___y_2402_ = v___y_2426_;
v___y_2403_ = v___y_2431_;
v___y_2404_ = v___y_2428_;
v___y_2405_ = v___y_2432_;
v___y_2406_ = v___y_2432_;
goto v___jp_2398_;
}
else
{
lean_object* v_val_2434_; 
v_val_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v___y_2399_ = v___y_2426_;
v___y_2400_ = v___y_2427_;
v___y_2401_ = v___y_2430_;
v___y_2402_ = v___y_2426_;
v___y_2403_ = v___y_2431_;
v___y_2404_ = v___y_2428_;
v___y_2405_ = v___y_2432_;
v___y_2406_ = v_val_2434_;
goto v___jp_2398_;
}
}
v___jp_2435_:
{
lean_object* v_toCold_2439_; lean_object* v_ref_2440_; uint8_t v_suppressElabErrors_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v_ref_2445_; lean_object* v___x_2446_; 
v_toCold_2439_ = lean_ctor_get(v___y_2358_, 0);
v_ref_2440_ = lean_ctor_get(v___y_2358_, 2);
v_suppressElabErrors_2441_ = lean_ctor_get_uint8(v___y_2358_, sizeof(void*)*3 + 2);
v___x_2442_ = lean_box(v_suppressElabErrors_2441_);
v___x_2443_ = lean_box(v___y_2436_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2444_, 0, v___x_2442_);
lean_closure_set(v___f_2444_, 1, v___x_2443_);
v_ref_2445_ = l_Lean_replaceRef(v_ref_2352_, v_ref_2440_);
v___x_2446_ = l_Lean_Syntax_getPos_x3f(v_ref_2445_, v___y_2437_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_unsigned_to_nat(0u);
v___y_2426_ = v_toCold_2439_;
v___y_2427_ = v___f_2444_;
v___y_2428_ = v_suppressElabErrors_2441_;
v___y_2429_ = v_ref_2445_;
v___y_2430_ = v___y_2437_;
v___y_2431_ = v___y_2438_;
v___y_2432_ = v___x_2447_;
goto v___jp_2425_;
}
else
{
lean_object* v_val_2448_; 
v_val_2448_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v___x_2446_, 1);
v___y_2426_ = v_toCold_2439_;
v___y_2427_ = v___f_2444_;
v___y_2428_ = v_suppressElabErrors_2441_;
v___y_2429_ = v_ref_2445_;
v___y_2430_ = v___y_2437_;
v___y_2431_ = v___y_2438_;
v___y_2432_ = v_val_2448_;
goto v___jp_2425_;
}
}
v___jp_2450_:
{
if (v___y_2453_ == 0)
{
v___y_2436_ = v___y_2451_;
v___y_2437_ = v___y_2452_;
v___y_2438_ = v_severity_2354_;
goto v___jp_2435_;
}
else
{
v___y_2436_ = v___y_2451_;
v___y_2437_ = v___y_2452_;
v___y_2438_ = v___x_2449_;
goto v___jp_2435_;
}
}
v___jp_2454_:
{
if (v___y_2455_ == 0)
{
uint8_t v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = 1;
v___x_2457_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2354_, v___x_2456_);
if (v___x_2457_ == 0)
{
v___y_2451_ = v___y_2455_;
v___y_2452_ = v___y_2455_;
v___y_2453_ = v___x_2457_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2458_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2358_);
v___x_2459_ = l_Lean_warningAsError;
v___x_2460_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v___x_2458_, v___x_2459_);
lean_dec_ref(v___x_2458_);
v___y_2451_ = v___y_2455_;
v___y_2452_ = v___y_2455_;
v___y_2453_ = v___x_2460_;
goto v___jp_2450_;
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec_ref(v_msgData_2353_);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2465_, lean_object* v_msgData_2466_, lean_object* v_severity_2467_, lean_object* v_isSilent_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
uint8_t v_severity_boxed_2474_; uint8_t v_isSilent_boxed_2475_; lean_object* v_res_2476_; 
v_severity_boxed_2474_ = lean_unbox(v_severity_2467_);
v_isSilent_boxed_2475_ = lean_unbox(v_isSilent_2468_);
v_res_2476_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2465_, v_msgData_2466_, v_severity_boxed_2474_, v_isSilent_boxed_2475_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v_ref_2465_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object* v_msgData_2477_, uint8_t v_severity_2478_, uint8_t v_isSilent_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_ref_2487_; lean_object* v___x_2488_; 
v_ref_2487_ = lean_ctor_get(v___y_2484_, 2);
v___x_2488_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2487_, v_msgData_2477_, v_severity_2478_, v_isSilent_2479_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2489_, lean_object* v_severity_2490_, lean_object* v_isSilent_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v_severity_boxed_2499_; uint8_t v_isSilent_boxed_2500_; lean_object* v_res_2501_; 
v_severity_boxed_2499_ = lean_unbox(v_severity_2490_);
v_isSilent_boxed_2500_ = lean_unbox(v_isSilent_2491_);
v_res_2501_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2489_, v_severity_boxed_2499_, v_isSilent_boxed_2500_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object* v_msgData_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = 2;
v___x_2511_ = 0;
v___x_2512_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2502_, v___x_2510_, v___x_2511_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(lean_object* v_msgData_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object* v_ref_2522_, lean_object* v_msgData_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
uint8_t v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = 2;
v___x_2532_ = 0;
v___x_2533_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2522_, v_msgData_2523_, v___x_2531_, v___x_2532_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object* v_ref_2534_, lean_object* v_msgData_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2534_, v_msgData_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v_ref_2534_);
return v_res_2543_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object* v_ex_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
if (lean_obj_tag(v_ex_2547_) == 0)
{
lean_object* v_ref_2555_; lean_object* v_msg_2556_; lean_object* v___x_2557_; 
v_ref_2555_ = lean_ctor_get(v_ex_2547_, 0);
lean_inc(v_ref_2555_);
v_msg_2556_ = lean_ctor_get(v_ex_2547_, 1);
lean_inc_ref(v_msg_2556_);
lean_dec_ref_known(v_ex_2547_, 2);
v___x_2557_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2555_, v_msg_2556_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v_ref_2555_);
return v___x_2557_;
}
else
{
lean_object* v_id_2558_; uint8_t v___y_2560_; uint8_t v___x_2582_; 
v_id_2558_ = lean_ctor_get(v_ex_2547_, 0);
lean_inc(v_id_2558_);
v___x_2582_ = l_Lean_Elab_isAbortExceptionId(v_id_2558_);
if (v___x_2582_ == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = l_Lean_Exception_isInterrupt(v_ex_2547_);
lean_dec_ref_known(v_ex_2547_, 2);
v___y_2560_ = v___x_2583_;
goto v___jp_2559_;
}
else
{
lean_dec_ref_known(v_ex_2547_, 2);
v___y_2560_ = v___x_2582_;
goto v___jp_2559_;
}
v___jp_2559_:
{
if (v___y_2560_ == 0)
{
lean_object* v_ref_2561_; lean_object* v___x_2562_; 
v_ref_2561_ = lean_ctor_get(v___y_2552_, 2);
v___x_2562_ = l_Lean_InternalExceptionId_getName(v_id_2558_);
lean_dec(v_id_2558_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
v___x_2565_ = l_Lean_MessageData_ofName(v_a_2563_);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_2566_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2567_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2579_; 
v_a_2568_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2570_ = v___x_2562_;
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2562_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2572_ = lean_io_error_to_string(v_a_2568_);
v___x_2573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
v___x_2574_ = l_Lean_MessageData_ofFormat(v___x_2573_);
lean_inc(v_ref_2561_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_ref_2561_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2575_);
v___x_2577_ = v___x_2570_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec(v_id_2558_);
v___x_2580_ = lean_box(0);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object* v_ex_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object* v_a_2593_, lean_object* v_config_2594_, lean_object* v_____r_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_2593_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2611_; 
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v___x_2603_, 0);
lean_dec(v_unused_2612_);
v___x_2605_ = v___x_2603_;
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
else
{
lean_dec(v___x_2603_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_config_2594_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2607_);
v___x_2609_ = v___x_2605_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_config_2594_);
v_a_2613_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2603_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2603_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object* v_a_2621_, lean_object* v_config_2622_, lean_object* v_____r_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2621_, v_config_2622_, v_____r_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object* v___f_2632_, lean_object* v_x_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_box(0);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc(v___y_2635_);
lean_inc_ref(v___y_2634_);
v___x_2642_ = lean_apply_8(v___f_2632_, v___x_2641_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, lean_box(0));
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(lean_object* v___f_2643_, lean_object* v_x_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2643_, v_x_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec_ref(v_x_2644_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object* v_eval_2653_, lean_object* v_config_2654_, lean_object* v_item_2655_, uint8_t v_logExceptions_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v___y_2665_; lean_object* v___x_2683_; 
lean_inc(v_a_2662_);
lean_inc_ref(v_a_2661_);
lean_inc(v_a_2660_);
lean_inc_ref(v_a_2659_);
lean_inc(v_a_2658_);
lean_inc_ref(v_a_2657_);
lean_inc(v_config_2654_);
v___x_2683_ = lean_apply_9(v_eval_2653_, v_config_2654_, v_item_2655_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, lean_box(0));
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_dec(v_config_2654_);
return v___x_2683_;
}
else
{
lean_object* v_a_2684_; lean_object* v___f_2685_; uint8_t v___y_2687_; uint8_t v___x_2704_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc_n(v_a_2684_, 2);
lean_inc(v_config_2654_);
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2685_, 0, v_a_2684_);
lean_closure_set(v___f_2685_, 1, v_config_2654_);
v___x_2704_ = l_Lean_Exception_isInterrupt(v_a_2684_);
if (v___x_2704_ == 0)
{
uint8_t v___x_2705_; 
lean_inc(v_a_2684_);
v___x_2705_ = l_Lean_Exception_isRuntime(v_a_2684_);
v___y_2687_ = v___x_2705_;
goto v___jp_2686_;
}
else
{
v___y_2687_ = v___x_2704_;
goto v___jp_2686_;
}
v___jp_2686_:
{
if (v___y_2687_ == 0)
{
if (v_logExceptions_2656_ == 0)
{
lean_dec_ref(v___f_2685_);
lean_dec(v_a_2684_);
lean_dec(v_config_2654_);
return v___x_2683_;
}
else
{
lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2702_; 
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2683_, 0);
lean_dec(v_unused_2703_);
v___x_2689_ = v___x_2683_;
v_isShared_2690_ = v_isSharedCheck_2702_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v___x_2683_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2702_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
if (lean_obj_tag(v_a_2684_) == 1)
{
lean_object* v_extra_2691_; 
v_extra_2691_ = lean_ctor_get(v_a_2684_, 1);
if (lean_obj_tag(v_extra_2691_) == 0)
{
lean_object* v_id_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
lean_dec_ref(v___f_2685_);
v_id_2692_ = lean_ctor_get(v_a_2684_, 0);
v___x_2693_ = l_Lean_Elab_abortTermExceptionId;
v___x_2694_ = l_Lean_instBEqInternalExceptionId_beq(v_id_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_del_object(v___x_2689_);
v___x_2695_ = lean_box(0);
v___x_2696_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2684_, v_config_2654_, v___x_2695_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
v___y_2665_ = v___x_2696_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2698_; 
lean_dec_ref_known(v_a_2684_, 2);
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 0);
lean_ctor_set(v___x_2689_, 0, v_config_2654_);
v___x_2698_ = v___x_2689_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_config_2654_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v___x_2700_; 
lean_del_object(v___x_2689_);
lean_dec(v_config_2654_);
v___x_2700_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2685_, v_a_2684_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec_ref_known(v_a_2684_, 2);
v___y_2665_ = v___x_2700_;
goto v___jp_2664_;
}
}
else
{
lean_object* v___x_2701_; 
lean_del_object(v___x_2689_);
lean_dec(v_config_2654_);
v___x_2701_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2685_, v_a_2684_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2684_);
v___y_2665_ = v___x_2701_;
goto v___jp_2664_;
}
}
}
}
else
{
lean_dec_ref(v___f_2685_);
lean_dec(v_a_2684_);
lean_dec(v_config_2654_);
return v___x_2683_;
}
}
}
v___jp_2664_:
{
if (lean_obj_tag(v___y_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2674_; 
v_a_2666_ = lean_ctor_get(v___y_2665_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___y_2665_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2668_ = v___y_2665_;
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___y_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_a_2670_; lean_object* v___x_2672_; 
v_a_2670_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_a_2670_);
lean_dec(v_a_2666_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v_a_2670_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_a_2675_ = lean_ctor_get(v___y_2665_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___y_2665_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___y_2665_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___y_2665_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object* v_eval_2706_, lean_object* v_config_2707_, lean_object* v_item_2708_, lean_object* v_logExceptions_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
uint8_t v_logExceptions_boxed_2717_; lean_object* v_res_2718_; 
v_logExceptions_boxed_2717_ = lean_unbox(v_logExceptions_2709_);
v_res_2718_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2706_, v_config_2707_, v_item_2708_, v_logExceptions_boxed_2717_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object* v_00_u03b1_2719_, lean_object* v_eval_2720_, lean_object* v_config_2721_, lean_object* v_item_2722_, uint8_t v_logExceptions_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2720_, v_config_2721_, v_item_2722_, v_logExceptions_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_eval_2733_, lean_object* v_config_2734_, lean_object* v_item_2735_, lean_object* v_logExceptions_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
uint8_t v_logExceptions_boxed_2744_; lean_object* v_res_2745_; 
v_logExceptions_boxed_2744_ = lean_unbox(v_logExceptions_2736_);
v_res_2745_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(v_00_u03b1_2732_, v_eval_2733_, v_config_2734_, v_item_2735_, v_logExceptions_boxed_2744_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object* v_ref_2746_, lean_object* v_msgData_2747_, uint8_t v_severity_2748_, uint8_t v_isSilent_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2746_, v_msgData_2747_, v_severity_2748_, v_isSilent_2749_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2758_, lean_object* v_msgData_2759_, lean_object* v_severity_2760_, lean_object* v_isSilent_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
uint8_t v_severity_boxed_2769_; uint8_t v_isSilent_boxed_2770_; lean_object* v_res_2771_; 
v_severity_boxed_2769_ = lean_unbox(v_severity_2760_);
v_isSilent_boxed_2770_ = lean_unbox(v_isSilent_2761_);
v_res_2771_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2758_, v_msgData_2759_, v_severity_boxed_2769_, v_isSilent_boxed_2770_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v_ref_2758_);
return v_res_2771_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___x_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg(){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object* v_00_u03b1_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object* v_00_u03b1_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
return v_res_2797_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = l_Lean_Level_ofNat(v___x_2801_);
return v___x_2802_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2);
v___x_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2803_);
return v___x_2805_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3);
v___x_2807_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1));
v___x_2808_ = l_Lean_Expr_const___override(v___x_2807_, v___x_2806_);
return v___x_2808_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = lean_box(0);
v___x_2813_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6));
v___x_2814_ = l_Lean_Expr_const___override(v___x_2813_, v___x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object* v_cfg_2818_, lean_object* v_cfgItem_2819_, lean_object* v_cfgType_x3f_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; 
if (lean_obj_tag(v_cfgType_x3f_2820_) == 1)
{
lean_object* v_val_2838_; lean_object* v___x_2839_; lean_object* v_infoState_2840_; uint8_t v_enabled_2841_; 
v_val_2838_ = lean_ctor_get(v_cfgType_x3f_2820_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v_cfgType_x3f_2820_, 1);
v___x_2839_ = lean_st_ref_get(v_a_2826_);
v_infoState_2840_ = lean_ctor_get(v___x_2839_, 8);
lean_inc_ref(v_infoState_2840_);
lean_dec(v___x_2839_);
v_enabled_2841_ = lean_ctor_get_uint8(v_infoState_2840_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2840_);
if (v_enabled_2841_ == 0)
{
lean_dec(v_val_2838_);
v___y_2829_ = v_a_2821_;
v___y_2830_ = v_a_2822_;
v___y_2831_ = v_a_2823_;
v___y_2832_ = v_a_2824_;
v___y_2833_ = v_a_2825_;
v___y_2834_ = v_a_2826_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___y_2845_; uint8_t v___x_2857_; 
v___x_2842_ = lean_unsigned_to_nat(0u);
v___x_2843_ = l_Lean_Syntax_getArg(v_cfgItem_2819_, v___x_2842_);
v___x_2857_ = l_Lean_Syntax_isAtom(v___x_2843_);
if (v___x_2857_ == 0)
{
v___y_2845_ = v___x_2857_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = l_Lean_Syntax_getArg(v_cfgItem_2819_, v___x_2858_);
v___x_2860_ = l_Lean_Syntax_isMissing(v___x_2859_);
lean_dec(v___x_2859_);
v___y_2845_ = v___x_2860_;
goto v___jp_2844_;
}
v___jp_2844_:
{
if (v___y_2845_ == 0)
{
lean_dec(v___x_2843_);
lean_dec(v_val_2838_);
v___y_2829_ = v_a_2821_;
v___y_2830_ = v_a_2822_;
v___y_2831_ = v_a_2823_;
v___y_2832_ = v_a_2824_;
v___y_2833_ = v_a_2825_;
v___y_2834_ = v_a_2826_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2846_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
v___x_2847_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
v___x_2848_ = l_Lean_mkAppB(v___x_2846_, v_val_2838_, v___x_2847_);
v___x_2849_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9));
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2843_);
v___x_2851_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2852_ = lean_box(0);
v___x_2853_ = 0;
v___x_2854_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2854_, 0, v___x_2850_);
lean_ctor_set(v___x_2854_, 1, v___x_2851_);
lean_ctor_set(v___x_2854_, 2, v___x_2852_);
lean_ctor_set(v___x_2854_, 3, v___x_2848_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*4, v___x_2853_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*4 + 1, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2852_);
v___x_2856_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2855_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
lean_dec_ref(v___x_2856_);
v___y_2829_ = v_a_2821_;
v___y_2830_ = v_a_2822_;
v___y_2831_ = v_a_2823_;
v___y_2832_ = v_a_2824_;
v___y_2833_ = v_a_2825_;
v___y_2834_ = v_a_2826_;
goto v___jp_2828_;
}
}
}
}
else
{
lean_dec(v_cfgType_x3f_2820_);
v___y_2829_ = v_a_2821_;
v___y_2830_ = v_a_2822_;
v___y_2831_ = v_a_2823_;
v___y_2832_ = v_a_2824_;
v___y_2833_ = v_a_2825_;
v___y_2834_ = v_a_2826_;
goto v___jp_2828_;
}
v___jp_2828_:
{
uint8_t v___x_2835_; 
v___x_2835_ = l_Lean_Syntax_hasMissing(v_cfgItem_2819_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; 
lean_dec(v_cfg_2818_);
v___x_2836_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; 
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v_cfg_2818_);
return v___x_2837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object* v_cfg_2861_, lean_object* v_cfgItem_2862_, lean_object* v_cfgType_x3f_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2861_, v_cfgItem_2862_, v_cfgType_x3f_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_cfgItem_2862_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object* v_00_u03b1_2872_, lean_object* v_cfg_2873_, lean_object* v_cfgItem_2874_, lean_object* v_cfgType_x3f_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2873_, v_cfgItem_2874_, v_cfgType_x3f_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_cfg_2885_, lean_object* v_cfgItem_2886_, lean_object* v_cfgType_x3f_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(v_00_u03b1_2884_, v_cfg_2885_, v_cfgItem_2886_, v_cfgType_x3f_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_cfgItem_2886_);
return v_res_2895_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_s_2896_, lean_object* v_a_2897_, uint8_t v_b_2898_){
_start:
{
lean_object* v_str_2899_; lean_object* v_startInclusive_2900_; lean_object* v_endExclusive_2901_; lean_object* v___x_2902_; uint8_t v_decide_2903_; 
v_str_2899_ = lean_ctor_get(v_s_2896_, 0);
v_startInclusive_2900_ = lean_ctor_get(v_s_2896_, 1);
v_endExclusive_2901_ = lean_ctor_get(v_s_2896_, 2);
v___x_2902_ = lean_nat_sub(v_endExclusive_2901_, v_startInclusive_2900_);
v_decide_2903_ = lean_nat_dec_eq(v_a_2897_, v___x_2902_);
lean_dec(v___x_2902_);
if (v_decide_2903_ == 0)
{
lean_object* v___x_2904_; uint32_t v___x_2905_; uint32_t v___x_2906_; uint8_t v___x_2907_; 
v___x_2904_ = lean_nat_add(v_startInclusive_2900_, v_a_2897_);
lean_dec(v_a_2897_);
v___x_2905_ = lean_string_utf8_get_fast(v_str_2899_, v___x_2904_);
v___x_2906_ = 46;
v___x_2907_ = lean_uint32_dec_eq(v___x_2905_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_string_utf8_next_fast(v_str_2899_, v___x_2904_);
lean_dec(v___x_2904_);
v___x_2909_ = lean_nat_sub(v___x_2908_, v_startInclusive_2900_);
v_a_2897_ = v___x_2909_;
v_b_2898_ = v___x_2907_;
goto _start;
}
else
{
lean_dec(v___x_2904_);
return v___x_2907_;
}
}
else
{
lean_dec(v_a_2897_);
return v_b_2898_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_s_2911_, lean_object* v_a_2912_, lean_object* v_b_2913_){
_start:
{
uint8_t v_b_boxed_2914_; uint8_t v_res_2915_; lean_object* v_r_2916_; 
v_b_boxed_2914_ = lean_unbox(v_b_2913_);
v_res_2915_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2911_, v_a_2912_, v_b_boxed_2914_);
lean_dec_ref(v_s_2911_);
v_r_2916_ = lean_box(v_res_2915_);
return v_r_2916_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object* v_s_2917_){
_start:
{
lean_object* v_searcher_2918_; uint8_t v___x_2919_; uint8_t v___x_2920_; 
v_searcher_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = 0;
v___x_2920_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2917_, v_searcher_2918_, v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object* v_s_2921_){
_start:
{
uint8_t v_res_2922_; lean_object* v_r_2923_; 
v_res_2922_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2921_);
lean_dec_ref(v_s_2921_);
v_r_2923_ = lean_box(v_res_2922_);
return v_r_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object* v_si_2924_, lean_object* v_val_2925_){
_start:
{
lean_object* v___y_2927_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = lean_string_utf8_byte_size(v_val_2925_);
lean_inc_ref(v_val_2925_);
v___x_2935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2935_, 0, v_val_2925_);
lean_ctor_set(v___x_2935_, 1, v___x_2933_);
lean_ctor_set(v___x_2935_, 2, v___x_2934_);
v___x_2936_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_2935_);
lean_dec_ref_known(v___x_2935_, 3);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_box(0);
lean_inc_ref(v_val_2925_);
v___x_2938_ = l_Lean_Name_str___override(v___x_2937_, v_val_2925_);
v___y_2927_ = v___x_2938_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_2939_; 
lean_inc_ref(v_val_2925_);
v___x_2939_ = l_String_toName(v_val_2925_);
v___y_2927_ = v___x_2939_;
goto v___jp_2926_;
}
v___jp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = lean_string_utf8_byte_size(v_val_2925_);
v___x_2930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2930_, 0, v_val_2925_);
lean_ctor_set(v___x_2930_, 1, v___x_2928_);
lean_ctor_set(v___x_2930_, 2, v___x_2929_);
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2932_, 0, v_si_2924_);
lean_ctor_set(v___x_2932_, 1, v___x_2930_);
lean_ctor_set(v___x_2932_, 2, v___y_2927_);
lean_ctor_set(v___x_2932_, 3, v___x_2931_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object* v_eval_2941_, uint8_t v_logExceptions_2942_, lean_object* v_onErr_2943_, lean_object* v_init_2944_, lean_object* v_cfg_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2945_);
v___x_2975_ = l_Lean_Syntax_isOfKind(v_cfg_2945_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = l_Lean_Syntax_getNumArgs(v_cfg_2945_);
v___x_2977_ = lean_unsigned_to_nat(1u);
v___x_2978_ = lean_nat_dec_eq(v___x_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v_atomAsIdent_2979_; uint8_t v___x_2980_; 
v_atomAsIdent_2979_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0));
v___x_2980_ = lean_nat_dec_le(v___x_2977_, v___x_2976_);
if (v___x_2980_ == 0)
{
lean_dec(v___x_2976_);
if (lean_obj_tag(v_cfg_2945_) == 2)
{
lean_object* v_info_2981_; lean_object* v_val_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_dec_ref(v_onErr_2943_);
v_info_2981_ = lean_ctor_get(v_cfg_2945_, 0);
v_val_2982_ = lean_ctor_get(v_cfg_2945_, 1);
lean_inc_ref(v_val_2982_);
lean_inc(v_info_2981_);
v___x_2983_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_2981_, v_val_2982_);
v___x_2984_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2985_ = l_Lean_mkCIdentFrom(v_cfg_2945_, v___x_2984_, v___x_2980_);
v___x_2986_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2987_ = l_Lean_TSyntax_getId(v___x_2983_);
v___x_2988_ = l_Lean_Name_eraseMacroScopes(v___x_2987_);
lean_dec(v___x_2987_);
v___x_2989_ = lean_box(0);
lean_inc(v___x_2983_);
v___x_2990_ = l_Lean_Syntax_identComponents(v___x_2983_, v___x_2989_);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2992_, 0, v_cfg_2945_);
lean_ctor_set(v___x_2992_, 1, v___x_2983_);
lean_ctor_set(v___x_2992_, 2, v___x_2985_);
lean_ctor_set(v___x_2992_, 3, v___x_2986_);
lean_ctor_set(v___x_2992_, 4, v___x_2988_);
lean_ctor_set(v___x_2992_, 5, v___x_2990_);
lean_ctor_set(v___x_2992_, 6, v___x_2991_);
v___x_2993_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2941_, v_init_2944_, v___x_2992_, v_logExceptions_2942_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
return v___x_2993_;
}
else
{
lean_dec_ref(v_eval_2941_);
goto v___jp_2964_;
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = l_Lean_Syntax_getArg(v_cfg_2945_, v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 2)
{
lean_object* v_val_2996_; lean_object* v___y_2998_; uint8_t v_val_2999_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v_val_2996_ = lean_ctor_get(v___x_2995_, 1);
v___x_3010_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_3011_ = lean_string_dec_eq(v_val_2996_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_3013_ = lean_string_dec_eq(v_val_2996_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; uint8_t v___x_3015_; 
lean_inc_ref(v_val_2996_);
lean_dec_ref_known(v___x_2995_, 2);
v___x_3014_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_3015_ = lean_string_dec_eq(v_val_2996_, v___x_3014_);
lean_dec_ref(v_val_2996_);
if (v___x_3015_ == 0)
{
lean_dec(v___x_2976_);
lean_dec_ref(v_eval_2941_);
goto v___jp_2964_;
}
else
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = lean_unsigned_to_nat(5u);
v___x_3017_ = lean_nat_dec_le(v___x_2976_, v___x_3016_);
lean_dec(v___x_2976_);
if (v___x_3017_ == 0)
{
lean_dec_ref(v_eval_2941_);
goto v___jp_2964_;
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = l_Lean_Syntax_getArg(v_cfg_2945_, v___x_2977_);
v___x_3019_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2979_, v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 1)
{
lean_object* v_val_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec_ref(v_onErr_2943_);
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc_n(v_val_3020_, 2);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = lean_unsigned_to_nat(3u);
v___x_3022_ = l_Lean_Syntax_getArg(v_cfg_2945_, v___x_3021_);
v___x_3023_ = lean_box(0);
v___x_3024_ = l_Lean_TSyntax_getId(v_val_3020_);
v___x_3025_ = l_Lean_Name_eraseMacroScopes(v___x_3024_);
lean_dec(v___x_3024_);
v___x_3026_ = l_Lean_Syntax_identComponents(v_val_3020_, v___x_3023_);
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3028_, 0, v_cfg_2945_);
lean_ctor_set(v___x_3028_, 1, v_val_3020_);
lean_ctor_set(v___x_3028_, 2, v___x_3022_);
lean_ctor_set(v___x_3028_, 3, v___x_3023_);
lean_ctor_set(v___x_3028_, 4, v___x_3025_);
lean_ctor_set(v___x_3028_, 5, v___x_3026_);
lean_ctor_set(v___x_3028_, 6, v___x_3027_);
v___x_3029_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2941_, v_init_2944_, v___x_3028_, v_logExceptions_2942_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
return v___x_3029_;
}
else
{
lean_dec(v___x_3019_);
lean_dec_ref(v_eval_2941_);
goto v___jp_2964_;
}
}
}
}
else
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = lean_box(v___x_3011_);
v___x_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___y_2998_ = v___x_3031_;
v_val_2999_ = v___x_3011_;
goto v___jp_2997_;
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_box(v___x_2980_);
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
v___y_2998_ = v___x_3033_;
v_val_2999_ = v___x_2980_;
goto v___jp_2997_;
}
v___jp_2997_:
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(2u);
v___x_3001_ = lean_nat_dec_eq(v___x_2976_, v___x_3000_);
lean_dec(v___x_2976_);
if (v___x_3001_ == 0)
{
lean_dec(v___y_2998_);
lean_dec_ref_known(v___x_2995_, 2);
lean_dec_ref(v_eval_2941_);
goto v___jp_2964_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = l_Lean_Syntax_getArg(v_cfg_2945_, v___x_2977_);
v___x_3003_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2979_, v___x_3002_);
if (lean_obj_tag(v___x_3003_) == 1)
{
lean_dec_ref(v_onErr_2943_);
if (v_val_2999_ == 0)
{
lean_object* v_val_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_val_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_3006_ = l_Lean_mkCIdentFrom(v___x_2995_, v___x_3005_, v_val_2999_);
lean_dec_ref_known(v___x_2995_, 2);
v___y_2954_ = v_val_3004_;
v___y_2955_ = v___y_2998_;
v___y_2956_ = v___x_3006_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_val_3007_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_val_3007_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3008_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_3009_ = l_Lean_mkCIdentFrom(v___x_2995_, v___x_3008_, v___x_2978_);
lean_dec_ref_known(v___x_2995_, 2);
v___y_2954_ = v_val_3007_;
v___y_2955_ = v___y_2998_;
v___y_2956_ = v___x_3009_;
goto v___jp_2953_;
}
}
else
{
lean_dec(v___x_3003_);
lean_dec(v___y_2998_);
lean_dec_ref_known(v___x_2995_, 2);
lean_dec_ref(v_eval_2941_);
goto v___jp_2964_;
}
}
}
}
else
{
lean_dec(v___x_2995_);
lean_dec(v___x_2976_);
lean_dec_ref(v_eval_2941_);
goto v___jp_2964_;
}
}
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec(v___x_2976_);
v___x_3034_ = lean_unsigned_to_nat(0u);
v___x_3035_ = l_Lean_Syntax_getArg(v_cfg_2945_, v___x_3034_);
lean_dec(v_cfg_2945_);
v_cfg_2945_ = v___x_3035_;
goto _start;
}
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = l_Lean_Syntax_getArgs(v_cfg_2945_);
lean_dec(v_cfg_2945_);
v___x_3038_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_2941_, v_logExceptions_2942_, v_onErr_2943_, v_init_2944_, v___x_3037_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec_ref(v___x_3037_);
return v___x_3038_;
}
v___jp_2953_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2957_ = l_Lean_TSyntax_getId(v___y_2954_);
v___x_2958_ = l_Lean_Name_eraseMacroScopes(v___x_2957_);
lean_dec(v___x_2957_);
v___x_2959_ = lean_box(0);
lean_inc(v___y_2954_);
v___x_2960_ = l_Lean_Syntax_identComponents(v___y_2954_, v___x_2959_);
v___x_2961_ = lean_box(0);
v___x_2962_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2962_, 0, v_cfg_2945_);
lean_ctor_set(v___x_2962_, 1, v___y_2954_);
lean_ctor_set(v___x_2962_, 2, v___y_2956_);
lean_ctor_set(v___x_2962_, 3, v___y_2955_);
lean_ctor_set(v___x_2962_, 4, v___x_2958_);
lean_ctor_set(v___x_2962_, 5, v___x_2960_);
lean_ctor_set(v___x_2962_, 6, v___x_2961_);
v___x_2963_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2941_, v_init_2944_, v___x_2962_, v_logExceptions_2942_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
return v___x_2963_;
}
v___jp_2964_:
{
lean_object* v_toCold_2965_; lean_object* v_currRecDepth_2966_; lean_object* v_ref_2967_; uint16_t v_optionFlags_2968_; uint8_t v_suppressElabErrors_2969_; uint8_t v_isRecordingDeps_2970_; lean_object* v_ref_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_toCold_2965_ = lean_ctor_get(v___y_2950_, 0);
v_currRecDepth_2966_ = lean_ctor_get(v___y_2950_, 1);
v_ref_2967_ = lean_ctor_get(v___y_2950_, 2);
v_optionFlags_2968_ = lean_ctor_get_uint16(v___y_2950_, sizeof(void*)*3);
v_suppressElabErrors_2969_ = lean_ctor_get_uint8(v___y_2950_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2970_ = lean_ctor_get_uint8(v___y_2950_, sizeof(void*)*3 + 3);
v_ref_2971_ = l_Lean_replaceRef(v_cfg_2945_, v_ref_2967_);
lean_inc(v_currRecDepth_2966_);
lean_inc_ref(v_toCold_2965_);
v___x_2972_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2972_, 0, v_toCold_2965_);
lean_ctor_set(v___x_2972_, 1, v_currRecDepth_2966_);
lean_ctor_set(v___x_2972_, 2, v_ref_2971_);
lean_ctor_set_uint16(v___x_2972_, sizeof(void*)*3, v_optionFlags_2968_);
lean_ctor_set_uint8(v___x_2972_, sizeof(void*)*3 + 2, v_suppressElabErrors_2969_);
lean_ctor_set_uint8(v___x_2972_, sizeof(void*)*3 + 3, v_isRecordingDeps_2970_);
lean_inc(v___y_2951_);
lean_inc(v___y_2949_);
lean_inc_ref(v___y_2948_);
lean_inc(v___y_2947_);
lean_inc_ref(v___y_2946_);
v___x_2973_ = lean_apply_9(v_onErr_2943_, v_init_2944_, v_cfg_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___x_2972_, v___y_2951_, lean_box(0));
return v___x_2973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object* v_eval_3039_, uint8_t v_logExceptions_3040_, lean_object* v_onErr_3041_, lean_object* v_as_3042_, size_t v_i_3043_, size_t v_stop_3044_, lean_object* v_b_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_usize_dec_eq(v_i_3043_, v_stop_3044_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_array_uget_borrowed(v_as_3042_, v_i_3043_);
lean_inc(v___x_3054_);
lean_inc_ref(v_onErr_3041_);
lean_inc_ref(v_eval_3039_);
v___x_3055_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3039_, v_logExceptions_3040_, v_onErr_3041_, v_b_3045_, v___x_3054_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; size_t v___x_3057_; size_t v___x_3058_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3057_ = ((size_t)1ULL);
v___x_3058_ = lean_usize_add(v_i_3043_, v___x_3057_);
v_i_3043_ = v___x_3058_;
v_b_3045_ = v_a_3056_;
goto _start;
}
else
{
lean_dec_ref(v_onErr_3041_);
lean_dec_ref(v_eval_3039_);
return v___x_3055_;
}
}
else
{
lean_object* v___x_3060_; 
lean_dec_ref(v_onErr_3041_);
lean_dec_ref(v_eval_3039_);
v___x_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_b_3045_);
return v___x_3060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object* v_eval_3061_, uint8_t v_logExceptions_3062_, lean_object* v_onErr_3063_, lean_object* v_init_3064_, lean_object* v_cfgs_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = lean_array_get_size(v_cfgs_3065_);
v___x_3075_ = lean_nat_dec_lt(v___x_3073_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
lean_dec_ref(v_onErr_3063_);
lean_dec_ref(v_eval_3061_);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_init_3064_);
return v___x_3076_;
}
else
{
size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((size_t)0ULL);
v___x_3078_ = lean_usize_of_nat(v___x_3074_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3061_, v_logExceptions_3062_, v_onErr_3063_, v_cfgs_3065_, v___x_3077_, v___x_3078_, v_init_3064_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object* v_eval_3080_, lean_object* v_logExceptions_3081_, lean_object* v_onErr_3082_, lean_object* v_init_3083_, lean_object* v_cfgs_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
uint8_t v_logExceptions_boxed_3092_; lean_object* v_res_3093_; 
v_logExceptions_boxed_3092_ = lean_unbox(v_logExceptions_3081_);
v_res_3093_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3080_, v_logExceptions_boxed_3092_, v_onErr_3082_, v_init_3083_, v_cfgs_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec_ref(v_cfgs_3084_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_eval_3094_, lean_object* v_logExceptions_3095_, lean_object* v_onErr_3096_, lean_object* v_as_3097_, lean_object* v_i_3098_, lean_object* v_stop_3099_, lean_object* v_b_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
uint8_t v_logExceptions_boxed_3108_; size_t v_i_boxed_3109_; size_t v_stop_boxed_3110_; lean_object* v_res_3111_; 
v_logExceptions_boxed_3108_ = lean_unbox(v_logExceptions_3095_);
v_i_boxed_3109_ = lean_unbox_usize(v_i_3098_);
lean_dec(v_i_3098_);
v_stop_boxed_3110_ = lean_unbox_usize(v_stop_3099_);
lean_dec(v_stop_3099_);
v_res_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3094_, v_logExceptions_boxed_3108_, v_onErr_3096_, v_as_3097_, v_i_boxed_3109_, v_stop_boxed_3110_, v_b_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec_ref(v_as_3097_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object* v_eval_3112_, lean_object* v_logExceptions_3113_, lean_object* v_onErr_3114_, lean_object* v_init_3115_, lean_object* v_cfg_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
uint8_t v_logExceptions_boxed_3124_; lean_object* v_res_3125_; 
v_logExceptions_boxed_3124_ = lean_unbox(v_logExceptions_3113_);
v_res_3125_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3112_, v_logExceptions_boxed_3124_, v_onErr_3114_, v_init_3115_, v_cfg_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object* v_eval_3126_, lean_object* v_init_3127_, lean_object* v_cfg_3128_, lean_object* v_onErr_3129_, uint8_t v_logExceptions_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3126_, v_logExceptions_3130_, v_onErr_3129_, v_init_3127_, v_cfg_3128_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object* v_eval_3139_, lean_object* v_init_3140_, lean_object* v_cfg_3141_, lean_object* v_onErr_3142_, lean_object* v_logExceptions_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
uint8_t v_logExceptions_boxed_3151_; lean_object* v_res_3152_; 
v_logExceptions_boxed_3151_ = lean_unbox(v_logExceptions_3143_);
v_res_3152_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3139_, v_init_3140_, v_cfg_3141_, v_onErr_3142_, v_logExceptions_boxed_3151_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object* v_00_u03b1_3153_, lean_object* v_eval_3154_, lean_object* v_init_3155_, lean_object* v_cfg_3156_, lean_object* v_onErr_3157_, uint8_t v_logExceptions_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3154_, v_logExceptions_3158_, v_onErr_3157_, v_init_3155_, v_cfg_3156_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object* v_00_u03b1_3167_, lean_object* v_eval_3168_, lean_object* v_init_3169_, lean_object* v_cfg_3170_, lean_object* v_onErr_3171_, lean_object* v_logExceptions_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
uint8_t v_logExceptions_boxed_3180_; lean_object* v_res_3181_; 
v_logExceptions_boxed_3180_ = lean_unbox(v_logExceptions_3172_);
v_res_3181_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(v_00_u03b1_3167_, v_eval_3168_, v_init_3169_, v_cfg_3170_, v_onErr_3171_, v_logExceptions_boxed_3180_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object* v_00_u03b1_3182_, lean_object* v_eval_3183_, uint8_t v_logExceptions_3184_, lean_object* v_onErr_3185_, lean_object* v_init_3186_, lean_object* v_cfg_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3183_, v_logExceptions_3184_, v_onErr_3185_, v_init_3186_, v_cfg_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(lean_object* v_00_u03b1_3196_, lean_object* v_eval_3197_, lean_object* v_logExceptions_3198_, lean_object* v_onErr_3199_, lean_object* v_init_3200_, lean_object* v_cfg_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v_logExceptions_boxed_3209_; lean_object* v_res_3210_; 
v_logExceptions_boxed_3209_ = lean_unbox(v_logExceptions_3198_);
v_res_3210_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_3196_, v_eval_3197_, v_logExceptions_boxed_3209_, v_onErr_3199_, v_init_3200_, v_cfg_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object* v_00_u03b1_3211_, lean_object* v_eval_3212_, uint8_t v_logExceptions_3213_, lean_object* v_onErr_3214_, lean_object* v_init_3215_, lean_object* v_cfgs_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3212_, v_logExceptions_3213_, v_onErr_3214_, v_init_3215_, v_cfgs_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3225_, lean_object* v_eval_3226_, lean_object* v_logExceptions_3227_, lean_object* v_onErr_3228_, lean_object* v_init_3229_, lean_object* v_cfgs_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_logExceptions_boxed_3238_; lean_object* v_res_3239_; 
v_logExceptions_boxed_3238_ = lean_unbox(v_logExceptions_3227_);
v_res_3239_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_3225_, v_eval_3226_, v_logExceptions_boxed_3238_, v_onErr_3228_, v_init_3229_, v_cfgs_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec_ref(v_cfgs_3230_);
return v_res_3239_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object* v_s_3240_, lean_object* v_inst_3241_, lean_object* v_R_3242_, lean_object* v_a_3243_, uint8_t v_b_3244_, lean_object* v_c_3245_){
_start:
{
uint8_t v___x_3246_; 
v___x_3246_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_3240_, v_a_3243_, v_b_3244_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_s_3247_, lean_object* v_inst_3248_, lean_object* v_R_3249_, lean_object* v_a_3250_, lean_object* v_b_3251_, lean_object* v_c_3252_){
_start:
{
uint8_t v_b_boxed_3253_; uint8_t v_res_3254_; lean_object* v_r_3255_; 
v_b_boxed_3253_ = lean_unbox(v_b_3251_);
v_res_3254_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3247_, v_inst_3248_, v_R_3249_, v_a_3250_, v_b_boxed_3253_, v_c_3252_);
lean_dec_ref(v_s_3247_);
v_r_3255_ = lean_box(v_res_3254_);
return v_r_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3256_, lean_object* v_eval_3257_, uint8_t v_logExceptions_3258_, lean_object* v_onErr_3259_, lean_object* v_as_3260_, size_t v_i_3261_, size_t v_stop_3262_, lean_object* v_b_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3257_, v_logExceptions_3258_, v_onErr_3259_, v_as_3260_, v_i_3261_, v_stop_3262_, v_b_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3272_, lean_object* v_eval_3273_, lean_object* v_logExceptions_3274_, lean_object* v_onErr_3275_, lean_object* v_as_3276_, lean_object* v_i_3277_, lean_object* v_stop_3278_, lean_object* v_b_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v_logExceptions_boxed_3287_; size_t v_i_boxed_3288_; size_t v_stop_boxed_3289_; lean_object* v_res_3290_; 
v_logExceptions_boxed_3287_ = lean_unbox(v_logExceptions_3274_);
v_i_boxed_3288_ = lean_unbox_usize(v_i_3277_);
lean_dec(v_i_3277_);
v_stop_boxed_3289_ = lean_unbox_usize(v_stop_3278_);
lean_dec(v_stop_3278_);
v_res_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_3272_, v_eval_3273_, v_logExceptions_boxed_3287_, v_onErr_3275_, v_as_3276_, v_i_boxed_3288_, v_stop_boxed_3289_, v_b_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec_ref(v_as_3276_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object* v_eval_3291_, lean_object* v_init_3292_, lean_object* v_cfgs_3293_, lean_object* v_onErr_3294_, uint8_t v_logExceptions_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3291_, v_logExceptions_3295_, v_onErr_3294_, v_init_3292_, v_cfgs_3293_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object* v_eval_3304_, lean_object* v_init_3305_, lean_object* v_cfgs_3306_, lean_object* v_onErr_3307_, lean_object* v_logExceptions_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
uint8_t v_logExceptions_boxed_3316_; lean_object* v_res_3317_; 
v_logExceptions_boxed_3316_ = lean_unbox(v_logExceptions_3308_);
v_res_3317_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3304_, v_init_3305_, v_cfgs_3306_, v_onErr_3307_, v_logExceptions_boxed_3316_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec_ref(v_cfgs_3306_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object* v_00_u03b1_3318_, lean_object* v_eval_3319_, lean_object* v_init_3320_, lean_object* v_cfgs_3321_, lean_object* v_onErr_3322_, uint8_t v_logExceptions_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3319_, v_logExceptions_3323_, v_onErr_3322_, v_init_3320_, v_cfgs_3321_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object* v_00_u03b1_3332_, lean_object* v_eval_3333_, lean_object* v_init_3334_, lean_object* v_cfgs_3335_, lean_object* v_onErr_3336_, lean_object* v_logExceptions_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
uint8_t v_logExceptions_boxed_3345_; lean_object* v_res_3346_; 
v_logExceptions_boxed_3345_ = lean_unbox(v_logExceptions_3337_);
v_res_3346_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(v_00_u03b1_3332_, v_eval_3333_, v_init_3334_, v_cfgs_3335_, v_onErr_3336_, v_logExceptions_boxed_3345_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec_ref(v_cfgs_3335_);
return v_res_3346_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object* v_x_3347_){
_start:
{
uint8_t v___x_3348_; 
v___x_3348_ = 0;
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object* v_x_3349_){
_start:
{
uint8_t v_res_3350_; lean_object* v_r_3351_; 
v_res_3350_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3349_);
lean_dec(v_x_3349_);
v_r_3351_ = lean_box(v_res_3350_);
return v_r_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(lean_object* v___x_3352_, lean_object* v_ctx_x3f_3353_, size_t v_sz_3354_, size_t v_i_3355_, lean_object* v_bs_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
uint8_t v___x_3364_; 
v___x_3364_ = lean_usize_dec_lt(v_i_3355_, v_sz_3354_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref(v_ctx_x3f_3353_);
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_bs_3356_);
return v___x_3365_;
}
else
{
lean_object* v_assignment_3366_; lean_object* v_v_3367_; lean_object* v___x_3368_; lean_object* v_bs_x27_3369_; lean_object* v_a_3371_; lean_object* v_tree_3376_; lean_object* v___x_3377_; 
v_assignment_3366_ = lean_ctor_get(v___x_3352_, 0);
v_v_3367_ = lean_array_uget(v_bs_3356_, v_i_3355_);
v___x_3368_ = lean_unsigned_to_nat(0u);
v_bs_x27_3369_ = lean_array_uset(v_bs_3356_, v_i_3355_, v___x_3368_);
v_tree_3376_ = l_Lean_Elab_InfoTree_substitute(v_v_3367_, v_assignment_3366_);
lean_inc_ref(v_ctx_x3f_3353_);
lean_inc(v___y_3362_);
lean_inc_ref(v___y_3361_);
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
v___x_3377_ = lean_apply_7(v_ctx_x3f_3353_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, lean_box(0));
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
if (lean_obj_tag(v_a_3378_) == 0)
{
v_a_3371_ = v_tree_3376_;
goto v___jp_3370_;
}
else
{
lean_object* v_val_3379_; lean_object* v___x_3380_; 
v_val_3379_ = lean_ctor_get(v_a_3378_, 0);
lean_inc(v_val_3379_);
lean_dec_ref_known(v_a_3378_, 1);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_val_3379_);
lean_ctor_set(v___x_3380_, 1, v_tree_3376_);
v_a_3371_ = v___x_3380_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec_ref(v_tree_3376_);
lean_dec_ref(v_bs_x27_3369_);
lean_dec_ref(v_ctx_x3f_3353_);
v_a_3381_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3377_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3377_);
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
v___jp_3370_:
{
size_t v___x_3372_; size_t v___x_3373_; lean_object* v___x_3374_; 
v___x_3372_ = ((size_t)1ULL);
v___x_3373_ = lean_usize_add(v_i_3355_, v___x_3372_);
v___x_3374_ = lean_array_uset(v_bs_x27_3369_, v_i_3355_, v_a_3371_);
v_i_3355_ = v___x_3373_;
v_bs_3356_ = v___x_3374_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v___x_3389_, lean_object* v_ctx_x3f_3390_, lean_object* v_sz_3391_, lean_object* v_i_3392_, lean_object* v_bs_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
size_t v_sz_boxed_3401_; size_t v_i_boxed_3402_; lean_object* v_res_3403_; 
v_sz_boxed_3401_ = lean_unbox_usize(v_sz_3391_);
lean_dec(v_sz_3391_);
v_i_boxed_3402_ = lean_unbox_usize(v_i_3392_);
lean_dec(v_i_3392_);
v_res_3403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3389_, v_ctx_x3f_3390_, v_sz_boxed_3401_, v_i_boxed_3402_, v_bs_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec_ref(v___x_3389_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(lean_object* v___x_3404_, lean_object* v_ctx_x3f_3405_, lean_object* v_x_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
if (lean_obj_tag(v_x_3406_) == 0)
{
lean_object* v_cs_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3440_; 
v_cs_3414_ = lean_ctor_get(v_x_3406_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_x_3406_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3416_ = v_x_3406_;
v_isShared_3417_ = v_isSharedCheck_3440_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_cs_3414_);
lean_dec(v_x_3406_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3440_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
size_t v_sz_3418_; size_t v___x_3419_; lean_object* v___x_3420_; 
v_sz_3418_ = lean_array_size(v_cs_3414_);
v___x_3419_ = ((size_t)0ULL);
v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3404_, v_ctx_x3f_3405_, v_sz_3418_, v___x_3419_, v_cs_3414_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3431_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_a_3421_);
v___x_3426_ = v___x_3416_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3428_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3426_);
v___x_3428_ = v___x_3423_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_del_object(v___x_3416_);
v_a_3432_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3420_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3420_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
else
{
lean_object* v_vs_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3467_; 
v_vs_3441_ = lean_ctor_get(v_x_3406_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_x_3406_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3443_ = v_x_3406_;
v_isShared_3444_ = v_isSharedCheck_3467_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_vs_3441_);
lean_dec(v_x_3406_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3467_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
size_t v_sz_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v_sz_3445_ = lean_array_size(v_vs_3441_);
v___x_3446_ = ((size_t)0ULL);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3404_, v_ctx_x3f_3405_, v_sz_3445_, v___x_3446_, v_vs_3441_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3458_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v_a_3448_);
v___x_3453_ = v___x_3443_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3453_);
v___x_3455_ = v___x_3450_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_del_object(v___x_3443_);
v_a_3459_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3447_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3447_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v___x_3468_, lean_object* v_ctx_x3f_3469_, size_t v_sz_3470_, size_t v_i_3471_, lean_object* v_bs_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_usize_dec_lt(v_i_3471_, v_sz_3470_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec_ref(v_ctx_x3f_3469_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_bs_3472_);
return v___x_3481_;
}
else
{
lean_object* v_v_3482_; lean_object* v___x_3483_; lean_object* v_bs_x27_3484_; lean_object* v___x_3485_; 
v_v_3482_ = lean_array_uget(v_bs_3472_, v_i_3471_);
v___x_3483_ = lean_unsigned_to_nat(0u);
v_bs_x27_3484_ = lean_array_uset(v_bs_3472_, v_i_3471_, v___x_3483_);
lean_inc_ref(v_ctx_x3f_3469_);
v___x_3485_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3468_, v_ctx_x3f_3469_, v_v_3482_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; size_t v___x_3487_; size_t v___x_3488_; lean_object* v___x_3489_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = ((size_t)1ULL);
v___x_3488_ = lean_usize_add(v_i_3471_, v___x_3487_);
v___x_3489_ = lean_array_uset(v_bs_x27_3484_, v_i_3471_, v_a_3486_);
v_i_3471_ = v___x_3488_;
v_bs_3472_ = v___x_3489_;
goto _start;
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v_bs_x27_3484_);
lean_dec_ref(v_ctx_x3f_3469_);
v_a_3491_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3485_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3485_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v___x_3499_, lean_object* v_ctx_x3f_3500_, lean_object* v_sz_3501_, lean_object* v_i_3502_, lean_object* v_bs_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
size_t v_sz_boxed_3511_; size_t v_i_boxed_3512_; lean_object* v_res_3513_; 
v_sz_boxed_3511_ = lean_unbox_usize(v_sz_3501_);
lean_dec(v_sz_3501_);
v_i_boxed_3512_ = lean_unbox_usize(v_i_3502_);
lean_dec(v_i_3502_);
v_res_3513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3499_, v_ctx_x3f_3500_, v_sz_boxed_3511_, v_i_boxed_3512_, v_bs_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v___x_3499_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v___x_3514_, lean_object* v_ctx_x3f_3515_, lean_object* v_x_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3514_, v_ctx_x3f_3515_, v_x_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___x_3514_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object* v___x_3525_, lean_object* v_ctx_x3f_3526_, lean_object* v_t_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_root_3535_; lean_object* v_tail_3536_; lean_object* v_size_3537_; size_t v_shift_3538_; lean_object* v_tailOff_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3575_; 
v_root_3535_ = lean_ctor_get(v_t_3527_, 0);
v_tail_3536_ = lean_ctor_get(v_t_3527_, 1);
v_size_3537_ = lean_ctor_get(v_t_3527_, 2);
v_shift_3538_ = lean_ctor_get_usize(v_t_3527_, 4);
v_tailOff_3539_ = lean_ctor_get(v_t_3527_, 3);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_t_3527_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3541_ = v_t_3527_;
v_isShared_3542_ = v_isSharedCheck_3575_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_tailOff_3539_);
lean_inc(v_size_3537_);
lean_inc(v_tail_3536_);
lean_inc(v_root_3535_);
lean_dec(v_t_3527_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3575_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; 
lean_inc_ref(v_ctx_x3f_3526_);
v___x_3543_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3525_, v_ctx_x3f_3526_, v_root_3535_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; size_t v_sz_3545_; size_t v___x_3546_; lean_object* v___x_3547_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v_sz_3545_ = lean_array_size(v_tail_3536_);
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3525_, v_ctx_x3f_3526_, v_sz_3545_, v___x_3546_, v_tail_3536_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3558_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3550_ = v___x_3547_;
v_isShared_3551_ = v_isSharedCheck_3558_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3558_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 1, v_a_3548_);
lean_ctor_set(v___x_3541_, 0, v_a_3544_);
v___x_3553_ = v___x_3541_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3544_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_a_3548_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_size_3537_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_tailOff_3539_);
lean_ctor_set_usize(v_reuseFailAlloc_3557_, 4, v_shift_3538_);
v___x_3553_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3555_; 
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v___x_3553_);
v___x_3555_ = v___x_3550_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_a_3544_);
lean_del_object(v___x_3541_);
lean_dec(v_tailOff_3539_);
lean_dec(v_size_3537_);
v_a_3559_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3547_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3547_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_del_object(v___x_3541_);
lean_dec(v_tailOff_3539_);
lean_dec(v_size_3537_);
lean_dec_ref(v_tail_3536_);
lean_dec_ref(v_ctx_x3f_3526_);
v_a_3567_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3543_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3543_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object* v___x_3576_, lean_object* v_ctx_x3f_3577_, lean_object* v_t_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3576_, v_ctx_x3f_3577_, v_t_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v___x_3576_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3587_, lean_object* v_ctx_x3f_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v_a_3594_, lean_object* v_a_x3f_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v_infoState_3598_; lean_object* v_trees_3599_; lean_object* v___x_3600_; 
v___x_3597_ = lean_st_ref_get(v___y_3587_);
v_infoState_3598_ = lean_ctor_get(v___x_3597_, 8);
lean_inc_ref(v_infoState_3598_);
lean_dec(v___x_3597_);
v_trees_3599_ = lean_ctor_get(v_infoState_3598_, 2);
lean_inc_ref(v_trees_3599_);
v___x_3600_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_3598_, v_ctx_x3f_3588_, v_trees_3599_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3587_);
lean_dec_ref(v_infoState_3598_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3640_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3640_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3640_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v_infoState_3606_; lean_object* v_env_3607_; lean_object* v_nextMacroScope_3608_; lean_object* v_ngen_3609_; lean_object* v_auxDeclNGen_3610_; lean_object* v_traceState_3611_; lean_object* v_cache_3612_; lean_object* v_recordedDeps_3613_; lean_object* v_messages_3614_; lean_object* v_snapshotTasks_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3639_; 
v___x_3605_ = lean_st_ref_take(v___y_3587_);
v_infoState_3606_ = lean_ctor_get(v___x_3605_, 8);
v_env_3607_ = lean_ctor_get(v___x_3605_, 0);
v_nextMacroScope_3608_ = lean_ctor_get(v___x_3605_, 1);
v_ngen_3609_ = lean_ctor_get(v___x_3605_, 2);
v_auxDeclNGen_3610_ = lean_ctor_get(v___x_3605_, 3);
v_traceState_3611_ = lean_ctor_get(v___x_3605_, 4);
v_cache_3612_ = lean_ctor_get(v___x_3605_, 5);
v_recordedDeps_3613_ = lean_ctor_get(v___x_3605_, 6);
v_messages_3614_ = lean_ctor_get(v___x_3605_, 7);
v_snapshotTasks_3615_ = lean_ctor_get(v___x_3605_, 9);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3617_ = v___x_3605_;
v_isShared_3618_ = v_isSharedCheck_3639_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_snapshotTasks_3615_);
lean_inc(v_infoState_3606_);
lean_inc(v_messages_3614_);
lean_inc(v_recordedDeps_3613_);
lean_inc(v_cache_3612_);
lean_inc(v_traceState_3611_);
lean_inc(v_auxDeclNGen_3610_);
lean_inc(v_ngen_3609_);
lean_inc(v_nextMacroScope_3608_);
lean_inc(v_env_3607_);
lean_dec(v___x_3605_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3639_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
uint8_t v_enabled_3619_; lean_object* v_assignment_3620_; lean_object* v_lazyAssignment_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3637_; 
v_enabled_3619_ = lean_ctor_get_uint8(v_infoState_3606_, sizeof(void*)*3);
v_assignment_3620_ = lean_ctor_get(v_infoState_3606_, 0);
v_lazyAssignment_3621_ = lean_ctor_get(v_infoState_3606_, 1);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_infoState_3606_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v_infoState_3606_, 2);
lean_dec(v_unused_3638_);
v___x_3623_ = v_infoState_3606_;
v_isShared_3624_ = v_isSharedCheck_3637_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_lazyAssignment_3621_);
lean_inc(v_assignment_3620_);
lean_dec(v_infoState_3606_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3637_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3625_ = lean_box(0);
v___x_3626_ = l_Lean_PersistentArray_append___redArg(v_a_3594_, v_a_3601_);
lean_dec(v_a_3601_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 2, v___x_3626_);
v___x_3628_ = v___x_3623_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_assignment_3620_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_lazyAssignment_3621_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v___x_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3636_, sizeof(void*)*3, v_enabled_3619_);
v___x_3628_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3630_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 8, v___x_3628_);
v___x_3630_ = v___x_3617_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_env_3607_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_nextMacroScope_3608_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_ngen_3609_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_auxDeclNGen_3610_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_traceState_3611_);
lean_ctor_set(v_reuseFailAlloc_3635_, 5, v_cache_3612_);
lean_ctor_set(v_reuseFailAlloc_3635_, 6, v_recordedDeps_3613_);
lean_ctor_set(v_reuseFailAlloc_3635_, 7, v_messages_3614_);
lean_ctor_set(v_reuseFailAlloc_3635_, 8, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3635_, 9, v_snapshotTasks_3615_);
v___x_3630_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3631_ = lean_st_ref_put(v___y_3587_, v___x_3630_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3625_);
v___x_3633_ = v___x_3603_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3625_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec_ref(v_a_3594_);
v_a_3641_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3600_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3600_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3649_, lean_object* v_ctx_x3f_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v_a_3656_, lean_object* v_a_x3f_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3649_, v_ctx_x3f_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v_a_3656_, v_a_x3f_3657_);
lean_dec(v_a_x3f_3657_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3649_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; lean_object* v_infoState_3663_; lean_object* v_trees_3664_; lean_object* v___x_3665_; lean_object* v_infoState_3666_; lean_object* v_env_3667_; lean_object* v_nextMacroScope_3668_; lean_object* v_ngen_3669_; lean_object* v_auxDeclNGen_3670_; lean_object* v_traceState_3671_; lean_object* v_cache_3672_; lean_object* v_recordedDeps_3673_; lean_object* v_messages_3674_; lean_object* v_snapshotTasks_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3698_; 
v___x_3662_ = lean_st_ref_get(v___y_3660_);
v_infoState_3663_ = lean_ctor_get(v___x_3662_, 8);
lean_inc_ref(v_infoState_3663_);
lean_dec(v___x_3662_);
v_trees_3664_ = lean_ctor_get(v_infoState_3663_, 2);
lean_inc_ref(v_trees_3664_);
lean_dec_ref(v_infoState_3663_);
v___x_3665_ = lean_st_ref_take(v___y_3660_);
v_infoState_3666_ = lean_ctor_get(v___x_3665_, 8);
v_env_3667_ = lean_ctor_get(v___x_3665_, 0);
v_nextMacroScope_3668_ = lean_ctor_get(v___x_3665_, 1);
v_ngen_3669_ = lean_ctor_get(v___x_3665_, 2);
v_auxDeclNGen_3670_ = lean_ctor_get(v___x_3665_, 3);
v_traceState_3671_ = lean_ctor_get(v___x_3665_, 4);
v_cache_3672_ = lean_ctor_get(v___x_3665_, 5);
v_recordedDeps_3673_ = lean_ctor_get(v___x_3665_, 6);
v_messages_3674_ = lean_ctor_get(v___x_3665_, 7);
v_snapshotTasks_3675_ = lean_ctor_get(v___x_3665_, 9);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3677_ = v___x_3665_;
v_isShared_3678_ = v_isSharedCheck_3698_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_snapshotTasks_3675_);
lean_inc(v_infoState_3666_);
lean_inc(v_messages_3674_);
lean_inc(v_recordedDeps_3673_);
lean_inc(v_cache_3672_);
lean_inc(v_traceState_3671_);
lean_inc(v_auxDeclNGen_3670_);
lean_inc(v_ngen_3669_);
lean_inc(v_nextMacroScope_3668_);
lean_inc(v_env_3667_);
lean_dec(v___x_3665_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3698_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
uint8_t v_enabled_3679_; lean_object* v_assignment_3680_; lean_object* v_lazyAssignment_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3696_; 
v_enabled_3679_ = lean_ctor_get_uint8(v_infoState_3666_, sizeof(void*)*3);
v_assignment_3680_ = lean_ctor_get(v_infoState_3666_, 0);
v_lazyAssignment_3681_ = lean_ctor_get(v_infoState_3666_, 1);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_infoState_3666_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; 
v_unused_3697_ = lean_ctor_get(v_infoState_3666_, 2);
lean_dec(v_unused_3697_);
v___x_3683_ = v_infoState_3666_;
v_isShared_3684_ = v_isSharedCheck_3696_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_lazyAssignment_3681_);
lean_inc(v_assignment_3680_);
lean_dec(v_infoState_3666_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3696_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3685_ = lean_unsigned_to_nat(32u);
v___x_3686_ = lean_mk_empty_array_with_capacity(v___x_3685_);
lean_dec_ref(v___x_3686_);
v___x_3687_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 2, v___x_3687_);
v___x_3689_ = v___x_3683_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_assignment_3680_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_lazyAssignment_3681_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v___x_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3695_, sizeof(void*)*3, v_enabled_3679_);
v___x_3689_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3691_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 8, v___x_3689_);
v___x_3691_ = v___x_3677_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_env_3667_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_nextMacroScope_3668_);
lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_ngen_3669_);
lean_ctor_set(v_reuseFailAlloc_3694_, 3, v_auxDeclNGen_3670_);
lean_ctor_set(v_reuseFailAlloc_3694_, 4, v_traceState_3671_);
lean_ctor_set(v_reuseFailAlloc_3694_, 5, v_cache_3672_);
lean_ctor_set(v_reuseFailAlloc_3694_, 6, v_recordedDeps_3673_);
lean_ctor_set(v_reuseFailAlloc_3694_, 7, v_messages_3674_);
lean_ctor_set(v_reuseFailAlloc_3694_, 8, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3694_, 9, v_snapshotTasks_3675_);
v___x_3691_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = lean_st_ref_put(v___y_3660_, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v_trees_3664_);
return v___x_3693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3699_);
lean_dec(v___y_3699_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object* v_x_3702_, lean_object* v_ctx_x3f_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; lean_object* v_infoState_3712_; uint8_t v_enabled_3713_; 
v___x_3711_ = lean_st_ref_get(v___y_3709_);
v_infoState_3712_ = lean_ctor_get(v___x_3711_, 8);
lean_inc_ref(v_infoState_3712_);
lean_dec(v___x_3711_);
v_enabled_3713_ = lean_ctor_get_uint8(v_infoState_3712_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3712_);
if (v_enabled_3713_ == 0)
{
lean_object* v___x_3714_; 
lean_dec_ref(v_ctx_x3f_3703_);
lean_inc(v___y_3709_);
lean_inc_ref(v___y_3708_);
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3706_);
lean_inc(v___y_3705_);
lean_inc_ref(v___y_3704_);
v___x_3714_ = lean_apply_7(v_x_3702_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, lean_box(0));
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; lean_object* v_a_3716_; lean_object* v_r_3717_; 
v___x_3715_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3709_);
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref(v___x_3715_);
lean_inc(v___y_3709_);
lean_inc_ref(v___y_3708_);
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3706_);
lean_inc(v___y_3705_);
lean_inc_ref(v___y_3704_);
v_r_3717_ = lean_apply_7(v_x_3702_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, lean_box(0));
if (lean_obj_tag(v_r_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3742_; 
v_a_3718_ = lean_ctor_get(v_r_3717_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_r_3717_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3720_ = v_r_3717_;
v_isShared_3721_ = v_isSharedCheck_3742_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v_r_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3742_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
lean_inc(v_a_3718_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set_tag(v___x_3720_, 1);
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; 
v___x_3724_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3709_, v_ctx_x3f_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v_a_3716_, v___x_3723_);
lean_dec_ref(v___x_3723_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v___x_3724_, 0);
lean_dec(v_unused_3732_);
v___x_3726_ = v___x_3724_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v___x_3724_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v_a_3718_);
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3718_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v_a_3718_);
v_a_3733_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3724_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3724_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3743_ = lean_ctor_get(v_r_3717_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v_r_3717_, 1);
v___x_3744_ = lean_box(0);
v___x_3745_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3709_, v_ctx_x3f_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v_a_3716_, v___x_3744_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; 
v_unused_3753_ = lean_ctor_get(v___x_3745_, 0);
lean_dec(v_unused_3753_);
v___x_3747_ = v___x_3745_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_dec(v___x_3745_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set_tag(v___x_3747_, 1);
lean_ctor_set(v___x_3747_, 0, v_a_3743_);
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3743_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v_a_3743_);
v_a_3754_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3745_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3745_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_3762_, lean_object* v_ctx_x3f_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3762_, v_ctx_x3f_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; lean_object* v_env_3777_; lean_object* v___x_3778_; lean_object* v_toCold_3779_; lean_object* v_mctx_3780_; lean_object* v_currNamespace_3781_; lean_object* v_openDecls_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v_ngen_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3776_ = lean_st_ref_get(v___y_3774_);
v_env_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc_ref(v_env_3777_);
lean_dec(v___x_3776_);
v___x_3778_ = lean_st_ref_get(v___y_3772_);
v_toCold_3779_ = lean_ctor_get(v___y_3773_, 0);
v_mctx_3780_ = lean_ctor_get(v___x_3778_, 0);
lean_inc_ref(v_mctx_3780_);
lean_dec(v___x_3778_);
v_currNamespace_3781_ = lean_ctor_get(v_toCold_3779_, 4);
v_openDecls_3782_ = lean_ctor_get(v_toCold_3779_, 5);
v___x_3783_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3773_);
v___x_3784_ = lean_st_ref_get(v___y_3774_);
v_ngen_3785_ = lean_ctor_get(v___x_3784_, 2);
lean_inc_ref(v_ngen_3785_);
lean_dec(v___x_3784_);
v___x_3786_ = lean_box(0);
v___x_3787_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_3782_);
lean_inc(v_currNamespace_3781_);
v___x_3788_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3788_, 0, v_env_3777_);
lean_ctor_set(v___x_3788_, 1, v___x_3786_);
lean_ctor_set(v___x_3788_, 2, v___x_3787_);
lean_ctor_set(v___x_3788_, 3, v_mctx_3780_);
lean_ctor_set(v___x_3788_, 4, v___x_3783_);
lean_ctor_set(v___x_3788_, 5, v_currNamespace_3781_);
lean_ctor_set(v___x_3788_, 6, v_openDecls_3782_);
lean_ctor_set(v___x_3788_, 7, v_ngen_3785_);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; lean_object* v_toCold_3803_; lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3828_; 
v___x_3802_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3798_, v___y_3799_, v___y_3800_);
v_toCold_3803_ = lean_ctor_get(v___y_3799_, 0);
v_a_3804_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3806_ = v___x_3802_;
v_isShared_3807_ = v_isSharedCheck_3828_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3802_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3828_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v_fileMap_3808_; lean_object* v_env_3809_; lean_object* v_mctx_3810_; lean_object* v_options_3811_; lean_object* v_currNamespace_3812_; lean_object* v_openDecls_3813_; lean_object* v_ngen_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3825_; 
v_fileMap_3808_ = lean_ctor_get(v_toCold_3803_, 1);
v_env_3809_ = lean_ctor_get(v_a_3804_, 0);
v_mctx_3810_ = lean_ctor_get(v_a_3804_, 3);
v_options_3811_ = lean_ctor_get(v_a_3804_, 4);
v_currNamespace_3812_ = lean_ctor_get(v_a_3804_, 5);
v_openDecls_3813_ = lean_ctor_get(v_a_3804_, 6);
v_ngen_3814_ = lean_ctor_get(v_a_3804_, 7);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_a_3804_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; lean_object* v_unused_3827_; 
v_unused_3826_ = lean_ctor_get(v_a_3804_, 2);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_a_3804_, 1);
lean_dec(v_unused_3827_);
v___x_3816_ = v_a_3804_;
v_isShared_3817_ = v_isSharedCheck_3825_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_ngen_3814_);
lean_inc(v_openDecls_3813_);
lean_inc(v_currNamespace_3812_);
lean_inc(v_options_3811_);
lean_inc(v_mctx_3810_);
lean_inc(v_env_3809_);
lean_dec(v_a_3804_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3825_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v___x_3820_; 
v___x_3818_ = lean_box(0);
lean_inc_ref(v_fileMap_3808_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 2, v_fileMap_3808_);
lean_ctor_set(v___x_3816_, 1, v___x_3818_);
v___x_3820_ = v___x_3816_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_env_3809_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3824_, 2, v_fileMap_3808_);
lean_ctor_set(v_reuseFailAlloc_3824_, 3, v_mctx_3810_);
lean_ctor_set(v_reuseFailAlloc_3824_, 4, v_options_3811_);
lean_ctor_set(v_reuseFailAlloc_3824_, 5, v_currNamespace_3812_);
lean_ctor_set(v_reuseFailAlloc_3824_, 6, v_openDecls_3813_);
lean_ctor_set(v_reuseFailAlloc_3824_, 7, v_ngen_3814_);
v___x_3820_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3822_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3820_);
v___x_3822_ = v___x_3806_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___x_3844_; lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3854_; 
v___x_3844_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3847_ = v___x_3844_;
v_isShared_3848_ = v_isSharedCheck_3854_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3854_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v_a_3845_);
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3850_);
v___x_3852_ = v___x_3847_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object* v_x_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v___f_3872_; lean_object* v___x_3873_; 
v___f_3872_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0));
v___x_3873_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3864_, v___f_3872_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object* v_x_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object* v_00_u03b1_3883_, lean_object* v_x_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object* v_00_u03b1_3893_, lean_object* v_x_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(v_00_u03b1_3893_, v_x_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
return v_res_3902_;
}
}
static uint64_t _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5(void){
_start:
{
lean_object* v___x_3923_; uint64_t v___x_3924_; 
v___x_3923_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3924_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3923_);
return v___x_3924_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6(void){
_start:
{
uint64_t v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = lean_uint64_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5);
v___x_3926_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4));
v___x_3927_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set_uint64(v___x_3927_, sizeof(void*)*1, v___x_3925_);
return v___x_3927_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7(void){
_start:
{
uint8_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3928_ = 1;
v___x_3929_ = lean_unsigned_to_nat(0u);
v___x_3930_ = lean_box(0);
v___x_3931_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1));
v___x_3932_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_3933_ = lean_box(1);
v___x_3934_ = 0;
v___x_3935_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6);
v___x_3936_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
lean_ctor_set(v___x_3936_, 1, v___x_3933_);
lean_ctor_set(v___x_3936_, 2, v___x_3932_);
lean_ctor_set(v___x_3936_, 3, v___x_3931_);
lean_ctor_set(v___x_3936_, 4, v___x_3930_);
lean_ctor_set(v___x_3936_, 5, v___x_3929_);
lean_ctor_set(v___x_3936_, 6, v___x_3930_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*7, v___x_3934_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*7 + 1, v___x_3934_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*7 + 2, v___x_3934_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*7 + 3, v___x_3928_);
return v___x_3936_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3937_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3938_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3939_ = lean_unsigned_to_nat(0u);
v___x_3940_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
lean_ctor_set(v___x_3940_, 2, v___x_3939_);
lean_ctor_set(v___x_3940_, 3, v___x_3939_);
lean_ctor_set(v___x_3940_, 4, v___x_3938_);
lean_ctor_set(v___x_3940_, 5, v___x_3938_);
lean_ctor_set(v___x_3940_, 6, v___x_3938_);
lean_ctor_set(v___x_3940_, 7, v___x_3938_);
lean_ctor_set(v___x_3940_, 8, v___x_3938_);
lean_ctor_set(v___x_3940_, 9, v___x_3938_);
lean_ctor_set(v___x_3940_, 10, v___x_3938_);
lean_ctor_set(v___x_3940_, 11, v___x_3937_);
return v___x_3940_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3942_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
lean_ctor_set(v___x_3942_, 2, v___x_3941_);
lean_ctor_set(v___x_3942_, 3, v___x_3941_);
lean_ctor_set(v___x_3942_, 4, v___x_3941_);
lean_ctor_set(v___x_3942_, 5, v___x_3941_);
return v___x_3942_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_3944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
lean_ctor_set(v___x_3944_, 2, v___x_3943_);
lean_ctor_set(v___x_3944_, 3, v___x_3943_);
lean_ctor_set(v___x_3944_, 4, v___x_3943_);
return v___x_3944_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3945_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10);
v___x_3946_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_3947_ = lean_box(1);
v___x_3948_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
v___x_3949_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8);
v___x_3950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
lean_ctor_set(v___x_3950_, 1, v___x_3948_);
lean_ctor_set(v___x_3950_, 2, v___x_3947_);
lean_ctor_set(v___x_3950_, 3, v___x_3946_);
lean_ctor_set(v___x_3950_, 4, v___x_3945_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object* v_mx_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3955_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed), 9, 2);
lean_closure_set(v___x_3955_, 0, lean_box(0));
lean_closure_set(v___x_3955_, 1, v_mx_3951_);
v___x_3956_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2));
v___x_3957_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3958_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7);
v___x_3959_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11);
v___x_3960_ = lean_st_mk_ref(v___x_3959_);
v___x_3961_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3955_, v___x_3956_, v___x_3957_, v___x_3958_, v___x_3960_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3971_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3971_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3971_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v_fst_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v_fst_3966_ = lean_ctor_get(v_a_3962_, 0);
lean_inc(v_fst_3966_);
lean_dec(v_a_3962_);
v___x_3967_ = lean_st_ref_get(v___x_3960_);
lean_dec(v___x_3960_);
lean_dec(v___x_3967_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v_fst_3966_);
v___x_3969_ = v___x_3964_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_fst_3966_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v___x_3960_);
v_a_3972_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3961_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3961_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object* v_mx_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3980_, v_a_3981_, v_a_3982_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object* v_00_u03b1_3985_, lean_object* v_mx_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_3986_, v_a_3987_, v_a_3988_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object* v_00_u03b1_3991_, lean_object* v_mx_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_3991_, v_mx_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_4018_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object* v_00_u03b1_4029_, lean_object* v_x_4030_, lean_object* v_ctx_x3f_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_4030_, v_ctx_x3f_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4040_, lean_object* v_x_4041_, lean_object* v_ctx_x3f_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_4040_, v_x_4041_, v_ctx_x3f_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object* v_eval_4051_, uint8_t v_logExceptions_4052_, lean_object* v_onErr_4053_, lean_object* v_init_4054_, lean_object* v_cfg_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_4051_, v_logExceptions_4052_, v_onErr_4053_, v_init_4054_, v_cfg_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object* v_eval_4064_, lean_object* v_logExceptions_4065_, lean_object* v_onErr_4066_, lean_object* v_init_4067_, lean_object* v_cfg_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v_logExceptions_boxed_4076_; lean_object* v_res_4077_; 
v_logExceptions_boxed_4076_ = lean_unbox(v_logExceptions_4065_);
v_res_4077_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4064_, v_logExceptions_boxed_4076_, v_onErr_4066_, v_init_4067_, v_cfg_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object* v_eval_4078_, lean_object* v_init_4079_, lean_object* v_cfg_4080_, lean_object* v_onErr_4081_, uint8_t v_logExceptions_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; lean_object* v___f_4087_; uint8_t v___y_4089_; lean_object* v___x_4092_; uint8_t v___x_4093_; 
v___x_4086_ = lean_box(v_logExceptions_4082_);
lean_inc_n(v_cfg_4080_, 2);
lean_inc(v_init_4079_);
v___f_4087_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4087_, 0, v_eval_4078_);
lean_closure_set(v___f_4087_, 1, v___x_4086_);
lean_closure_set(v___f_4087_, 2, v_onErr_4081_);
lean_closure_set(v___f_4087_, 3, v_init_4079_);
lean_closure_set(v___f_4087_, 4, v_cfg_4080_);
v___x_4092_ = lean_unsigned_to_nat(0u);
v___x_4093_ = l_Lean_Syntax_matchesNull(v_cfg_4080_, v___x_4092_);
if (v___x_4093_ == 0)
{
lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; 
v___x_4094_ = l_Lean_Syntax_getNumArgs(v_cfg_4080_);
v___x_4095_ = lean_unsigned_to_nat(1u);
v___x_4096_ = lean_nat_dec_eq(v___x_4094_, v___x_4095_);
lean_dec(v___x_4094_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; 
lean_dec(v_cfg_4080_);
lean_dec(v_init_4079_);
v___x_4097_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4087_, v_a_4083_, v_a_4084_);
return v___x_4097_;
}
else
{
lean_object* v___x_4098_; uint8_t v___x_4099_; 
v___x_4098_ = l_Lean_Syntax_getArg(v_cfg_4080_, v___x_4092_);
lean_dec(v_cfg_4080_);
v___x_4099_ = l_Lean_Syntax_matchesNull(v___x_4098_, v___x_4092_);
v___y_4089_ = v___x_4099_;
goto v___jp_4088_;
}
}
else
{
lean_dec(v_cfg_4080_);
v___y_4089_ = v___x_4093_;
goto v___jp_4088_;
}
v___jp_4088_:
{
if (v___y_4089_ == 0)
{
lean_object* v___x_4090_; 
lean_dec(v_init_4079_);
v___x_4090_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4087_, v_a_4083_, v_a_4084_);
return v___x_4090_;
}
else
{
lean_object* v___x_4091_; 
lean_dec_ref(v___f_4087_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_init_4079_);
return v___x_4091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object* v_eval_4100_, lean_object* v_init_4101_, lean_object* v_cfg_4102_, lean_object* v_onErr_4103_, lean_object* v_logExceptions_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
uint8_t v_logExceptions_boxed_4108_; lean_object* v_res_4109_; 
v_logExceptions_boxed_4108_ = lean_unbox(v_logExceptions_4104_);
v_res_4109_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4100_, v_init_4101_, v_cfg_4102_, v_onErr_4103_, v_logExceptions_boxed_4108_, v_a_4105_, v_a_4106_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object* v_00_u03b1_4110_, lean_object* v_eval_4111_, lean_object* v_init_4112_, lean_object* v_cfg_4113_, lean_object* v_onErr_4114_, uint8_t v_logExceptions_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4111_, v_init_4112_, v_cfg_4113_, v_onErr_4114_, v_logExceptions_4115_, v_a_4116_, v_a_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object* v_00_u03b1_4120_, lean_object* v_eval_4121_, lean_object* v_init_4122_, lean_object* v_cfg_4123_, lean_object* v_onErr_4124_, lean_object* v_logExceptions_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
uint8_t v_logExceptions_boxed_4129_; lean_object* v_res_4130_; 
v_logExceptions_boxed_4129_ = lean_unbox(v_logExceptions_4125_);
v_res_4130_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(v_00_u03b1_4120_, v_eval_4121_, v_init_4122_, v_cfg_4123_, v_onErr_4124_, v_logExceptions_boxed_4129_, v_a_4126_, v_a_4127_);
lean_dec(v_a_4127_);
lean_dec_ref(v_a_4126_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object* v_eval_4131_, uint8_t v_logExceptions_4132_, lean_object* v_onErr_4133_, lean_object* v_init_4134_, lean_object* v_cfgs_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_4131_, v_logExceptions_4132_, v_onErr_4133_, v_init_4134_, v_cfgs_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object* v_eval_4144_, lean_object* v_logExceptions_4145_, lean_object* v_onErr_4146_, lean_object* v_init_4147_, lean_object* v_cfgs_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
uint8_t v_logExceptions_boxed_4156_; lean_object* v_res_4157_; 
v_logExceptions_boxed_4156_ = lean_unbox(v_logExceptions_4145_);
v_res_4157_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4144_, v_logExceptions_boxed_4156_, v_onErr_4146_, v_init_4147_, v_cfgs_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec_ref(v_cfgs_4148_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object* v_eval_4158_, lean_object* v_init_4159_, lean_object* v_cfgs_4160_, lean_object* v_onErr_4161_, uint8_t v_logExceptions_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; 
v___x_4166_ = lean_array_get_size(v_cfgs_4160_);
v___x_4167_ = lean_unsigned_to_nat(0u);
v___x_4168_ = lean_nat_dec_eq(v___x_4166_, v___x_4167_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4169_; lean_object* v___f_4170_; lean_object* v___x_4171_; 
v___x_4169_ = lean_box(v_logExceptions_4162_);
v___f_4170_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4170_, 0, v_eval_4158_);
lean_closure_set(v___f_4170_, 1, v___x_4169_);
lean_closure_set(v___f_4170_, 2, v_onErr_4161_);
lean_closure_set(v___f_4170_, 3, v_init_4159_);
lean_closure_set(v___f_4170_, 4, v_cfgs_4160_);
v___x_4171_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4170_, v_a_4163_, v_a_4164_);
return v___x_4171_;
}
else
{
lean_object* v___x_4172_; 
lean_dec_ref(v_onErr_4161_);
lean_dec_ref(v_cfgs_4160_);
lean_dec_ref(v_eval_4158_);
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v_init_4159_);
return v___x_4172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object* v_eval_4173_, lean_object* v_init_4174_, lean_object* v_cfgs_4175_, lean_object* v_onErr_4176_, lean_object* v_logExceptions_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
uint8_t v_logExceptions_boxed_4181_; lean_object* v_res_4182_; 
v_logExceptions_boxed_4181_ = lean_unbox(v_logExceptions_4177_);
v_res_4182_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4173_, v_init_4174_, v_cfgs_4175_, v_onErr_4176_, v_logExceptions_boxed_4181_, v_a_4178_, v_a_4179_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object* v_00_u03b1_4183_, lean_object* v_eval_4184_, lean_object* v_init_4185_, lean_object* v_cfgs_4186_, lean_object* v_onErr_4187_, uint8_t v_logExceptions_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4184_, v_init_4185_, v_cfgs_4186_, v_onErr_4187_, v_logExceptions_4188_, v_a_4189_, v_a_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object* v_00_u03b1_4193_, lean_object* v_eval_4194_, lean_object* v_init_4195_, lean_object* v_cfgs_4196_, lean_object* v_onErr_4197_, lean_object* v_logExceptions_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
uint8_t v_logExceptions_boxed_4202_; lean_object* v_res_4203_; 
v_logExceptions_boxed_4202_ = lean_unbox(v_logExceptions_4198_);
v_res_4203_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(v_00_u03b1_4193_, v_eval_4194_, v_init_4195_, v_cfgs_4196_, v_onErr_4197_, v_logExceptions_boxed_4202_, v_a_4199_, v_a_4200_);
lean_dec(v_a_4200_);
lean_dec_ref(v_a_4199_);
return v_res_4203_;
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

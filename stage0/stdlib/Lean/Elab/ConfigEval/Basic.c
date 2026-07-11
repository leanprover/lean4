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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_identComponents(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5;
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
static const lean_ctor_object l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11_value;
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
lean_object* v_evalTerm_10_; lean_object* v_fileName_11_; lean_object* v_fileMap_12_; lean_object* v_options_13_; lean_object* v_currRecDepth_14_; lean_object* v_maxRecDepth_15_; lean_object* v_ref_16_; lean_object* v_currNamespace_17_; lean_object* v_openDecls_18_; lean_object* v_initHeartbeats_19_; lean_object* v_maxHeartbeats_20_; lean_object* v_quotContext_21_; lean_object* v_currMacroScope_22_; uint8_t v_diag_23_; lean_object* v_cancelTk_x3f_24_; uint8_t v_suppressElabErrors_25_; lean_object* v_inheritedTraceOptions_26_; lean_object* v_ref_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_evalTerm_10_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_evalTerm_10_);
lean_dec_ref(v_inst_1_);
v_fileName_11_ = lean_ctor_get(v_a_7_, 0);
v_fileMap_12_ = lean_ctor_get(v_a_7_, 1);
v_options_13_ = lean_ctor_get(v_a_7_, 2);
v_currRecDepth_14_ = lean_ctor_get(v_a_7_, 3);
v_maxRecDepth_15_ = lean_ctor_get(v_a_7_, 4);
v_ref_16_ = lean_ctor_get(v_a_7_, 5);
v_currNamespace_17_ = lean_ctor_get(v_a_7_, 6);
v_openDecls_18_ = lean_ctor_get(v_a_7_, 7);
v_initHeartbeats_19_ = lean_ctor_get(v_a_7_, 8);
v_maxHeartbeats_20_ = lean_ctor_get(v_a_7_, 9);
v_quotContext_21_ = lean_ctor_get(v_a_7_, 10);
v_currMacroScope_22_ = lean_ctor_get(v_a_7_, 11);
v_diag_23_ = lean_ctor_get_uint8(v_a_7_, sizeof(void*)*14);
v_cancelTk_x3f_24_ = lean_ctor_get(v_a_7_, 12);
v_suppressElabErrors_25_ = lean_ctor_get_uint8(v_a_7_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_26_ = lean_ctor_get(v_a_7_, 13);
v_ref_27_ = l_Lean_replaceRef(v_stx_2_, v_ref_16_);
lean_inc_ref(v_inheritedTraceOptions_26_);
lean_inc(v_cancelTk_x3f_24_);
lean_inc(v_currMacroScope_22_);
lean_inc(v_quotContext_21_);
lean_inc(v_maxHeartbeats_20_);
lean_inc(v_initHeartbeats_19_);
lean_inc(v_openDecls_18_);
lean_inc(v_currNamespace_17_);
lean_inc(v_maxRecDepth_15_);
lean_inc(v_currRecDepth_14_);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_fileMap_12_);
lean_inc_ref(v_fileName_11_);
v___x_28_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_28_, 0, v_fileName_11_);
lean_ctor_set(v___x_28_, 1, v_fileMap_12_);
lean_ctor_set(v___x_28_, 2, v_options_13_);
lean_ctor_set(v___x_28_, 3, v_currRecDepth_14_);
lean_ctor_set(v___x_28_, 4, v_maxRecDepth_15_);
lean_ctor_set(v___x_28_, 5, v_ref_27_);
lean_ctor_set(v___x_28_, 6, v_currNamespace_17_);
lean_ctor_set(v___x_28_, 7, v_openDecls_18_);
lean_ctor_set(v___x_28_, 8, v_initHeartbeats_19_);
lean_ctor_set(v___x_28_, 9, v_maxHeartbeats_20_);
lean_ctor_set(v___x_28_, 10, v_quotContext_21_);
lean_ctor_set(v___x_28_, 11, v_currMacroScope_22_);
lean_ctor_set(v___x_28_, 12, v_cancelTk_x3f_24_);
lean_ctor_set(v___x_28_, 13, v_inheritedTraceOptions_26_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*14, v_diag_23_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*14 + 1, v_suppressElabErrors_25_);
lean_inc(v_a_8_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_29_ = lean_apply_8(v_evalTerm_10_, v_stx_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v___x_28_, v_a_8_, lean_box(0));
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_38_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_38_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_38_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_38_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v_fst_34_; lean_object* v___x_36_; 
v_fst_34_ = lean_ctor_get(v_a_30_, 0);
lean_inc(v_fst_34_);
lean_dec(v_a_30_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v_fst_34_);
v___x_36_ = v___x_32_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_fst_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_29_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_29_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___redArg___boxed(lean_object* v_inst_47_, lean_object* v_stx_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_47_, v_stx_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_stx_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_ConfigEval_evalTermWithRef___redArg(v_inst_58_, v_stx_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermWithRef___boxed(lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_stx_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Elab_ConfigEval_evalTermWithRef(v_00_u03b1_68_, v_inst_69_, v_stx_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_78_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_instMonadEIO(lean_box(0));
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__0);
v___x_81_ = l_StateRefT_x27_instMonad___redArg(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_90_; lean_object* v___f_91_; 
v___x_90_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_91_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_91_, 0, v___x_90_);
return v___f_91_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11(void){
_start:
{
lean_object* v___x_92_; lean_object* v___f_93_; 
v___x_92_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_93_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_93_, 0, v___x_92_);
return v___f_93_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12(void){
_start:
{
lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; 
v___f_94_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__11);
v___f_95_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__10);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___f_95_);
lean_ctor_set(v___x_96_, 1, v___f_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13(void){
_start:
{
lean_object* v___x_97_; lean_object* v___f_98_; 
v___x_97_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_98_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_98_, 0, v___x_97_);
return v___f_98_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14(void){
_start:
{
lean_object* v___x_99_; lean_object* v___f_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__12);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_100_, 0, v___x_99_);
return v___f_100_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15(void){
_start:
{
lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___x_103_; 
v___f_101_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__14);
v___f_102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__13);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___f_102_);
lean_ctor_set(v___x_103_, 1, v___f_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16(void){
_start:
{
lean_object* v___x_104_; lean_object* v___f_105_; 
v___x_104_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_105_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_105_, 0, v___x_104_);
return v___f_105_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17(void){
_start:
{
lean_object* v___x_106_; lean_object* v___f_107_; 
v___x_106_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__15);
v___f_107_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_107_, 0, v___x_106_);
return v___f_107_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18(void){
_start:
{
lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v___f_108_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__17);
v___f_109_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__16);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___f_109_);
lean_ctor_set(v___x_110_, 1, v___f_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_112_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20(void){
_start:
{
lean_object* v___x_113_; lean_object* v___f_114_; 
v___x_113_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__18);
v___f_114_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_114_, 0, v___x_113_);
return v___f_114_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21(void){
_start:
{
lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___x_117_; 
v___f_115_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__20);
v___f_116_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__19);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___f_116_);
lean_ctor_set(v___x_117_, 1, v___f_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_119_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__23));
v___x_122_ = l_Lean_stringToMessageData(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__25));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__27));
v___x_128_ = l_Lean_stringToMessageData(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__31));
v___x_134_ = l_Lean_stringToMessageData(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(lean_object* v_inst_135_, lean_object* v_stx_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_144_; lean_object* v_toApplicative_145_; lean_object* v_toFunctor_146_; lean_object* v_toSeq_147_; lean_object* v_toSeqLeft_148_; lean_object* v_toSeqRight_149_; lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_toApplicative_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_411_; 
v___x_144_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__1);
v_toApplicative_145_ = lean_ctor_get(v___x_144_, 0);
v_toFunctor_146_ = lean_ctor_get(v_toApplicative_145_, 0);
v_toSeq_147_ = lean_ctor_get(v_toApplicative_145_, 2);
v_toSeqLeft_148_ = lean_ctor_get(v_toApplicative_145_, 3);
v_toSeqRight_149_ = lean_ctor_get(v_toApplicative_145_, 4);
v___f_150_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__2));
v___f_151_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_146_, 2);
v___f_152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_152_, 0, v_toFunctor_146_);
v___f_153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_153_, 0, v_toFunctor_146_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___f_152_);
lean_ctor_set(v___x_154_, 1, v___f_153_);
lean_inc(v_toSeqRight_149_);
v___f_155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_155_, 0, v_toSeqRight_149_);
lean_inc(v_toSeqLeft_148_);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_156_, 0, v_toSeqLeft_148_);
lean_inc(v_toSeq_147_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_157_, 0, v_toSeq_147_);
v___x_158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_158_, 0, v___x_154_);
lean_ctor_set(v___x_158_, 1, v___f_150_);
lean_ctor_set(v___x_158_, 2, v___f_157_);
lean_ctor_set(v___x_158_, 3, v___f_156_);
lean_ctor_set(v___x_158_, 4, v___f_155_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___f_151_);
v___x_160_ = l_StateRefT_x27_instMonad___redArg(v___x_159_);
v_toApplicative_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_160_, 1);
lean_dec(v_unused_412_);
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_411_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_toApplicative_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_411_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_toFunctor_165_; lean_object* v_toSeq_166_; lean_object* v_toSeqLeft_167_; lean_object* v_toSeqRight_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_409_; 
v_toFunctor_165_ = lean_ctor_get(v_toApplicative_161_, 0);
v_toSeq_166_ = lean_ctor_get(v_toApplicative_161_, 2);
v_toSeqLeft_167_ = lean_ctor_get(v_toApplicative_161_, 3);
v_toSeqRight_168_ = lean_ctor_get(v_toApplicative_161_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v_toApplicative_161_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v_toApplicative_161_, 1);
lean_dec(v_unused_410_);
v___x_170_ = v_toApplicative_161_;
v_isShared_171_ = v_isSharedCheck_409_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_toSeqRight_168_);
lean_inc(v_toSeqLeft_167_);
lean_inc(v_toSeq_166_);
lean_inc(v_toFunctor_165_);
lean_dec(v_toApplicative_161_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_409_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_181_; 
v___f_172_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__4));
v___f_173_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__5));
lean_inc_ref(v_toFunctor_165_);
v___f_174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_174_, 0, v_toFunctor_165_);
v___f_175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_175_, 0, v_toFunctor_165_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___f_174_);
lean_ctor_set(v___x_176_, 1, v___f_175_);
v___f_177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_177_, 0, v_toSeqRight_168_);
v___f_178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_178_, 0, v_toSeqLeft_167_);
v___f_179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_179_, 0, v_toSeq_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___f_177_);
lean_ctor_set(v___x_170_, 3, v___f_178_);
lean_ctor_set(v___x_170_, 2, v___f_179_);
lean_ctor_set(v___x_170_, 1, v___f_172_);
lean_ctor_set(v___x_170_, 0, v___x_176_);
v___x_181_ = v___x_170_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___f_172_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v___f_179_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v___f_178_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___f_177_);
v___x_181_ = v_reuseFailAlloc_408_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___f_173_);
lean_ctor_set(v___x_163_, 0, v___x_181_);
v___x_183_ = v___x_163_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___f_173_);
v___x_183_ = v_reuseFailAlloc_407_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v_toApplicative_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_405_; 
v___x_184_ = l_StateRefT_x27_instMonad___redArg(v___x_183_);
v_toApplicative_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_184_, 1);
lean_dec(v_unused_406_);
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_405_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_toApplicative_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_405_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_toFunctor_189_; lean_object* v_toSeq_190_; lean_object* v_toSeqLeft_191_; lean_object* v_toSeqRight_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_403_; 
v_toFunctor_189_ = lean_ctor_get(v_toApplicative_185_, 0);
v_toSeq_190_ = lean_ctor_get(v_toApplicative_185_, 2);
v_toSeqLeft_191_ = lean_ctor_get(v_toApplicative_185_, 3);
v_toSeqRight_192_ = lean_ctor_get(v_toApplicative_185_, 4);
v_isSharedCheck_403_ = !lean_is_exclusive(v_toApplicative_185_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_toApplicative_185_, 1);
lean_dec(v_unused_404_);
v___x_194_ = v_toApplicative_185_;
v_isShared_195_ = v_isSharedCheck_403_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_toSeqRight_192_);
lean_inc(v_toSeqLeft_191_);
lean_inc(v_toSeq_190_);
lean_inc(v_toFunctor_189_);
lean_dec(v_toApplicative_185_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_403_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_205_; 
v___f_196_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__6));
v___f_197_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__7));
lean_inc_ref(v_toFunctor_189_);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_198_, 0, v_toFunctor_189_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_199_, 0, v_toFunctor_189_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___f_198_);
lean_ctor_set(v___x_200_, 1, v___f_199_);
v___f_201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_201_, 0, v_toSeqRight_192_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_202_, 0, v_toSeqLeft_191_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_203_, 0, v_toSeq_190_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 4, v___f_201_);
lean_ctor_set(v___x_194_, 3, v___f_202_);
lean_ctor_set(v___x_194_, 2, v___f_203_);
lean_ctor_set(v___x_194_, 1, v___f_196_);
lean_ctor_set(v___x_194_, 0, v___x_200_);
v___x_205_ = v___x_194_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___f_196_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v___f_203_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v___f_202_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___f_201_);
v___x_205_ = v_reuseFailAlloc_402_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___f_197_);
lean_ctor_set(v___x_187_, 0, v___x_205_);
v___x_207_ = v___x_187_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___f_197_);
v___x_207_ = v_reuseFailAlloc_401_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v_toMonadQuotation_209_; lean_object* v_toMonadRef_210_; lean_object* v___x_211_; lean_object* v_getMCtx_212_; lean_object* v_modifyMCtx_213_; lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_evalExpr_225_; lean_object* v_expectedType_x3f_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_400_; 
v___x_208_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
v_toMonadQuotation_209_ = lean_ctor_get(v___x_208_, 0);
v_toMonadRef_210_ = lean_ctor_get(v_toMonadQuotation_209_, 0);
v___x_211_ = l_Lean_Meta_instMonadMCtxMetaM;
v_getMCtx_212_ = lean_ctor_get(v___x_211_, 0);
v_modifyMCtx_213_ = lean_ctor_get(v___x_211_, 1);
v___f_214_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__8));
v___x_215_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__9));
lean_inc(v_modifyMCtx_213_);
v___f_216_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_216_, 0, v_modifyMCtx_213_);
lean_closure_set(v___f_216_, 1, v___x_215_);
lean_inc(v_getMCtx_212_);
v___x_217_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_217_, 0, lean_box(0));
lean_closure_set(v___x_217_, 1, lean_box(0));
lean_closure_set(v___x_217_, 2, lean_box(0));
lean_closure_set(v___x_217_, 3, lean_box(0));
lean_closure_set(v___x_217_, 4, v_getMCtx_212_);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_218_, 0, v___f_216_);
lean_closure_set(v___f_218_, 1, v___f_214_);
v___x_219_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_219_, 0, lean_box(0));
lean_closure_set(v___x_219_, 1, v___x_217_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___f_218_);
v___x_221_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__21);
v___x_222_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
lean_inc_ref(v_toMonadRef_210_);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v_toMonadRef_210_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__22);
v_evalExpr_225_ = lean_ctor_get(v_inst_135_, 0);
v_expectedType_x3f_226_ = lean_ctor_get(v_inst_135_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_inst_135_);
if (v_isSharedCheck_400_ == 0)
{
v___x_228_ = v_inst_135_;
v_isShared_229_ = v_isSharedCheck_400_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_expectedType_x3f_226_);
lean_inc(v_evalExpr_225_);
lean_dec(v_inst_135_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_400_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_fileName_235_; lean_object* v_fileMap_236_; lean_object* v_options_237_; lean_object* v_currRecDepth_238_; lean_object* v_maxRecDepth_239_; lean_object* v_ref_240_; lean_object* v_currNamespace_241_; lean_object* v_openDecls_242_; lean_object* v_initHeartbeats_243_; lean_object* v_maxHeartbeats_244_; lean_object* v_quotContext_245_; lean_object* v_currMacroScope_246_; uint8_t v_diag_247_; lean_object* v_cancelTk_x3f_248_; uint8_t v_suppressElabErrors_249_; lean_object* v_inheritedTraceOptions_250_; uint8_t v___x_251_; lean_object* v_ref_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_230_ = 1;
v___x_231_ = lean_box(0);
v___x_232_ = lean_box(v___x_230_);
v___x_233_ = lean_box(v___x_230_);
lean_inc(v_expectedType_x3f_226_);
lean_inc(v_stx_136_);
v___x_234_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_234_, 0, v_stx_136_);
lean_closure_set(v___x_234_, 1, v_expectedType_x3f_226_);
lean_closure_set(v___x_234_, 2, v___x_232_);
lean_closure_set(v___x_234_, 3, v___x_233_);
lean_closure_set(v___x_234_, 4, v___x_231_);
v_fileName_235_ = lean_ctor_get(v_a_141_, 0);
v_fileMap_236_ = lean_ctor_get(v_a_141_, 1);
v_options_237_ = lean_ctor_get(v_a_141_, 2);
v_currRecDepth_238_ = lean_ctor_get(v_a_141_, 3);
v_maxRecDepth_239_ = lean_ctor_get(v_a_141_, 4);
v_ref_240_ = lean_ctor_get(v_a_141_, 5);
v_currNamespace_241_ = lean_ctor_get(v_a_141_, 6);
v_openDecls_242_ = lean_ctor_get(v_a_141_, 7);
v_initHeartbeats_243_ = lean_ctor_get(v_a_141_, 8);
v_maxHeartbeats_244_ = lean_ctor_get(v_a_141_, 9);
v_quotContext_245_ = lean_ctor_get(v_a_141_, 10);
v_currMacroScope_246_ = lean_ctor_get(v_a_141_, 11);
v_diag_247_ = lean_ctor_get_uint8(v_a_141_, sizeof(void*)*14);
v_cancelTk_x3f_248_ = lean_ctor_get(v_a_141_, 12);
v_suppressElabErrors_249_ = lean_ctor_get_uint8(v_a_141_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_250_ = lean_ctor_get(v_a_141_, 13);
v___x_251_ = 1;
v_ref_252_ = l_Lean_replaceRef(v_stx_136_, v_ref_240_);
lean_dec(v_stx_136_);
lean_inc_ref(v_inheritedTraceOptions_250_);
lean_inc(v_cancelTk_x3f_248_);
lean_inc(v_currMacroScope_246_);
lean_inc(v_quotContext_245_);
lean_inc(v_maxHeartbeats_244_);
lean_inc(v_initHeartbeats_243_);
lean_inc(v_openDecls_242_);
lean_inc(v_currNamespace_241_);
lean_inc(v_maxRecDepth_239_);
lean_inc(v_currRecDepth_238_);
lean_inc_ref(v_options_237_);
lean_inc_ref(v_fileMap_236_);
lean_inc_ref(v_fileName_235_);
v___x_253_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_253_, 0, v_fileName_235_);
lean_ctor_set(v___x_253_, 1, v_fileMap_236_);
lean_ctor_set(v___x_253_, 2, v_options_237_);
lean_ctor_set(v___x_253_, 3, v_currRecDepth_238_);
lean_ctor_set(v___x_253_, 4, v_maxRecDepth_239_);
lean_ctor_set(v___x_253_, 5, v_ref_252_);
lean_ctor_set(v___x_253_, 6, v_currNamespace_241_);
lean_ctor_set(v___x_253_, 7, v_openDecls_242_);
lean_ctor_set(v___x_253_, 8, v_initHeartbeats_243_);
lean_ctor_set(v___x_253_, 9, v_maxHeartbeats_244_);
lean_ctor_set(v___x_253_, 10, v_quotContext_245_);
lean_ctor_set(v___x_253_, 11, v_currMacroScope_246_);
lean_ctor_set(v___x_253_, 12, v_cancelTk_x3f_248_);
lean_ctor_set(v___x_253_, 13, v_inheritedTraceOptions_250_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*14, v_diag_247_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*14 + 1, v_suppressElabErrors_249_);
v___x_254_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_234_, v___x_251_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v___x_253_, v_a_142_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_3751__overap_256_; lean_object* v___x_257_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
lean_inc_ref(v___x_207_);
v___x_3751__overap_256_ = l_Lean_instantiateMVars___redArg(v___x_207_, v___x_220_, v_a_255_);
lean_inc(v_a_142_);
lean_inc_ref(v___x_253_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_a_138_);
lean_inc_ref(v_a_137_);
v___x_257_ = lean_apply_7(v___x_3751__overap_256_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v___x_253_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; uint8_t v___x_372_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v___x_372_ = l_Lean_Expr_hasSorry(v_a_258_);
if (v___x_372_ == 0)
{
v___y_315_ = v_a_137_;
v___y_316_ = v_a_138_;
v___y_317_ = v_a_139_;
v___y_318_ = v_a_140_;
v___y_319_ = v___x_253_;
v___y_320_ = v_a_142_;
goto v___jp_314_;
}
else
{
uint8_t v___x_373_; 
v___x_373_ = l_Lean_Expr_hasSyntheticSorry(v_a_258_);
if (v___x_373_ == 0)
{
v___y_353_ = v_a_137_;
v___y_354_ = v_a_138_;
v___y_355_ = v_a_139_;
v___y_356_ = v_a_140_;
v___y_357_ = v___x_253_;
v___y_358_ = v_a_142_;
goto v___jp_352_;
}
else
{
lean_object* v___x_3959__overap_374_; lean_object* v___x_375_; 
v___x_3959__overap_374_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_224_);
lean_inc(v_a_142_);
lean_inc_ref(v___x_253_);
lean_inc(v_a_140_);
lean_inc_ref(v_a_139_);
lean_inc(v_a_138_);
lean_inc_ref(v_a_137_);
v___x_375_ = lean_apply_7(v___x_3959__overap_374_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v___x_253_, v_a_142_, lean_box(0));
if (lean_obj_tag(v___x_375_) == 0)
{
lean_dec_ref_known(v___x_375_, 1);
v___y_353_ = v_a_137_;
v___y_354_ = v_a_138_;
v___y_355_ = v_a_139_;
v___y_356_ = v_a_140_;
v___y_357_ = v___x_253_;
v___y_358_ = v_a_142_;
goto v___jp_352_;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_a_258_);
lean_dec_ref_known(v___x_253_, 14);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref(v_evalExpr_225_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
v___jp_259_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_267_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__24);
v___x_268_ = l_Lean_indentExpr(v_a_258_);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 7);
lean_ctor_set(v___x_228_, 1, v___x_268_);
lean_ctor_set(v___x_228_, 0, v___x_267_);
v___x_270_ = v___x_228_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_274_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; lean_object* v___x_3802__overap_272_; lean_object* v___x_273_; 
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___y_266_);
v___x_3802__overap_272_ = l_Lean_throwError___redArg(v___x_207_, v___x_223_, v___x_271_);
lean_inc(v___y_264_);
lean_inc(v___y_260_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_265_);
v___x_273_ = lean_apply_7(v___x_3802__overap_272_, v___y_265_, v___y_262_, v___y_263_, v___y_260_, v___y_261_, v___y_264_, lean_box(0));
return v___x_273_;
}
}
v___jp_275_:
{
if (v___y_285_ == 0)
{
if (lean_obj_tag(v___y_279_) == 0)
{
lean_dec_ref_known(v___y_279_, 2);
lean_dec_ref(v___y_280_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
return v___y_278_;
}
else
{
lean_object* v_id_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_300_; 
v_id_286_ = lean_ctor_get(v___y_279_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___y_279_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___y_279_, 1);
lean_dec(v_unused_301_);
v___x_288_ = v___y_279_;
v_isShared_289_ = v_isSharedCheck_300_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_id_286_);
lean_dec(v___y_279_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_300_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___x_290_; 
v___x_290_ = l_Lean_instBEqInternalExceptionId_beq(v___y_277_, v_id_286_);
lean_dec(v_id_286_);
if (v___x_290_ == 0)
{
lean_del_object(v___x_288_);
lean_dec_ref(v___y_280_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
return v___y_278_;
}
else
{
lean_dec_ref(v___y_278_);
if (lean_obj_tag(v_expectedType_x3f_226_) == 1)
{
lean_object* v_val_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v_val_291_ = lean_ctor_get(v_expectedType_x3f_226_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v_expectedType_x3f_226_, 1);
v___x_292_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__26);
v___x_293_ = l_Lean_MessageData_ofExpr(v_val_291_);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 7);
lean_ctor_set(v___x_288_, 1, v___x_293_);
lean_ctor_set(v___x_288_, 0, v___x_292_);
v___x_295_ = v___x_288_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_298_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___y_260_ = v___y_276_;
v___y_261_ = v___y_280_;
v___y_262_ = v___y_281_;
v___y_263_ = v___y_282_;
v___y_264_ = v___y_284_;
v___y_265_ = v___y_283_;
v___y_266_ = v___x_297_;
goto v___jp_259_;
}
}
else
{
lean_object* v___x_299_; 
lean_del_object(v___x_288_);
lean_dec(v_expectedType_x3f_226_);
v___x_299_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_260_ = v___y_276_;
v___y_261_ = v___y_280_;
v___y_262_ = v___y_281_;
v___y_263_ = v___y_282_;
v___y_264_ = v___y_284_;
v___y_265_ = v___y_283_;
v___y_266_ = v___x_299_;
goto v___jp_259_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
return v___y_278_;
}
}
v___jp_302_:
{
lean_object* v___x_309_; 
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v_a_258_);
v___x_309_ = lean_apply_6(v_evalExpr_225_, v_a_258_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, lean_box(0));
if (lean_obj_tag(v___x_309_) == 0)
{
lean_dec_ref(v___y_307_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
return v___x_309_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
v___x_311_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_312_ = l_Lean_Exception_isInterrupt(v_a_310_);
if (v___x_312_ == 0)
{
uint8_t v___x_313_; 
lean_inc(v_a_310_);
v___x_313_ = l_Lean_Exception_isRuntime(v_a_310_);
v___y_276_ = v___y_306_;
v___y_277_ = v___x_311_;
v___y_278_ = v___x_309_;
v___y_279_ = v_a_310_;
v___y_280_ = v___y_307_;
v___y_281_ = v___y_304_;
v___y_282_ = v___y_305_;
v___y_283_ = v___y_303_;
v___y_284_ = v___y_308_;
v___y_285_ = v___x_313_;
goto v___jp_275_;
}
else
{
v___y_276_ = v___y_306_;
v___y_277_ = v___x_311_;
v___y_278_ = v___x_309_;
v___y_279_ = v_a_310_;
v___y_280_ = v___y_307_;
v___y_281_ = v___y_304_;
v___y_282_ = v___y_305_;
v___y_283_ = v___y_303_;
v___y_284_ = v___y_308_;
v___y_285_ = v___x_312_;
goto v___jp_275_;
}
}
}
v___jp_314_:
{
lean_object* v___x_321_; 
lean_inc(v_a_258_);
v___x_321_ = l_Lean_Meta_getMVars(v_a_258_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_322_, v___x_231_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v_a_322_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; uint8_t v___x_325_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
v___x_325_ = lean_unbox(v_a_324_);
lean_dec(v_a_324_);
if (v___x_325_ == 0)
{
v___y_303_ = v___y_315_;
v___y_304_ = v___y_316_;
v___y_305_ = v___y_317_;
v___y_306_ = v___y_318_;
v___y_307_ = v___y_319_;
v___y_308_ = v___y_320_;
goto v___jp_302_;
}
else
{
lean_object* v___x_4071__overap_326_; lean_object* v___x_327_; 
v___x_4071__overap_326_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_224_);
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
v___x_327_ = lean_apply_7(v___x_4071__overap_326_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, lean_box(0));
if (lean_obj_tag(v___x_327_) == 0)
{
lean_dec_ref_known(v___x_327_, 1);
v___y_303_ = v___y_315_;
v___y_304_ = v___y_316_;
v___y_305_ = v___y_317_;
v___y_306_ = v___y_318_;
v___y_307_ = v___y_319_;
v___y_308_ = v___y_320_;
goto v___jp_302_;
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v___y_319_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref(v_evalExpr_225_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v___y_319_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref(v_evalExpr_225_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
v_a_336_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_323_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_323_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v___y_319_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref(v_evalExpr_225_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
v_a_344_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_321_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_321_);
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
v___jp_352_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_3938__overap_362_; lean_object* v___x_363_; 
v___x_359_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__32);
lean_inc(v_a_258_);
v___x_360_ = l_Lean_indentExpr(v_a_258_);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_inc_ref(v___x_223_);
lean_inc_ref(v___x_207_);
v___x_3938__overap_362_ = l_Lean_throwError___redArg(v___x_207_, v___x_223_, v___x_361_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
v___x_363_ = lean_apply_7(v___x_3938__overap_362_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
if (lean_obj_tag(v___x_363_) == 0)
{
lean_dec_ref_known(v___x_363_, 1);
v___y_315_ = v___y_353_;
v___y_316_ = v___y_354_;
v___y_317_ = v___y_355_;
v___y_318_ = v___y_356_;
v___y_319_ = v___y_357_;
v___y_320_ = v___y_358_;
goto v___jp_314_;
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v___y_357_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref(v_evalExpr_225_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
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
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref_known(v___x_253_, 14);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref(v_evalExpr_225_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
v_a_384_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_257_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_257_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref_known(v___x_253_, 14);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref(v_evalExpr_225_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref_known(v___x_220_, 2);
lean_dec_ref(v___x_207_);
v_a_392_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_254_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_254_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___boxed(lean_object* v_inst_413_, lean_object* v_stx_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_413_, v_stx_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab(lean_object* v_00_u03b1_423_, lean_object* v_inst_424_, lean_object* v_stx_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_424_, v_stx_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___boxed(lean_object* v_00_u03b1_434_, lean_object* v_inst_435_, lean_object* v_stx_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_ConfigEval_evalExprWithElab(v_00_u03b1_434_, v_inst_435_, v_stx_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_stx_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_evalTerm_455_; lean_object* v_fileName_456_; lean_object* v_fileMap_457_; lean_object* v_options_458_; lean_object* v_currRecDepth_459_; lean_object* v_maxRecDepth_460_; lean_object* v_ref_461_; lean_object* v_currNamespace_462_; lean_object* v_openDecls_463_; lean_object* v_initHeartbeats_464_; lean_object* v_maxHeartbeats_465_; lean_object* v_quotContext_466_; lean_object* v_currMacroScope_467_; uint8_t v_diag_468_; lean_object* v_cancelTk_x3f_469_; uint8_t v_suppressElabErrors_470_; lean_object* v_inheritedTraceOptions_471_; lean_object* v_ref_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_evalTerm_455_ = lean_ctor_get(v_inst_445_, 0);
lean_inc_ref(v_evalTerm_455_);
lean_dec_ref(v_inst_445_);
v_fileName_456_ = lean_ctor_get(v_a_452_, 0);
v_fileMap_457_ = lean_ctor_get(v_a_452_, 1);
v_options_458_ = lean_ctor_get(v_a_452_, 2);
v_currRecDepth_459_ = lean_ctor_get(v_a_452_, 3);
v_maxRecDepth_460_ = lean_ctor_get(v_a_452_, 4);
v_ref_461_ = lean_ctor_get(v_a_452_, 5);
v_currNamespace_462_ = lean_ctor_get(v_a_452_, 6);
v_openDecls_463_ = lean_ctor_get(v_a_452_, 7);
v_initHeartbeats_464_ = lean_ctor_get(v_a_452_, 8);
v_maxHeartbeats_465_ = lean_ctor_get(v_a_452_, 9);
v_quotContext_466_ = lean_ctor_get(v_a_452_, 10);
v_currMacroScope_467_ = lean_ctor_get(v_a_452_, 11);
v_diag_468_ = lean_ctor_get_uint8(v_a_452_, sizeof(void*)*14);
v_cancelTk_x3f_469_ = lean_ctor_get(v_a_452_, 12);
v_suppressElabErrors_470_ = lean_ctor_get_uint8(v_a_452_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_471_ = lean_ctor_get(v_a_452_, 13);
v_ref_472_ = l_Lean_replaceRef(v_stx_447_, v_ref_461_);
lean_inc_ref(v_inheritedTraceOptions_471_);
lean_inc(v_cancelTk_x3f_469_);
lean_inc(v_currMacroScope_467_);
lean_inc(v_quotContext_466_);
lean_inc(v_maxHeartbeats_465_);
lean_inc(v_initHeartbeats_464_);
lean_inc(v_openDecls_463_);
lean_inc(v_currNamespace_462_);
lean_inc(v_maxRecDepth_460_);
lean_inc(v_currRecDepth_459_);
lean_inc_ref(v_options_458_);
lean_inc_ref(v_fileMap_457_);
lean_inc_ref(v_fileName_456_);
v___x_473_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_473_, 0, v_fileName_456_);
lean_ctor_set(v___x_473_, 1, v_fileMap_457_);
lean_ctor_set(v___x_473_, 2, v_options_458_);
lean_ctor_set(v___x_473_, 3, v_currRecDepth_459_);
lean_ctor_set(v___x_473_, 4, v_maxRecDepth_460_);
lean_ctor_set(v___x_473_, 5, v_ref_472_);
lean_ctor_set(v___x_473_, 6, v_currNamespace_462_);
lean_ctor_set(v___x_473_, 7, v_openDecls_463_);
lean_ctor_set(v___x_473_, 8, v_initHeartbeats_464_);
lean_ctor_set(v___x_473_, 9, v_maxHeartbeats_465_);
lean_ctor_set(v___x_473_, 10, v_quotContext_466_);
lean_ctor_set(v___x_473_, 11, v_currMacroScope_467_);
lean_ctor_set(v___x_473_, 12, v_cancelTk_x3f_469_);
lean_ctor_set(v___x_473_, 13, v_inheritedTraceOptions_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*14, v_diag_468_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*14 + 1, v_suppressElabErrors_470_);
lean_inc(v_a_453_);
lean_inc_ref(v___x_473_);
lean_inc(v_a_451_);
lean_inc_ref(v_a_450_);
lean_inc(v_a_449_);
lean_inc_ref(v_a_448_);
lean_inc(v_stx_447_);
v___x_474_ = lean_apply_8(v_evalTerm_455_, v_stx_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v___x_473_, v_a_453_, lean_box(0));
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref_known(v___x_473_, 14);
lean_dec(v_stx_447_);
lean_dec_ref(v_inst_446_);
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_483_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_fst_479_; lean_object* v___x_481_; 
v_fst_479_ = lean_ctor_get(v_a_475_, 0);
lean_inc(v_fst_479_);
lean_dec(v_a_475_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v_fst_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fst_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_499_; 
v_a_484_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_499_ == 0)
{
v___x_486_ = v___x_474_;
v_isShared_487_ = v_isSharedCheck_499_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_474_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_499_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_484_);
if (v_isShared_487_ == 0)
{
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_484_);
v___x_490_ = v_reuseFailAlloc_498_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
uint8_t v___y_492_; uint8_t v___x_496_; 
v___x_496_ = l_Lean_Exception_isInterrupt(v_a_484_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
lean_inc(v_a_484_);
v___x_497_ = l_Lean_Exception_isRuntime(v_a_484_);
v___y_492_ = v___x_497_;
goto v___jp_491_;
}
else
{
v___y_492_ = v___x_496_;
goto v___jp_491_;
}
v___jp_491_:
{
if (v___y_492_ == 0)
{
if (lean_obj_tag(v_a_484_) == 0)
{
lean_dec_ref_known(v_a_484_, 2);
lean_dec_ref_known(v___x_473_, 14);
lean_dec(v_stx_447_);
lean_dec_ref(v_inst_446_);
return v___x_490_;
}
else
{
lean_object* v_id_493_; uint8_t v___x_494_; 
v_id_493_ = lean_ctor_get(v_a_484_, 0);
lean_inc(v_id_493_);
lean_dec_ref_known(v_a_484_, 2);
v___x_494_ = l_Lean_instBEqInternalExceptionId_beq(v___x_488_, v_id_493_);
lean_dec(v_id_493_);
if (v___x_494_ == 0)
{
lean_dec_ref_known(v___x_473_, 14);
lean_dec(v_stx_447_);
lean_dec_ref(v_inst_446_);
return v___x_490_;
}
else
{
lean_object* v___x_495_; 
lean_dec_ref(v___x_490_);
v___x_495_ = l_Lean_Elab_ConfigEval_evalExprWithElab___redArg(v_inst_446_, v_stx_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v___x_473_, v_a_453_);
lean_dec_ref_known(v___x_473_, 14);
return v___x_495_;
}
}
}
else
{
lean_dec(v_a_484_);
lean_dec_ref_known(v___x_473_, 14);
lean_dec(v_stx_447_);
lean_dec_ref(v_inst_446_);
return v___x_490_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg___boxed(lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_stx_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_500_, v_inst_501_, v_stx_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(lean_object* v_00_u03b1_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_stx_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_512_, v_inst_513_, v_stx_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___boxed(lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_stx_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab(v_00_u03b1_523_, v_inst_524_, v_inst_525_, v_stx_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__4));
lean_inc(v_x_553_);
v___x_555_ = l_Lean_Syntax_isOfKind(v_x_553_, v___x_554_);
if (v___x_555_ == 0)
{
return v_x_553_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Lean_Syntax_getArg(v_x_553_, v___x_556_);
v___x_558_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__6));
lean_inc(v___x_557_);
v___x_559_ = l_Lean_Syntax_isOfKind(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_dec(v___x_557_);
return v_x_553_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = l_Lean_Syntax_getArg(v___x_557_, v___x_560_);
lean_dec(v___x_557_);
v___x_562_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens___closed__8));
lean_inc(v___x_561_);
v___x_563_ = l_Lean_Syntax_isOfKind(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec(v___x_561_);
return v_x_553_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = l_Lean_Syntax_getArg(v___x_561_, v___x_556_);
lean_dec(v___x_561_);
v___x_565_ = lean_box(0);
v___x_566_ = l_Lean_Syntax_matchesIdent(v___x_564_, v___x_565_);
lean_dec(v___x_564_);
if (v___x_566_ == 0)
{
return v_x_553_;
}
else
{
lean_object* v_t_567_; 
v_t_567_ = l_Lean_Syntax_getArg(v_x_553_, v___x_560_);
lean_dec(v_x_553_);
v_x_553_ = v_t_567_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(lean_object* v_expectedType_x3f_569_, lean_object* v_f_570_, lean_object* v_stx_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_fileName_579_; lean_object* v_fileMap_580_; lean_object* v_options_581_; lean_object* v_currRecDepth_582_; lean_object* v_maxRecDepth_583_; lean_object* v_ref_584_; lean_object* v_currNamespace_585_; lean_object* v_openDecls_586_; lean_object* v_initHeartbeats_587_; lean_object* v_maxHeartbeats_588_; lean_object* v_quotContext_589_; lean_object* v_currMacroScope_590_; uint8_t v_diag_591_; lean_object* v_cancelTk_x3f_592_; uint8_t v_suppressElabErrors_593_; lean_object* v_inheritedTraceOptions_594_; lean_object* v___x_595_; lean_object* v_ref_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_fileName_579_ = lean_ctor_get(v_a_576_, 0);
v_fileMap_580_ = lean_ctor_get(v_a_576_, 1);
v_options_581_ = lean_ctor_get(v_a_576_, 2);
v_currRecDepth_582_ = lean_ctor_get(v_a_576_, 3);
v_maxRecDepth_583_ = lean_ctor_get(v_a_576_, 4);
v_ref_584_ = lean_ctor_get(v_a_576_, 5);
v_currNamespace_585_ = lean_ctor_get(v_a_576_, 6);
v_openDecls_586_ = lean_ctor_get(v_a_576_, 7);
v_initHeartbeats_587_ = lean_ctor_get(v_a_576_, 8);
v_maxHeartbeats_588_ = lean_ctor_get(v_a_576_, 9);
v_quotContext_589_ = lean_ctor_get(v_a_576_, 10);
v_currMacroScope_590_ = lean_ctor_get(v_a_576_, 11);
v_diag_591_ = lean_ctor_get_uint8(v_a_576_, sizeof(void*)*14);
v_cancelTk_x3f_592_ = lean_ctor_get(v_a_576_, 12);
v_suppressElabErrors_593_ = lean_ctor_get_uint8(v_a_576_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_594_ = lean_ctor_get(v_a_576_, 13);
lean_inc(v_stx_571_);
v___x_595_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_571_);
v_ref_596_ = l_Lean_replaceRef(v_stx_571_, v_ref_584_);
lean_inc_ref(v_inheritedTraceOptions_594_);
lean_inc(v_cancelTk_x3f_592_);
lean_inc(v_currMacroScope_590_);
lean_inc(v_quotContext_589_);
lean_inc(v_maxHeartbeats_588_);
lean_inc(v_initHeartbeats_587_);
lean_inc(v_openDecls_586_);
lean_inc(v_currNamespace_585_);
lean_inc(v_maxRecDepth_583_);
lean_inc(v_currRecDepth_582_);
lean_inc_ref(v_options_581_);
lean_inc_ref(v_fileMap_580_);
lean_inc_ref(v_fileName_579_);
v___x_597_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_597_, 0, v_fileName_579_);
lean_ctor_set(v___x_597_, 1, v_fileMap_580_);
lean_ctor_set(v___x_597_, 2, v_options_581_);
lean_ctor_set(v___x_597_, 3, v_currRecDepth_582_);
lean_ctor_set(v___x_597_, 4, v_maxRecDepth_583_);
lean_ctor_set(v___x_597_, 5, v_ref_596_);
lean_ctor_set(v___x_597_, 6, v_currNamespace_585_);
lean_ctor_set(v___x_597_, 7, v_openDecls_586_);
lean_ctor_set(v___x_597_, 8, v_initHeartbeats_587_);
lean_ctor_set(v___x_597_, 9, v_maxHeartbeats_588_);
lean_ctor_set(v___x_597_, 10, v_quotContext_589_);
lean_ctor_set(v___x_597_, 11, v_currMacroScope_590_);
lean_ctor_set(v___x_597_, 12, v_cancelTk_x3f_592_);
lean_ctor_set(v___x_597_, 13, v_inheritedTraceOptions_594_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*14, v_diag_591_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*14 + 1, v_suppressElabErrors_593_);
lean_inc(v_a_577_);
lean_inc(v_a_575_);
lean_inc_ref(v_a_574_);
lean_inc(v_a_573_);
lean_inc_ref(v_a_572_);
v___x_598_ = lean_apply_8(v_f_570_, v___x_595_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v___x_597_, v_a_577_, lean_box(0));
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_630_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_630_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_630_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_630_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_snd_603_; lean_object* v___x_604_; lean_object* v_infoState_605_; uint8_t v_enabled_606_; 
v_snd_603_ = lean_ctor_get(v_a_599_, 1);
v___x_604_ = lean_st_ref_get(v_a_577_);
v_infoState_605_ = lean_ctor_get(v___x_604_, 7);
lean_inc_ref(v_infoState_605_);
lean_dec(v___x_604_);
v_enabled_606_ = lean_ctor_get_uint8(v_infoState_605_, sizeof(void*)*3);
lean_dec_ref(v_infoState_605_);
if (v_enabled_606_ == 0)
{
lean_object* v___x_608_; 
lean_dec(v_stx_571_);
lean_dec(v_expectedType_x3f_569_);
if (v_isShared_602_ == 0)
{
v___x_608_ = v___x_601_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_599_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; 
lean_del_object(v___x_601_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_box(0);
v___x_612_ = 0;
lean_inc(v_snd_603_);
v___x_613_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_571_, v_snd_603_, v_expectedType_x3f_569_, v___x_610_, v___x_611_, v___x_612_, v___x_612_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_613_, 0);
lean_dec(v_unused_621_);
v___x_615_ = v___x_613_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_dec(v___x_613_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_a_599_);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_599_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_a_599_);
v_a_622_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_613_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_613_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_571_);
lean_dec(v_expectedType_x3f_569_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg___boxed(lean_object* v_expectedType_x3f_631_, lean_object* v_f_632_, lean_object* v_stx_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___redArg(v_expectedType_x3f_631_, v_f_632_, v_stx_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(lean_object* v_00_u03b1_642_, lean_object* v_expectedType_x3f_643_, lean_object* v_f_644_, lean_object* v_stx_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_fileName_653_; lean_object* v_fileMap_654_; lean_object* v_options_655_; lean_object* v_currRecDepth_656_; lean_object* v_maxRecDepth_657_; lean_object* v_ref_658_; lean_object* v_currNamespace_659_; lean_object* v_openDecls_660_; lean_object* v_initHeartbeats_661_; lean_object* v_maxHeartbeats_662_; lean_object* v_quotContext_663_; lean_object* v_currMacroScope_664_; uint8_t v_diag_665_; lean_object* v_cancelTk_x3f_666_; uint8_t v_suppressElabErrors_667_; lean_object* v_inheritedTraceOptions_668_; lean_object* v___x_669_; lean_object* v_ref_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_fileName_653_ = lean_ctor_get(v_a_650_, 0);
v_fileMap_654_ = lean_ctor_get(v_a_650_, 1);
v_options_655_ = lean_ctor_get(v_a_650_, 2);
v_currRecDepth_656_ = lean_ctor_get(v_a_650_, 3);
v_maxRecDepth_657_ = lean_ctor_get(v_a_650_, 4);
v_ref_658_ = lean_ctor_get(v_a_650_, 5);
v_currNamespace_659_ = lean_ctor_get(v_a_650_, 6);
v_openDecls_660_ = lean_ctor_get(v_a_650_, 7);
v_initHeartbeats_661_ = lean_ctor_get(v_a_650_, 8);
v_maxHeartbeats_662_ = lean_ctor_get(v_a_650_, 9);
v_quotContext_663_ = lean_ctor_get(v_a_650_, 10);
v_currMacroScope_664_ = lean_ctor_get(v_a_650_, 11);
v_diag_665_ = lean_ctor_get_uint8(v_a_650_, sizeof(void*)*14);
v_cancelTk_x3f_666_ = lean_ctor_get(v_a_650_, 12);
v_suppressElabErrors_667_ = lean_ctor_get_uint8(v_a_650_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_668_ = lean_ctor_get(v_a_650_, 13);
lean_inc(v_stx_645_);
v___x_669_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_645_);
v_ref_670_ = l_Lean_replaceRef(v_stx_645_, v_ref_658_);
lean_inc_ref(v_inheritedTraceOptions_668_);
lean_inc(v_cancelTk_x3f_666_);
lean_inc(v_currMacroScope_664_);
lean_inc(v_quotContext_663_);
lean_inc(v_maxHeartbeats_662_);
lean_inc(v_initHeartbeats_661_);
lean_inc(v_openDecls_660_);
lean_inc(v_currNamespace_659_);
lean_inc(v_maxRecDepth_657_);
lean_inc(v_currRecDepth_656_);
lean_inc_ref(v_options_655_);
lean_inc_ref(v_fileMap_654_);
lean_inc_ref(v_fileName_653_);
v___x_671_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_671_, 0, v_fileName_653_);
lean_ctor_set(v___x_671_, 1, v_fileMap_654_);
lean_ctor_set(v___x_671_, 2, v_options_655_);
lean_ctor_set(v___x_671_, 3, v_currRecDepth_656_);
lean_ctor_set(v___x_671_, 4, v_maxRecDepth_657_);
lean_ctor_set(v___x_671_, 5, v_ref_670_);
lean_ctor_set(v___x_671_, 6, v_currNamespace_659_);
lean_ctor_set(v___x_671_, 7, v_openDecls_660_);
lean_ctor_set(v___x_671_, 8, v_initHeartbeats_661_);
lean_ctor_set(v___x_671_, 9, v_maxHeartbeats_662_);
lean_ctor_set(v___x_671_, 10, v_quotContext_663_);
lean_ctor_set(v___x_671_, 11, v_currMacroScope_664_);
lean_ctor_set(v___x_671_, 12, v_cancelTk_x3f_666_);
lean_ctor_set(v___x_671_, 13, v_inheritedTraceOptions_668_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*14, v_diag_665_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*14 + 1, v_suppressElabErrors_667_);
lean_inc(v_a_651_);
lean_inc(v_a_649_);
lean_inc_ref(v_a_648_);
lean_inc(v_a_647_);
lean_inc_ref(v_a_646_);
v___x_672_ = lean_apply_8(v_f_644_, v___x_669_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v___x_671_, v_a_651_, lean_box(0));
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_704_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_704_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_704_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_704_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_snd_677_; lean_object* v___x_678_; lean_object* v_infoState_679_; uint8_t v_enabled_680_; 
v_snd_677_ = lean_ctor_get(v_a_673_, 1);
v___x_678_ = lean_st_ref_get(v_a_651_);
v_infoState_679_ = lean_ctor_get(v___x_678_, 7);
lean_inc_ref(v_infoState_679_);
lean_dec(v___x_678_);
v_enabled_680_ = lean_ctor_get_uint8(v_infoState_679_, sizeof(void*)*3);
lean_dec_ref(v_infoState_679_);
if (v_enabled_680_ == 0)
{
lean_object* v___x_682_; 
lean_dec(v_stx_645_);
lean_dec(v_expectedType_x3f_643_);
if (v_isShared_676_ == 0)
{
v___x_682_ = v___x_675_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_673_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; 
lean_del_object(v___x_675_);
v___x_684_ = lean_box(0);
v___x_685_ = lean_box(0);
v___x_686_ = 0;
lean_inc(v_snd_677_);
v___x_687_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_645_, v_snd_677_, v_expectedType_x3f_643_, v___x_684_, v___x_685_, v___x_686_, v___x_686_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_695_);
v___x_689_ = v___x_687_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_dec(v___x_687_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v_a_673_);
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_673_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_a_673_);
v_a_696_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_687_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_645_);
lean_dec(v_expectedType_x3f_643_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo___boxed(lean_object* v_00_u03b1_705_, lean_object* v_expectedType_x3f_706_, lean_object* v_f_707_, lean_object* v_stx_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo(v_00_u03b1_705_, v_expectedType_x3f_706_, v_f_707_, v_stx_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(lean_object* v_inst_717_, lean_object* v_f_718_, lean_object* v_stx_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_toExpr_727_; lean_object* v_toTypeExpr_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_796_; 
v_toExpr_727_ = lean_ctor_get(v_inst_717_, 0);
v_toTypeExpr_728_ = lean_ctor_get(v_inst_717_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_inst_717_);
if (v_isSharedCheck_796_ == 0)
{
v___x_730_ = v_inst_717_;
v_isShared_731_ = v_isSharedCheck_796_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_toTypeExpr_728_);
lean_inc(v_toExpr_727_);
lean_dec(v_inst_717_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_796_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_fileName_732_; lean_object* v_fileMap_733_; lean_object* v_options_734_; lean_object* v_currRecDepth_735_; lean_object* v_maxRecDepth_736_; lean_object* v_ref_737_; lean_object* v_currNamespace_738_; lean_object* v_openDecls_739_; lean_object* v_initHeartbeats_740_; lean_object* v_maxHeartbeats_741_; lean_object* v_quotContext_742_; lean_object* v_currMacroScope_743_; uint8_t v_diag_744_; lean_object* v_cancelTk_x3f_745_; uint8_t v_suppressElabErrors_746_; lean_object* v_inheritedTraceOptions_747_; lean_object* v___x_748_; lean_object* v_ref_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_fileName_732_ = lean_ctor_get(v_a_724_, 0);
v_fileMap_733_ = lean_ctor_get(v_a_724_, 1);
v_options_734_ = lean_ctor_get(v_a_724_, 2);
v_currRecDepth_735_ = lean_ctor_get(v_a_724_, 3);
v_maxRecDepth_736_ = lean_ctor_get(v_a_724_, 4);
v_ref_737_ = lean_ctor_get(v_a_724_, 5);
v_currNamespace_738_ = lean_ctor_get(v_a_724_, 6);
v_openDecls_739_ = lean_ctor_get(v_a_724_, 7);
v_initHeartbeats_740_ = lean_ctor_get(v_a_724_, 8);
v_maxHeartbeats_741_ = lean_ctor_get(v_a_724_, 9);
v_quotContext_742_ = lean_ctor_get(v_a_724_, 10);
v_currMacroScope_743_ = lean_ctor_get(v_a_724_, 11);
v_diag_744_ = lean_ctor_get_uint8(v_a_724_, sizeof(void*)*14);
v_cancelTk_x3f_745_ = lean_ctor_get(v_a_724_, 12);
v_suppressElabErrors_746_ = lean_ctor_get_uint8(v_a_724_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_747_ = lean_ctor_get(v_a_724_, 13);
lean_inc(v_stx_719_);
v___x_748_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_719_);
v_ref_749_ = l_Lean_replaceRef(v_stx_719_, v_ref_737_);
lean_inc_ref(v_inheritedTraceOptions_747_);
lean_inc(v_cancelTk_x3f_745_);
lean_inc(v_currMacroScope_743_);
lean_inc(v_quotContext_742_);
lean_inc(v_maxHeartbeats_741_);
lean_inc(v_initHeartbeats_740_);
lean_inc(v_openDecls_739_);
lean_inc(v_currNamespace_738_);
lean_inc(v_maxRecDepth_736_);
lean_inc(v_currRecDepth_735_);
lean_inc_ref(v_options_734_);
lean_inc_ref(v_fileMap_733_);
lean_inc_ref(v_fileName_732_);
v___x_750_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_750_, 0, v_fileName_732_);
lean_ctor_set(v___x_750_, 1, v_fileMap_733_);
lean_ctor_set(v___x_750_, 2, v_options_734_);
lean_ctor_set(v___x_750_, 3, v_currRecDepth_735_);
lean_ctor_set(v___x_750_, 4, v_maxRecDepth_736_);
lean_ctor_set(v___x_750_, 5, v_ref_749_);
lean_ctor_set(v___x_750_, 6, v_currNamespace_738_);
lean_ctor_set(v___x_750_, 7, v_openDecls_739_);
lean_ctor_set(v___x_750_, 8, v_initHeartbeats_740_);
lean_ctor_set(v___x_750_, 9, v_maxHeartbeats_741_);
lean_ctor_set(v___x_750_, 10, v_quotContext_742_);
lean_ctor_set(v___x_750_, 11, v_currMacroScope_743_);
lean_ctor_set(v___x_750_, 12, v_cancelTk_x3f_745_);
lean_ctor_set(v___x_750_, 13, v_inheritedTraceOptions_747_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*14, v_diag_744_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*14 + 1, v_suppressElabErrors_746_);
lean_inc(v_a_725_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
v___x_751_ = lean_apply_8(v_f_718_, v___x_748_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v___x_750_, v_a_725_, lean_box(0));
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_787_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_787_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_787_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_787_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v_infoState_757_; uint8_t v_enabled_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_756_ = lean_st_ref_get(v_a_725_);
v_infoState_757_ = lean_ctor_get(v___x_756_, 7);
lean_inc_ref(v_infoState_757_);
lean_dec(v___x_756_);
v_enabled_758_ = lean_ctor_get_uint8(v_infoState_757_, sizeof(void*)*3);
lean_dec_ref(v_infoState_757_);
lean_inc(v_a_752_);
v___x_759_ = lean_apply_1(v_toExpr_727_, v_a_752_);
lean_inc_ref(v___x_759_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_759_);
lean_ctor_set(v___x_730_, 0, v_a_752_);
v___x_761_ = v___x_730_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_752_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_786_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
if (v_enabled_758_ == 0)
{
lean_object* v___x_763_; 
lean_dec_ref(v___x_759_);
lean_dec_ref(v_toTypeExpr_728_);
lean_dec(v_stx_719_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_761_);
v___x_763_ = v___x_754_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; 
lean_del_object(v___x_754_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v_toTypeExpr_728_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_box(0);
v___x_768_ = 0;
v___x_769_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_719_, v___x_759_, v___x_765_, v___x_766_, v___x_767_, v___x_768_, v___x_768_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v___x_769_, 0);
lean_dec(v_unused_777_);
v___x_771_ = v___x_769_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_dec(v___x_769_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_761_);
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_761_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___x_761_);
v_a_778_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_769_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_769_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_730_);
lean_dec_ref(v_toTypeExpr_728_);
lean_dec_ref(v_toExpr_727_);
lean_dec(v_stx_719_);
v_a_788_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_751_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_751_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg___boxed(lean_object* v_inst_797_, lean_object* v_f_798_, lean_object* v_stx_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___redArg(v_inst_797_, v_f_798_, v_stx_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(lean_object* v_00_u03b1_808_, lean_object* v_inst_809_, lean_object* v_f_810_, lean_object* v_stx_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_toExpr_819_; lean_object* v_toTypeExpr_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_888_; 
v_toExpr_819_ = lean_ctor_get(v_inst_809_, 0);
v_toTypeExpr_820_ = lean_ctor_get(v_inst_809_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_inst_809_);
if (v_isSharedCheck_888_ == 0)
{
v___x_822_ = v_inst_809_;
v_isShared_823_ = v_isSharedCheck_888_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_toTypeExpr_820_);
lean_inc(v_toExpr_819_);
lean_dec(v_inst_809_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_888_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_fileName_824_; lean_object* v_fileMap_825_; lean_object* v_options_826_; lean_object* v_currRecDepth_827_; lean_object* v_maxRecDepth_828_; lean_object* v_ref_829_; lean_object* v_currNamespace_830_; lean_object* v_openDecls_831_; lean_object* v_initHeartbeats_832_; lean_object* v_maxHeartbeats_833_; lean_object* v_quotContext_834_; lean_object* v_currMacroScope_835_; uint8_t v_diag_836_; lean_object* v_cancelTk_x3f_837_; uint8_t v_suppressElabErrors_838_; lean_object* v_inheritedTraceOptions_839_; lean_object* v___x_840_; lean_object* v_ref_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_fileName_824_ = lean_ctor_get(v_a_816_, 0);
v_fileMap_825_ = lean_ctor_get(v_a_816_, 1);
v_options_826_ = lean_ctor_get(v_a_816_, 2);
v_currRecDepth_827_ = lean_ctor_get(v_a_816_, 3);
v_maxRecDepth_828_ = lean_ctor_get(v_a_816_, 4);
v_ref_829_ = lean_ctor_get(v_a_816_, 5);
v_currNamespace_830_ = lean_ctor_get(v_a_816_, 6);
v_openDecls_831_ = lean_ctor_get(v_a_816_, 7);
v_initHeartbeats_832_ = lean_ctor_get(v_a_816_, 8);
v_maxHeartbeats_833_ = lean_ctor_get(v_a_816_, 9);
v_quotContext_834_ = lean_ctor_get(v_a_816_, 10);
v_currMacroScope_835_ = lean_ctor_get(v_a_816_, 11);
v_diag_836_ = lean_ctor_get_uint8(v_a_816_, sizeof(void*)*14);
v_cancelTk_x3f_837_ = lean_ctor_get(v_a_816_, 12);
v_suppressElabErrors_838_ = lean_ctor_get_uint8(v_a_816_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_839_ = lean_ctor_get(v_a_816_, 13);
lean_inc(v_stx_811_);
v___x_840_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_811_);
v_ref_841_ = l_Lean_replaceRef(v_stx_811_, v_ref_829_);
lean_inc_ref(v_inheritedTraceOptions_839_);
lean_inc(v_cancelTk_x3f_837_);
lean_inc(v_currMacroScope_835_);
lean_inc(v_quotContext_834_);
lean_inc(v_maxHeartbeats_833_);
lean_inc(v_initHeartbeats_832_);
lean_inc(v_openDecls_831_);
lean_inc(v_currNamespace_830_);
lean_inc(v_maxRecDepth_828_);
lean_inc(v_currRecDepth_827_);
lean_inc_ref(v_options_826_);
lean_inc_ref(v_fileMap_825_);
lean_inc_ref(v_fileName_824_);
v___x_842_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_842_, 0, v_fileName_824_);
lean_ctor_set(v___x_842_, 1, v_fileMap_825_);
lean_ctor_set(v___x_842_, 2, v_options_826_);
lean_ctor_set(v___x_842_, 3, v_currRecDepth_827_);
lean_ctor_set(v___x_842_, 4, v_maxRecDepth_828_);
lean_ctor_set(v___x_842_, 5, v_ref_841_);
lean_ctor_set(v___x_842_, 6, v_currNamespace_830_);
lean_ctor_set(v___x_842_, 7, v_openDecls_831_);
lean_ctor_set(v___x_842_, 8, v_initHeartbeats_832_);
lean_ctor_set(v___x_842_, 9, v_maxHeartbeats_833_);
lean_ctor_set(v___x_842_, 10, v_quotContext_834_);
lean_ctor_set(v___x_842_, 11, v_currMacroScope_835_);
lean_ctor_set(v___x_842_, 12, v_cancelTk_x3f_837_);
lean_ctor_set(v___x_842_, 13, v_inheritedTraceOptions_839_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*14, v_diag_836_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*14 + 1, v_suppressElabErrors_838_);
lean_inc(v_a_817_);
lean_inc(v_a_815_);
lean_inc_ref(v_a_814_);
lean_inc(v_a_813_);
lean_inc_ref(v_a_812_);
v___x_843_ = lean_apply_8(v_f_810_, v___x_840_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v___x_842_, v_a_817_, lean_box(0));
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_879_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_879_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_879_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_879_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v_infoState_849_; uint8_t v_enabled_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_848_ = lean_st_ref_get(v_a_817_);
v_infoState_849_ = lean_ctor_get(v___x_848_, 7);
lean_inc_ref(v_infoState_849_);
lean_dec(v___x_848_);
v_enabled_850_ = lean_ctor_get_uint8(v_infoState_849_, sizeof(void*)*3);
lean_dec_ref(v_infoState_849_);
lean_inc(v_a_844_);
v___x_851_ = lean_apply_1(v_toExpr_819_, v_a_844_);
lean_inc_ref(v___x_851_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_851_);
lean_ctor_set(v___x_822_, 0, v_a_844_);
v___x_853_ = v___x_822_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_844_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_851_);
v___x_853_ = v_reuseFailAlloc_878_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
if (v_enabled_850_ == 0)
{
lean_object* v___x_855_; 
lean_dec_ref(v___x_851_);
lean_dec_ref(v_toTypeExpr_820_);
lean_dec(v_stx_811_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_853_);
v___x_855_ = v___x_846_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; 
lean_del_object(v___x_846_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_toTypeExpr_820_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_box(0);
v___x_860_ = 0;
v___x_861_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_811_, v___x_851_, v___x_857_, v___x_858_, v___x_859_, v___x_860_, v___x_860_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v___x_861_, 0);
lean_dec(v_unused_869_);
v___x_863_ = v___x_861_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_dec(v___x_861_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_853_);
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_853_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v___x_853_);
v_a_870_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_861_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_861_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_del_object(v___x_822_);
lean_dec_ref(v_toTypeExpr_820_);
lean_dec_ref(v_toExpr_819_);
lean_dec(v_stx_811_);
v_a_880_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_843_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_843_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27___boxed(lean_object* v_00_u03b1_889_, lean_object* v_inst_890_, lean_object* v_f_891_, lean_object* v_stx_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Elab_ConfigEval_EvalTerm_evalTermWithInfo_x27(v_00_u03b1_889_, v_inst_890_, v_f_891_, v_stx_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(lean_object* v_msgData_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; lean_object* v_env_908_; lean_object* v___x_909_; lean_object* v_mctx_910_; lean_object* v_lctx_911_; lean_object* v_options_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_907_ = lean_st_ref_get(v___y_905_);
v_env_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_env_908_);
lean_dec(v___x_907_);
v___x_909_ = lean_st_ref_get(v___y_903_);
v_mctx_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_ref(v_mctx_910_);
lean_dec(v___x_909_);
v_lctx_911_ = lean_ctor_get(v___y_902_, 2);
v_options_912_ = lean_ctor_get(v___y_904_, 2);
lean_inc_ref(v_options_912_);
lean_inc_ref(v_lctx_911_);
v___x_913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_913_, 0, v_env_908_);
lean_ctor_set(v___x_913_, 1, v_mctx_910_);
lean_ctor_set(v___x_913_, 2, v_lctx_911_);
lean_ctor_set(v___x_913_, 3, v_options_912_);
v___x_914_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_msgData_901_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0___boxed(lean_object* v_msgData_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msgData_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(lean_object* v_msg_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_ref_929_; lean_object* v___x_930_; lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_ref_929_ = lean_ctor_get(v___y_926_, 5);
v___x_930_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_inc(v_ref_929_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_ref_929_);
lean_ctor_set(v___x_935_, 1, v_a_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg___boxed(lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__0));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(lean_object* v_f_950_, lean_object* v_e_951_, lean_object* v_errMsg_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
lean_inc_ref(v_f_950_);
lean_inc(v_a_956_);
lean_inc_ref(v_a_955_);
lean_inc(v_a_954_);
lean_inc_ref(v_a_953_);
lean_inc_ref(v_e_951_);
v___x_958_ = lean_apply_6(v_f_950_, v_e_951_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, lean_box(0));
if (lean_obj_tag(v___x_958_) == 0)
{
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
lean_dec_ref(v_f_950_);
return v___x_958_;
}
else
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___y_962_; lean_object* v___y_963_; uint8_t v___y_964_; lean_object* v___y_980_; lean_object* v_a_981_; uint8_t v___y_985_; uint8_t v___x_1000_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
v___x_960_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_1000_ = l_Lean_Exception_isInterrupt(v_a_959_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
lean_inc(v_a_959_);
v___x_1001_ = l_Lean_Exception_isRuntime(v_a_959_);
v___y_985_ = v___x_1001_;
goto v___jp_984_;
}
else
{
v___y_985_ = v___x_1000_;
goto v___jp_984_;
}
v___jp_961_:
{
if (v___y_964_ == 0)
{
if (lean_obj_tag(v___y_962_) == 0)
{
lean_dec_ref_known(v___y_962_, 2);
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
return v___y_963_;
}
else
{
lean_object* v_id_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_977_; 
v_id_965_ = lean_ctor_get(v___y_962_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___y_962_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___y_962_, 1);
lean_dec(v_unused_978_);
v___x_967_ = v___y_962_;
v_isShared_968_ = v_isSharedCheck_977_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_id_965_);
lean_dec(v___y_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_977_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint8_t v___x_969_; 
v___x_969_ = l_Lean_instBEqInternalExceptionId_beq(v___x_960_, v_id_965_);
lean_dec(v_id_965_);
if (v___x_969_ == 0)
{
lean_del_object(v___x_967_);
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
return v___y_963_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec_ref(v___y_963_);
v___x_970_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___closed__1);
v___x_971_ = l_Lean_indentExpr(v_e_951_);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 7);
lean_ctor_set(v___x_967_, 1, v___x_971_);
lean_ctor_set(v___x_967_, 0, v___x_970_);
v___x_973_ = v___x_967_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_976_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v_errMsg_952_);
v___x_975_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v___x_974_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_975_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_962_);
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
return v___y_963_;
}
}
v___jp_979_:
{
uint8_t v___x_982_; 
v___x_982_ = l_Lean_Exception_isInterrupt(v_a_981_);
if (v___x_982_ == 0)
{
uint8_t v___x_983_; 
lean_inc_ref(v_a_981_);
v___x_983_ = l_Lean_Exception_isRuntime(v_a_981_);
v___y_962_ = v_a_981_;
v___y_963_ = v___y_980_;
v___y_964_ = v___x_983_;
goto v___jp_961_;
}
else
{
v___y_962_ = v_a_981_;
v___y_963_ = v___y_980_;
v___y_964_ = v___x_982_;
goto v___jp_961_;
}
}
v___jp_984_:
{
if (v___y_985_ == 0)
{
if (lean_obj_tag(v_a_959_) == 0)
{
lean_dec_ref_known(v_a_959_, 2);
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
lean_dec_ref(v_f_950_);
return v___x_958_;
}
else
{
lean_object* v_id_986_; uint8_t v___x_987_; 
v_id_986_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_id_986_);
lean_dec_ref_known(v_a_959_, 2);
v___x_987_ = l_Lean_instBEqInternalExceptionId_beq(v___x_960_, v_id_986_);
lean_dec(v_id_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
lean_dec_ref(v_f_950_);
return v___x_958_;
}
else
{
lean_object* v___x_988_; 
lean_dec_ref_known(v___x_958_, 1);
lean_inc(v_a_956_);
lean_inc_ref(v_a_955_);
lean_inc(v_a_954_);
lean_inc_ref(v_a_953_);
lean_inc_ref(v_e_951_);
v___x_988_ = lean_whnf(v_e_951_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
lean_inc(v_a_956_);
lean_inc_ref(v_a_955_);
lean_inc(v_a_954_);
lean_inc_ref(v_a_953_);
v___x_990_ = lean_apply_6(v_f_950_, v_a_989_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, lean_box(0));
if (lean_obj_tag(v___x_990_) == 0)
{
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
return v___x_990_;
}
else
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
v___y_980_ = v___x_990_;
v_a_981_ = v_a_991_;
goto v___jp_979_;
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v_f_950_);
v_a_992_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_988_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_988_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
lean_inc(v_a_992_);
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v___y_980_ = v___x_997_;
v_a_981_ = v_a_992_;
goto v___jp_979_;
}
}
}
}
}
}
else
{
lean_dec(v_a_959_);
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
lean_dec_ref(v_f_950_);
return v___x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg___boxed(lean_object* v_f_1002_, lean_object* v_e_1003_, lean_object* v_errMsg_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_1002_, v_e_1003_, v_errMsg_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(lean_object* v_00_u03b1_1011_, lean_object* v_f_1012_, lean_object* v_e_1013_, lean_object* v_errMsg_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v_f_1012_, v_e_1013_, v_errMsg_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_f_1022_, lean_object* v_e_1023_, lean_object* v_errMsg_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF(v_00_u03b1_1021_, v_f_1022_, v_e_1023_, v_errMsg_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(lean_object* v_00_u03b1_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___redArg(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0(v_00_u03b1_1039_, v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object* v_item_1047_){
_start:
{
lean_object* v_optionComps_1048_; uint8_t v___x_1049_; 
v_optionComps_1048_ = lean_ctor_get(v_item_1047_, 5);
v___x_1049_ = l_List_isEmpty___redArg(v_optionComps_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous___boxed(lean_object* v_item_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1050_);
lean_dec_ref(v_item_1050_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root(lean_object* v_item_1053_){
_start:
{
lean_object* v_optionComps_1054_; 
v_optionComps_1054_ = lean_ctor_get(v_item_1053_, 5);
if (lean_obj_tag(v_optionComps_1054_) == 1)
{
lean_object* v_head_1055_; 
v_head_1055_ = lean_ctor_get(v_optionComps_1054_, 0);
lean_inc(v_head_1055_);
return v_head_1055_;
}
else
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_box(0);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_root___boxed(lean_object* v_item_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1057_);
lean_dec_ref(v_item_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object* v_item_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1059_);
v___x_1061_ = l_Lean_Syntax_getId(v___x_1060_);
lean_dec(v___x_1060_);
if (lean_obj_tag(v___x_1061_) == 1)
{
lean_object* v_str_1062_; 
v_str_1062_ = lean_ctor_get(v___x_1061_, 1);
lean_inc_ref(v_str_1062_);
lean_dec_ref_known(v___x_1061_, 2);
return v_str_1062_;
}
else
{
lean_object* v___x_1063_; 
lean_dec(v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr___boxed(lean_object* v_item_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1064_);
lean_dec_ref(v_item_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(lean_object* v_item_1066_){
_start:
{
lean_object* v_prevOptionComps_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_prevOptionComps_1067_ = lean_ctor_get(v_item_1066_, 6);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = l_List_get_x3fInternal___redArg(v_prevOptionComps_1067_, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f___boxed(lean_object* v_item_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot_x3f(v_item_1070_);
lean_dec_ref(v_item_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(lean_object* v_item_1072_){
_start:
{
lean_object* v_prevOptionComps_1073_; 
v_prevOptionComps_1073_ = lean_ctor_get(v_item_1072_, 6);
if (lean_obj_tag(v_prevOptionComps_1073_) == 1)
{
lean_object* v_head_1074_; 
v_head_1074_ = lean_ctor_get(v_prevOptionComps_1073_, 0);
lean_inc(v_head_1074_);
return v_head_1074_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot___boxed(lean_object* v_item_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_1076_);
lean_dec_ref(v_item_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
return v_x_1078_;
}
else
{
lean_object* v_head_1080_; lean_object* v_tail_1081_; lean_object* v___x_1082_; 
v_head_1080_ = lean_ctor_get(v_x_1079_, 0);
lean_inc(v_head_1080_);
v_tail_1081_ = lean_ctor_get(v_x_1079_, 1);
lean_inc(v_tail_1081_);
lean_dec_ref_known(v_x_1079_, 2);
v___x_1082_ = l_Lean_Name_appendCore(v_x_1078_, v_head_1080_);
lean_dec(v_x_1078_);
v_x_1078_ = v___x_1082_;
v_x_1079_ = v_tail_1081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
if (lean_obj_tag(v_a_1084_) == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = l_List_reverse___redArg(v_a_1085_);
return v___x_1086_;
}
else
{
lean_object* v_head_1087_; lean_object* v_tail_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1097_; 
v_head_1087_ = lean_ctor_get(v_a_1084_, 0);
v_tail_1088_ = lean_ctor_get(v_a_1084_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1084_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1090_ = v_a_1084_;
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_tail_1088_);
lean_inc(v_head_1087_);
lean_dec(v_a_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = l_Lean_Syntax_getId(v_head_1087_);
lean_dec(v_head_1087_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_a_1085_);
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_a_1085_);
v___x_1094_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v_a_1084_ = v_tail_1088_;
v_a_1085_ = v___x_1094_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(lean_object* v_item_1098_){
_start:
{
lean_object* v_optionComps_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_optionComps_1099_ = lean_ctor_get(v_item_1098_, 5);
lean_inc(v_optionComps_1099_);
lean_dec_ref(v_item_1098_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_box(0);
v___x_1102_ = l_List_mapTR_loop___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__0(v_optionComps_1099_, v___x_1101_);
v___x_1103_ = l_List_foldl___at___00Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName_spec__1(v___x_1100_, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object* v_item_1104_){
_start:
{
lean_object* v_ref_1105_; lean_object* v_option_1106_; lean_object* v_value_1107_; lean_object* v_bool_x3f_1108_; lean_object* v_origOptionName_1109_; lean_object* v_optionComps_1110_; lean_object* v_prevOptionComps_1111_; lean_object* v___y_1113_; 
v_ref_1105_ = lean_ctor_get(v_item_1104_, 0);
lean_inc(v_ref_1105_);
v_option_1106_ = lean_ctor_get(v_item_1104_, 1);
lean_inc(v_option_1106_);
v_value_1107_ = lean_ctor_get(v_item_1104_, 2);
lean_inc(v_value_1107_);
v_bool_x3f_1108_ = lean_ctor_get(v_item_1104_, 3);
lean_inc(v_bool_x3f_1108_);
v_origOptionName_1109_ = lean_ctor_get(v_item_1104_, 4);
lean_inc(v_origOptionName_1109_);
v_optionComps_1110_ = lean_ctor_get(v_item_1104_, 5);
v_prevOptionComps_1111_ = lean_ctor_get(v_item_1104_, 6);
lean_inc(v_prevOptionComps_1111_);
if (lean_obj_tag(v_optionComps_1110_) == 0)
{
v___y_1113_ = v_optionComps_1110_;
goto v___jp_1112_;
}
else
{
lean_object* v_tail_1130_; 
v_tail_1130_ = lean_ctor_get(v_optionComps_1110_, 1);
lean_inc(v_tail_1130_);
v___y_1113_ = v_tail_1130_;
goto v___jp_1112_;
}
v___jp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
v___x_1114_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1104_);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_item_1104_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; lean_object* v_unused_1124_; lean_object* v_unused_1125_; lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; lean_object* v_unused_1129_; 
v_unused_1123_ = lean_ctor_get(v_item_1104_, 6);
lean_dec(v_unused_1123_);
v_unused_1124_ = lean_ctor_get(v_item_1104_, 5);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_item_1104_, 4);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_item_1104_, 3);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_item_1104_, 2);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_item_1104_, 1);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_item_1104_, 0);
lean_dec(v_unused_1129_);
v___x_1116_ = v_item_1104_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_item_1104_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1114_);
lean_ctor_set(v___x_1118_, 1, v_prevOptionComps_1111_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 6, v___x_1118_);
lean_ctor_set(v___x_1116_, 5, v___y_1113_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_ref_1105_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_option_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_value_1107_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_bool_x3f_1108_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_origOptionName_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v___y_1113_);
lean_ctor_set(v_reuseFailAlloc_1121_, 6, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_box(1);
v___x_1132_ = l_Lean_MessageData_ofFormat(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__2));
v___x_1137_ = l_Lean_MessageData_ofFormat(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
return v_x_1138_;
}
else
{
lean_object* v_head_1140_; lean_object* v_tail_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1163_; 
v_head_1140_ = lean_ctor_get(v_x_1139_, 0);
v_tail_1141_ = lean_ctor_get(v_x_1139_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1143_ = v_x_1139_;
v_isShared_1144_ = v_isSharedCheck_1163_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_tail_1141_);
lean_inc(v_head_1140_);
lean_dec(v_x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1163_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_before_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1161_; 
v_before_1145_ = lean_ctor_get(v_head_1140_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_head_1140_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_head_1140_, 1);
lean_dec(v_unused_1162_);
v___x_1147_ = v_head_1140_;
v_isShared_1148_ = v_isSharedCheck_1161_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_before_1145_);
lean_dec(v_head_1140_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1161_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 7);
lean_ctor_set(v___x_1147_, 1, v___x_1149_);
lean_ctor_set(v___x_1147_, 0, v_x_1138_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_x_1138_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 7);
lean_ctor_set(v___x_1143_, 1, v___x_1152_);
lean_ctor_set(v___x_1143_, 0, v___x_1151_);
v___x_1154_ = v___x_1143_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = l_Lean_MessageData_ofSyntax(v_before_1145_);
v___x_1156_ = l_Lean_indentD(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1154_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v_x_1138_ = v___x_1157_;
v_x_1139_ = v_tail_1141_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(lean_object* v_opts_1164_, lean_object* v_opt_1165_){
_start:
{
lean_object* v_name_1166_; lean_object* v_defValue_1167_; lean_object* v_map_1168_; lean_object* v___x_1169_; 
v_name_1166_ = lean_ctor_get(v_opt_1165_, 0);
v_defValue_1167_ = lean_ctor_get(v_opt_1165_, 1);
v_map_1168_ = lean_ctor_get(v_opts_1164_, 0);
v___x_1169_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1168_, v_name_1166_);
if (lean_obj_tag(v___x_1169_) == 0)
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_unbox(v_defValue_1167_);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; 
v_val_1171_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v___x_1169_, 1);
if (lean_obj_tag(v_val_1171_) == 1)
{
uint8_t v_v_1172_; 
v_v_1172_ = lean_ctor_get_uint8(v_val_1171_, 0);
lean_dec_ref_known(v_val_1171_, 0);
return v_v_1172_;
}
else
{
uint8_t v___x_1173_; 
lean_dec(v_val_1171_);
v___x_1173_ = lean_unbox(v_defValue_1167_);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_1174_, lean_object* v_opt_1175_){
_start:
{
uint8_t v_res_1176_; lean_object* v_r_1177_; 
v_res_1176_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_opts_1174_, v_opt_1175_);
lean_dec_ref(v_opt_1175_);
lean_dec_ref(v_opts_1174_);
v_r_1177_ = lean_box(v_res_1176_);
return v_r_1177_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_1182_ = l_Lean_MessageData_ofFormat(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_1183_, lean_object* v_macroStack_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_options_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; 
v_options_1187_ = lean_ctor_get(v___y_1185_, 2);
v___x_1188_ = l_Lean_Elab_pp_macroStack;
v___x_1189_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_1187_, v___x_1188_);
v___x_1190_ = lean_bool_not(v___x_1189_);
if (v___x_1190_ == 0)
{
if (lean_obj_tag(v_macroStack_1184_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_msgData_1183_);
return v___x_1191_;
}
else
{
lean_object* v_head_1192_; lean_object* v_after_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1208_; 
v_head_1192_ = lean_ctor_get(v_macroStack_1184_, 0);
lean_inc(v_head_1192_);
v_after_1193_ = lean_ctor_get(v_head_1192_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_head_1192_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_head_1192_, 0);
lean_dec(v_unused_1209_);
v___x_1195_ = v_head_1192_;
v_isShared_1196_ = v_isSharedCheck_1208_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_after_1193_);
lean_dec(v_head_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1208_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 7);
lean_ctor_set(v___x_1195_, 1, v___x_1197_);
lean_ctor_set(v___x_1195_, 0, v_msgData_1183_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_msgData_1183_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_msgData_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1200_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_MessageData_ofSyntax(v_after_1193_);
v___x_1203_ = l_Lean_indentD(v___x_1202_);
v_msgData_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1204_, 0, v___x_1201_);
lean_ctor_set(v_msgData_1204_, 1, v___x_1203_);
v___x_1205_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__3(v_msgData_1204_, v_macroStack_1184_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
}
else
{
lean_object* v___x_1210_; 
lean_dec(v_macroStack_1184_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_msgData_1183_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_1211_, lean_object* v_macroStack_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1211_, v_macroStack_1212_, v___y_1213_);
lean_dec_ref(v___y_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_ref_1224_; lean_object* v___x_1225_; lean_object* v_a_1226_; lean_object* v_macroStack_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
v_ref_1224_ = lean_ctor_get(v___y_1221_, 5);
v___x_1225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_1216_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1225_);
v_macroStack_1227_ = lean_ctor_get(v___y_1217_, 1);
v___x_1228_ = l_Lean_Elab_getBetterRef(v_ref_1224_, v_macroStack_1227_);
lean_inc(v_macroStack_1227_);
v___x_1229_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_1226_, v_macroStack_1227_, v___y_1221_);
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1228_);
lean_ctor_set(v___x_1234_, 1, v_a_1230_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 1);
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(lean_object* v_ref_1248_, lean_object* v_msg_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_fileName_1257_; lean_object* v_fileMap_1258_; lean_object* v_options_1259_; lean_object* v_currRecDepth_1260_; lean_object* v_maxRecDepth_1261_; lean_object* v_ref_1262_; lean_object* v_currNamespace_1263_; lean_object* v_openDecls_1264_; lean_object* v_initHeartbeats_1265_; lean_object* v_maxHeartbeats_1266_; lean_object* v_quotContext_1267_; lean_object* v_currMacroScope_1268_; uint8_t v_diag_1269_; lean_object* v_cancelTk_x3f_1270_; uint8_t v_suppressElabErrors_1271_; lean_object* v_inheritedTraceOptions_1272_; lean_object* v_ref_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_fileName_1257_ = lean_ctor_get(v___y_1254_, 0);
v_fileMap_1258_ = lean_ctor_get(v___y_1254_, 1);
v_options_1259_ = lean_ctor_get(v___y_1254_, 2);
v_currRecDepth_1260_ = lean_ctor_get(v___y_1254_, 3);
v_maxRecDepth_1261_ = lean_ctor_get(v___y_1254_, 4);
v_ref_1262_ = lean_ctor_get(v___y_1254_, 5);
v_currNamespace_1263_ = lean_ctor_get(v___y_1254_, 6);
v_openDecls_1264_ = lean_ctor_get(v___y_1254_, 7);
v_initHeartbeats_1265_ = lean_ctor_get(v___y_1254_, 8);
v_maxHeartbeats_1266_ = lean_ctor_get(v___y_1254_, 9);
v_quotContext_1267_ = lean_ctor_get(v___y_1254_, 10);
v_currMacroScope_1268_ = lean_ctor_get(v___y_1254_, 11);
v_diag_1269_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*14);
v_cancelTk_x3f_1270_ = lean_ctor_get(v___y_1254_, 12);
v_suppressElabErrors_1271_ = lean_ctor_get_uint8(v___y_1254_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1272_ = lean_ctor_get(v___y_1254_, 13);
v_ref_1273_ = l_Lean_replaceRef(v_ref_1248_, v_ref_1262_);
lean_inc_ref(v_inheritedTraceOptions_1272_);
lean_inc(v_cancelTk_x3f_1270_);
lean_inc(v_currMacroScope_1268_);
lean_inc(v_quotContext_1267_);
lean_inc(v_maxHeartbeats_1266_);
lean_inc(v_initHeartbeats_1265_);
lean_inc(v_openDecls_1264_);
lean_inc(v_currNamespace_1263_);
lean_inc(v_maxRecDepth_1261_);
lean_inc(v_currRecDepth_1260_);
lean_inc_ref(v_options_1259_);
lean_inc_ref(v_fileMap_1258_);
lean_inc_ref(v_fileName_1257_);
v___x_1274_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1274_, 0, v_fileName_1257_);
lean_ctor_set(v___x_1274_, 1, v_fileMap_1258_);
lean_ctor_set(v___x_1274_, 2, v_options_1259_);
lean_ctor_set(v___x_1274_, 3, v_currRecDepth_1260_);
lean_ctor_set(v___x_1274_, 4, v_maxRecDepth_1261_);
lean_ctor_set(v___x_1274_, 5, v_ref_1273_);
lean_ctor_set(v___x_1274_, 6, v_currNamespace_1263_);
lean_ctor_set(v___x_1274_, 7, v_openDecls_1264_);
lean_ctor_set(v___x_1274_, 8, v_initHeartbeats_1265_);
lean_ctor_set(v___x_1274_, 9, v_maxHeartbeats_1266_);
lean_ctor_set(v___x_1274_, 10, v_quotContext_1267_);
lean_ctor_set(v___x_1274_, 11, v_currMacroScope_1268_);
lean_ctor_set(v___x_1274_, 12, v_cancelTk_x3f_1270_);
lean_ctor_set(v___x_1274_, 13, v_inheritedTraceOptions_1272_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*14, v_diag_1269_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*14 + 1, v_suppressElabErrors_1271_);
v___x_1275_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___x_1274_, v___y_1255_);
lean_dec_ref_known(v___x_1274_, 14);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(lean_object* v_ref_1276_, lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1276_, v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
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
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object* v_item_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_bool_x3f_1300_; 
v_bool_x3f_1300_ = lean_ctor_get(v_item_1292_, 3);
if (lean_obj_tag(v_bool_x3f_1300_) == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec_ref(v_item_1292_);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
else
{
lean_object* v_option_1303_; lean_object* v_origOptionName_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_option_1303_ = lean_ctor_get(v_item_1292_, 1);
lean_inc(v_option_1303_);
v_origOptionName_1304_ = lean_ctor_get(v_item_1292_, 4);
lean_inc(v_origOptionName_1304_);
lean_dec_ref(v_item_1292_);
v___x_1305_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1);
v___x_1306_ = l_Lean_MessageData_ofName(v_origOptionName_1304_);
v___x_1307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1303_, v___x_1309_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v_option_1303_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(lean_object* v_item_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(lean_object* v_00_u03b1_1320_, lean_object* v_ref_1321_, lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1321_, v_msg_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___boxed(lean_object* v_00_u03b1_1331_, lean_object* v_ref_1332_, lean_object* v_msg_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(v_00_u03b1_1331_, v_ref_1332_, v_msg_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v_ref_1332_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(lean_object* v_00_u03b1_1342_, lean_object* v_msg_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1352_, lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_1352_, v_msg_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(lean_object* v_msgData_1362_, lean_object* v_macroStack_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1362_, v_macroStack_1363_, v___y_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1372_, lean_object* v_macroStack_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_1372_, v_macroStack_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1381_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0));
v___x_1384_ = l_Lean_stringToMessageData(v___x_1383_);
return v___x_1384_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2));
v___x_1387_ = l_Lean_stringToMessageData(v___x_1386_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4));
v___x_1390_ = l_Lean_stringToMessageData(v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object* v_item_1391_, lean_object* v_structName_x3f_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_option_1400_; lean_object* v_origOptionName_1401_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1410_; uint8_t v___x_1419_; 
v_option_1400_ = lean_ctor_get(v_item_1391_, 1);
lean_inc(v_option_1400_);
v_origOptionName_1401_ = lean_ctor_get(v_item_1391_, 4);
lean_inc(v_origOptionName_1401_);
lean_dec_ref(v_item_1391_);
v___x_1419_ = l_Lean_Name_isAnonymous(v_origOptionName_1401_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1420_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1421_ = l_Lean_MessageData_ofName(v_origOptionName_1401_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___y_1410_ = v___x_1424_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_origOptionName_1401_);
v___x_1425_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1410_ = v___x_1425_;
goto v___jp_1409_;
}
v___jp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1405_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___y_1403_);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___y_1404_);
v___x_1408_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1400_, v___x_1407_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_option_1400_);
return v___x_1408_;
}
v___jp_1409_:
{
if (lean_obj_tag(v_structName_x3f_1392_) == 1)
{
lean_object* v_val_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_val_1411_ = lean_ctor_get(v_structName_x3f_1392_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v_structName_x3f_1392_, 1);
v___x_1412_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1413_ = 0;
v___x_1414_ = l_Lean_MessageData_ofConstName(v_val_1411_, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1412_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___y_1403_ = v___y_1410_;
v___y_1404_ = v___x_1417_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1418_; 
lean_dec(v_structName_x3f_1392_);
v___x_1418_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1403_ = v___y_1410_;
v___y_1404_ = v___x_1418_;
goto v___jp_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___boxed(lean_object* v_item_1426_, lean_object* v_structName_x3f_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1426_, v_structName_x3f_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(lean_object* v_00_u03b1_1436_, lean_object* v_item_1437_, lean_object* v_structName_x3f_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1437_, v_structName_x3f_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_item_1448_, lean_object* v_structName_x3f_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(v_00_u03b1_1447_, v_item_1448_, v_structName_x3f_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
return v_res_1457_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2));
v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(lean_object* v_item_1464_, lean_object* v_structName_x3f_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_option_1473_; lean_object* v_origOptionName_1474_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1485_; uint8_t v___x_1494_; 
v_option_1473_ = lean_ctor_get(v_item_1464_, 1);
lean_inc(v_option_1473_);
v_origOptionName_1474_ = lean_ctor_get(v_item_1464_, 4);
lean_inc(v_origOptionName_1474_);
lean_dec_ref(v_item_1464_);
v___x_1494_ = l_Lean_Name_isAnonymous(v_origOptionName_1474_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1495_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1496_ = l_Lean_MessageData_ofName(v_origOptionName_1474_);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___y_1485_ = v___x_1499_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_origOptionName_1474_);
v___x_1500_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1485_ = v___x_1500_;
goto v___jp_1484_;
}
v___jp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1478_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___y_1476_);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___y_1477_);
v___x_1481_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1473_, v___x_1482_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_option_1473_);
return v___x_1483_;
}
v___jp_1484_:
{
if (lean_obj_tag(v_structName_x3f_1465_) == 1)
{
lean_object* v_val_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_val_1486_ = lean_ctor_get(v_structName_x3f_1465_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v_structName_x3f_1465_, 1);
v___x_1487_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1488_ = 0;
v___x_1489_ = l_Lean_MessageData_ofConstName(v_val_1486_, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1487_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___y_1476_ = v___y_1485_;
v___y_1477_ = v___x_1492_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_structName_x3f_1465_);
v___x_1493_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1476_ = v___y_1485_;
v___y_1477_ = v___x_1493_;
goto v___jp_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___boxed(lean_object* v_item_1501_, lean_object* v_structName_x3f_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1501_, v_structName_x3f_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(lean_object* v_00_u03b1_1511_, lean_object* v_item_1512_, lean_object* v_structName_x3f_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1512_, v_structName_x3f_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_item_1523_, lean_object* v_structName_x3f_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(v_00_u03b1_1522_, v_item_1523_, v_structName_x3f_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
return v_res_1532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
lean_ctor_set(v___x_1538_, 2, v___x_1537_);
lean_ctor_set(v___x_1538_, 3, v___x_1537_);
lean_ctor_set(v___x_1538_, 4, v___x_1536_);
lean_ctor_set(v___x_1538_, 5, v___x_1536_);
lean_ctor_set(v___x_1538_, 6, v___x_1536_);
lean_ctor_set(v___x_1538_, 7, v___x_1536_);
lean_ctor_set(v___x_1538_, 8, v___x_1536_);
lean_ctor_set(v___x_1538_, 9, v___x_1536_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_unsigned_to_nat(32u);
v___x_1540_ = lean_mk_empty_array_with_capacity(v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1542_ = ((size_t)5ULL);
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_unsigned_to_nat(32u);
v___x_1545_ = lean_mk_empty_array_with_capacity(v___x_1544_);
v___x_1546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1547_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1545_);
lean_ctor_set(v___x_1547_, 2, v___x_1543_);
lean_ctor_set(v___x_1547_, 3, v___x_1543_);
lean_ctor_set_usize(v___x_1547_, 4, v___x_1542_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = lean_box(1);
v___x_1549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___x_1549_);
lean_ctor_set(v___x_1551_, 2, v___x_1548_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1573_, lean_object* v_declHint_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_env_1578_; uint8_t v___y_1580_; uint8_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1577_ = lean_st_ref_get(v___y_1575_);
v_env_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_env_1578_);
lean_dec(v___x_1577_);
v___x_1636_ = l_Lean_Name_isAnonymous(v_declHint_1574_);
v___x_1637_ = lean_bool_not(v___x_1636_);
if (v___x_1637_ == 0)
{
v___y_1580_ = v___x_1637_;
goto v___jp_1579_;
}
else
{
uint8_t v_isExporting_1638_; 
v_isExporting_1638_ = lean_ctor_get_uint8(v_env_1578_, sizeof(void*)*8);
v___y_1580_ = v_isExporting_1638_;
goto v___jp_1579_;
}
v___jp_1579_:
{
if (v___y_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref(v_env_1578_);
lean_dec(v_declHint_1574_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_msg_1573_);
return v___x_1581_;
}
else
{
uint8_t v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = 0;
lean_inc_ref(v_env_1578_);
v___x_1583_ = l_Lean_Environment_setExporting(v_env_1578_, v___x_1582_);
lean_inc(v_declHint_1574_);
lean_inc_ref(v___x_1583_);
v___x_1584_ = l_Lean_Environment_contains(v___x_1583_, v_declHint_1574_, v___y_1580_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref(v___x_1583_);
lean_dec_ref(v_env_1578_);
lean_dec(v_declHint_1574_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_msg_1573_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_c_1591_; lean_object* v___x_1592_; 
v___x_1586_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1588_ = l_Lean_Options_empty;
v___x_1589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1583_);
lean_ctor_set(v___x_1589_, 1, v___x_1586_);
lean_ctor_set(v___x_1589_, 2, v___x_1587_);
lean_ctor_set(v___x_1589_, 3, v___x_1588_);
lean_inc(v_declHint_1574_);
v___x_1590_ = l_Lean_MessageData_ofConstName(v_declHint_1574_, v___x_1582_);
v_c_1591_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1591_, 0, v___x_1589_);
lean_ctor_set(v_c_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1578_, v_declHint_1574_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v_env_1578_);
lean_dec(v_declHint_1574_);
v___x_1593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_c_1591_);
v___x_1595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_Lean_MessageData_note(v___x_1596_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_msg_1573_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1635_; 
v_val_1600_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1602_ = v___x_1592_;
v_isShared_1603_ = v_isSharedCheck_1635_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_val_1600_);
lean_dec(v___x_1592_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1635_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v_mod_1607_; uint8_t v___x_1608_; 
v___x_1604_ = lean_box(0);
v___x_1605_ = l_Lean_Environment_header(v_env_1578_);
lean_dec_ref(v_env_1578_);
v___x_1606_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1605_);
v_mod_1607_ = lean_array_get(v___x_1604_, v___x_1606_, v_val_1600_);
lean_dec(v_val_1600_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = l_Lean_isPrivateName(v_declHint_1574_);
lean_dec(v_declHint_1574_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_c_1591_);
v___x_1611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_MessageData_ofName(v_mod_1607_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_MessageData_note(v___x_1616_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_msg_1573_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1618_);
v___x_1620_ = v___x_1602_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v_c_1591_);
v___x_1624_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_Lean_MessageData_ofName(v_mod_1607_);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = l_Lean_MessageData_note(v___x_1629_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v_msg_1573_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1631_);
v___x_1633_ = v___x_1602_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1639_, lean_object* v_declHint_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1639_, v_declHint_1640_, v___y_1641_);
lean_dec(v___y_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_1644_, lean_object* v_declHint_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1663_; 
v___x_1653_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1644_, v_declHint_1645_, v___y_1651_);
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1663_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1663_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1658_ = l_Lean_unknownIdentifierMessageTag;
v___x_1659_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_a_1654_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1659_);
v___x_1661_ = v___x_1656_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_1664_, lean_object* v_declHint_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1664_, v_declHint_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1674_, lean_object* v_msg_1675_, lean_object* v_declHint_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1686_; 
v___x_1684_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1675_, v_declHint_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1674_, v_a_1685_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1687_, lean_object* v_msg_1688_, lean_object* v_declHint_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1687_, v_msg_1688_, v_declHint_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v_ref_1687_);
return v_res_1697_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_1701_, lean_object* v_constName_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1710_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1711_ = 0;
lean_inc(v_constName_1702_);
v___x_1712_ = l_Lean_MessageData_ofConstName(v_constName_1702_, v___x_1711_);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1710_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1701_, v___x_1715_, v_constName_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1717_, lean_object* v_constName_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1717_, v_constName_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v_ref_1717_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_ref_1735_; lean_object* v___x_1736_; 
v_ref_1735_ = lean_ctor_get(v___y_1732_, 5);
v___x_1736_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1735_, v_constName_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object* v_constName_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v_env_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = lean_st_ref_get(v___y_1752_);
v_env_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_ref(v_env_1755_);
lean_dec(v___x_1754_);
v___x_1756_ = 0;
lean_inc(v_constName_1746_);
v___x_1757_ = l_Lean_Environment_findConstVal_x3f(v_env_1755_, v_constName_1746_, v___x_1756_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1758_;
}
else
{
lean_object* v_val_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_constName_1746_);
v_val_1759_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1757_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_val_1759_);
lean_dec(v___x_1757_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 0);
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_val_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
if (lean_obj_tag(v_a_1776_) == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = l_List_reverse___redArg(v_a_1777_);
return v___x_1778_;
}
else
{
lean_object* v_head_1779_; lean_object* v_tail_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1789_; 
v_head_1779_ = lean_ctor_get(v_a_1776_, 0);
v_tail_1780_ = lean_ctor_get(v_a_1776_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_a_1776_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1782_ = v_a_1776_;
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_tail_1780_);
lean_inc(v_head_1779_);
lean_dec(v_a_1776_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = l_Lean_mkLevelParam(v_head_1779_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v_a_1777_);
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_a_1777_);
v___x_1786_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
v_a_1776_ = v_tail_1780_;
v_a_1777_ = v___x_1786_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object* v_constName_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
lean_inc(v_constName_1790_);
v___x_1798_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1810_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1810_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1810_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_levelParams_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v_levelParams_1803_ = lean_ctor_get(v_a_1799_, 1);
lean_inc(v_levelParams_1803_);
lean_dec(v_a_1799_);
v___x_1804_ = lean_box(0);
v___x_1805_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_1803_, v___x_1804_);
v___x_1806_ = l_Lean_mkConst(v_constName_1790_, v___x_1805_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1806_);
v___x_1808_ = v___x_1801_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_constName_1790_);
v_a_1811_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1798_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1798_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object* v_constName_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; lean_object* v_infoState_1832_; uint8_t v_enabled_1833_; 
v___x_1831_ = lean_st_ref_get(v___y_1829_);
v_infoState_1832_ = lean_ctor_get(v___x_1831_, 7);
lean_inc_ref(v_infoState_1832_);
lean_dec(v___x_1831_);
v_enabled_1833_ = lean_ctor_get_uint8(v_infoState_1832_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1832_);
if (v_enabled_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref(v_t_1828_);
v___x_1834_ = lean_box(0);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
else
{
lean_object* v___x_1836_; lean_object* v_infoState_1837_; lean_object* v_env_1838_; lean_object* v_nextMacroScope_1839_; lean_object* v_ngen_1840_; lean_object* v_auxDeclNGen_1841_; lean_object* v_traceState_1842_; lean_object* v_cache_1843_; lean_object* v_messages_1844_; lean_object* v_snapshotTasks_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1867_; 
v___x_1836_ = lean_st_ref_take(v___y_1829_);
v_infoState_1837_ = lean_ctor_get(v___x_1836_, 7);
v_env_1838_ = lean_ctor_get(v___x_1836_, 0);
v_nextMacroScope_1839_ = lean_ctor_get(v___x_1836_, 1);
v_ngen_1840_ = lean_ctor_get(v___x_1836_, 2);
v_auxDeclNGen_1841_ = lean_ctor_get(v___x_1836_, 3);
v_traceState_1842_ = lean_ctor_get(v___x_1836_, 4);
v_cache_1843_ = lean_ctor_get(v___x_1836_, 5);
v_messages_1844_ = lean_ctor_get(v___x_1836_, 6);
v_snapshotTasks_1845_ = lean_ctor_get(v___x_1836_, 8);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1847_ = v___x_1836_;
v_isShared_1848_ = v_isSharedCheck_1867_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_snapshotTasks_1845_);
lean_inc(v_infoState_1837_);
lean_inc(v_messages_1844_);
lean_inc(v_cache_1843_);
lean_inc(v_traceState_1842_);
lean_inc(v_auxDeclNGen_1841_);
lean_inc(v_ngen_1840_);
lean_inc(v_nextMacroScope_1839_);
lean_inc(v_env_1838_);
lean_dec(v___x_1836_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1867_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
uint8_t v_enabled_1849_; lean_object* v_assignment_1850_; lean_object* v_lazyAssignment_1851_; lean_object* v_trees_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1866_; 
v_enabled_1849_ = lean_ctor_get_uint8(v_infoState_1837_, sizeof(void*)*3);
v_assignment_1850_ = lean_ctor_get(v_infoState_1837_, 0);
v_lazyAssignment_1851_ = lean_ctor_get(v_infoState_1837_, 1);
v_trees_1852_ = lean_ctor_get(v_infoState_1837_, 2);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_infoState_1837_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1854_ = v_infoState_1837_;
v_isShared_1855_ = v_isSharedCheck_1866_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_trees_1852_);
lean_inc(v_lazyAssignment_1851_);
lean_inc(v_assignment_1850_);
lean_dec(v_infoState_1837_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1866_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1856_ = l_Lean_PersistentArray_push___redArg(v_trees_1852_, v_t_1828_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 2, v___x_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_assignment_1850_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_lazyAssignment_1851_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v___x_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*3, v_enabled_1849_);
v___x_1858_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1860_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 7, v___x_1858_);
v___x_1860_ = v___x_1847_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_env_1838_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_nextMacroScope_1839_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_ngen_1840_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_auxDeclNGen_1841_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_traceState_1842_);
lean_ctor_set(v_reuseFailAlloc_1864_, 5, v_cache_1843_);
lean_ctor_set(v_reuseFailAlloc_1864_, 6, v_messages_1844_);
lean_ctor_set(v_reuseFailAlloc_1864_, 7, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1864_, 8, v_snapshotTasks_1845_);
v___x_1860_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = lean_st_ref_set(v___y_1829_, v___x_1860_);
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1868_, v___y_1869_);
lean_dec(v___y_1869_);
return v_res_1871_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_unsigned_to_nat(32u);
v___x_1873_ = lean_mk_empty_array_with_capacity(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1875_ = ((size_t)5ULL);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_unsigned_to_nat(32u);
v___x_1878_ = lean_mk_empty_array_with_capacity(v___x_1877_);
v___x_1879_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
v___x_1880_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___x_1878_);
lean_ctor_set(v___x_1880_, 2, v___x_1876_);
lean_ctor_set(v___x_1880_, 3, v___x_1876_);
lean_ctor_set_usize(v___x_1880_, 4, v___x_1875_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object* v_t_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v_infoState_1890_; uint8_t v_enabled_1891_; 
v___x_1889_ = lean_st_ref_get(v___y_1887_);
v_infoState_1890_ = lean_ctor_get(v___x_1889_, 7);
lean_inc_ref(v_infoState_1890_);
lean_dec(v___x_1889_);
v_enabled_1891_ = lean_ctor_get_uint8(v_infoState_1890_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1890_);
if (v_enabled_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec_ref(v_t_1881_);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
v___x_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_t_1881_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_1895_, v___y_1887_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object* v_t_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object* v_stx_1906_, lean_object* v_n_1907_, lean_object* v_expectedType_x3f_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_1907_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v_stx_1906_);
v___x_1920_ = l_Lean_LocalContext_empty;
v___x_1921_ = 0;
v___x_1922_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1922_, 0, v___x_1919_);
lean_ctor_set(v___x_1922_, 1, v___x_1920_);
lean_ctor_set(v___x_1922_, 2, v_expectedType_x3f_1908_);
lean_ctor_set(v___x_1922_, 3, v_a_1917_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*4, v___x_1921_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*4 + 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
v___x_1924_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1923_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
return v___x_1924_;
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_expectedType_x3f_1908_);
lean_dec(v_stx_1906_);
v_a_1925_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1916_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1916_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object* v_stx_1933_, lean_object* v_n_1934_, lean_object* v_expectedType_x3f_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1933_, v_n_1934_, v_expectedType_x3f_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object* v_item_1944_, lean_object* v_projFn_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v_infoState_1954_; uint8_t v_enabled_1955_; 
v___x_1953_ = lean_st_ref_get(v_a_1951_);
v_infoState_1954_ = lean_ctor_get(v___x_1953_, 7);
lean_inc_ref(v_infoState_1954_);
lean_dec(v___x_1953_);
v_enabled_1955_ = lean_ctor_get_uint8(v_infoState_1954_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1954_);
if (v_enabled_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec(v_projFn_1945_);
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; lean_object* v_env_1959_; uint8_t v___x_1960_; 
v___x_1958_ = lean_st_ref_get(v_a_1951_);
v_env_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref(v_env_1959_);
lean_dec(v___x_1958_);
lean_inc(v_projFn_1945_);
v___x_1960_ = l_Lean_Environment_contains(v_env_1959_, v_projFn_1945_, v_enabled_1955_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v_projFn_1945_);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1944_);
v___x_1964_ = lean_box(0);
v___x_1965_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_1963_, v_projFn_1945_, v___x_1964_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object* v_item_1966_, lean_object* v_projFn_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1966_, v_projFn_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_item_1966_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object* v_t_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1976_, v___y_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1994_, lean_object* v_constName_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_constName_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2004_, v_constName_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2014_, lean_object* v_ref_2015_, lean_object* v_constName_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2015_, v_constName_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2025_, lean_object* v_ref_2026_, lean_object* v_constName_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2025_, v_ref_2026_, v_constName_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v_ref_2026_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2036_, lean_object* v_ref_2037_, lean_object* v_msg_2038_, lean_object* v_declHint_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2037_, v_msg_2038_, v_declHint_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_ref_2049_, lean_object* v_msg_2050_, lean_object* v_declHint_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2048_, v_ref_2049_, v_msg_2050_, v_declHint_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v_ref_2049_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2060_, lean_object* v_declHint_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2060_, v_declHint_2061_, v___y_2067_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2070_, lean_object* v_declHint_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2070_, v_declHint_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object* v_info_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_info_2080_);
v___x_2089_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_2088_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
return v___x_2089_;
}
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
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2099_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2102_ = lean_box(1);
v___x_2103_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2104_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
lean_ctor_set(v___x_2105_, 2, v___x_2102_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object* v_item_2106_, lean_object* v_structName_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v_infoState_2116_; uint8_t v_enabled_2117_; 
v___x_2115_ = lean_st_ref_get(v_a_2113_);
v_infoState_2116_ = lean_ctor_get(v___x_2115_, 7);
lean_inc_ref(v_infoState_2116_);
lean_dec(v___x_2115_);
v_enabled_2117_ = lean_ctor_get_uint8(v_infoState_2116_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2116_);
if (v_enabled_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec(v_structName_2107_);
v___x_2118_ = lean_box(0);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; lean_object* v_env_2121_; uint8_t v___x_2122_; 
v___x_2120_ = lean_st_ref_get(v_a_2113_);
v_env_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc_ref(v_env_2121_);
lean_dec(v___x_2120_);
lean_inc(v_structName_2107_);
v___x_2122_ = l_Lean_Environment_contains(v_env_2121_, v_structName_2107_, v_enabled_2117_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec(v_structName_2107_);
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2125_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_2106_);
v___x_2126_ = l_Lean_Syntax_getId(v___x_2125_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
v___x_2128_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2);
v___x_2129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2125_);
lean_ctor_set(v___x_2129_, 1, v___x_2127_);
lean_ctor_set(v___x_2129_, 2, v___x_2128_);
lean_ctor_set(v___x_2129_, 3, v_structName_2107_);
v___x_2130_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2129_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2130_;
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t v_x_2152_){
_start:
{
uint32_t v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = 46;
v___x_2154_ = lean_uint32_dec_eq(v_x_2152_, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object* v_x_2155_){
_start:
{
uint32_t v_x_1685__boxed_2156_; uint8_t v_res_2157_; lean_object* v_r_2158_; 
v_x_1685__boxed_2156_ = lean_unbox_uint32(v_x_2155_);
lean_dec(v_x_2155_);
v_res_2157_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_1685__boxed_2156_);
v_r_2158_ = lean_box(v_res_2157_);
return v_r_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object* v___f_2159_, lean_object* v_s_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2159_);
v___x_2168_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2160_, v___x_2167_, v___y_2161_, lean_box(0), lean_box(0), v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object* v___f_2170_, lean_object* v_si_2171_, lean_object* v_val_2172_){
_start:
{
lean_object* v___y_2174_; lean_object* v___f_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___f_2180_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0));
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_string_utf8_byte_size(v_val_2172_);
lean_inc_ref(v_val_2172_);
v___x_2183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2183_, 0, v_val_2172_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
lean_ctor_set(v___x_2183_, 2, v___x_2182_);
v___x_2184_ = l_String_Slice_contains___redArg(v___f_2170_, v___x_2183_, v___f_2180_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_box(0);
lean_inc_ref(v_val_2172_);
v___x_2186_ = l_Lean_Name_str___override(v___x_2185_, v_val_2172_);
v___y_2174_ = v___x_2186_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2187_; 
lean_inc_ref(v_val_2172_);
v___x_2187_ = l_String_toName(v_val_2172_);
v___y_2174_ = v___x_2187_;
goto v___jp_2173_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_string_utf8_byte_size(v_val_2172_);
v___x_2177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2177_, 0, v_val_2172_);
lean_ctor_set(v___x_2177_, 1, v___x_2175_);
lean_ctor_set(v___x_2177_, 2, v___x_2176_);
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2179_, 0, v_si_2171_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
lean_ctor_set(v___x_2179_, 2, v___y_2174_);
lean_ctor_set(v___x_2179_, 3, v___x_2178_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object* v_atomAsIdent_2188_, lean_object* v_stx_2189_){
_start:
{
switch(lean_obj_tag(v_stx_2189_))
{
case 3:
{
lean_object* v___x_2190_; 
lean_dec_ref(v_atomAsIdent_2188_);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_stx_2189_);
return v___x_2190_;
}
case 2:
{
lean_object* v_info_2191_; lean_object* v_val_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_info_2191_ = lean_ctor_get(v_stx_2189_, 0);
lean_inc(v_info_2191_);
v_val_2192_ = lean_ctor_get(v_stx_2189_, 1);
lean_inc_ref(v_val_2192_);
lean_dec_ref_known(v_stx_2189_, 2);
v___x_2193_ = lean_apply_2(v_atomAsIdent_2188_, v_info_2191_, v_val_2192_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
default: 
{
lean_object* v___x_2195_; 
lean_dec(v_stx_2189_);
lean_dec_ref(v_atomAsIdent_2188_);
v___x_2195_ = lean_box(0);
return v___x_2195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_init_2221_, lean_object* v_cfgs_2222_, lean_object* v_k_2223_, lean_object* v_onErr_2224_){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_array_get_size(v_cfgs_2222_);
v___x_2227_ = lean_nat_dec_lt(v___x_2225_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v_toApplicative_2228_; lean_object* v_toPure_2229_; lean_object* v___x_2230_; 
lean_dec(v_onErr_2224_);
lean_dec(v_k_2223_);
lean_dec_ref(v_cfgs_2222_);
lean_dec_ref(v_inst_2220_);
v_toApplicative_2228_ = lean_ctor_get(v_inst_2219_, 0);
lean_inc_ref(v_toApplicative_2228_);
lean_dec_ref(v_inst_2219_);
v_toPure_2229_ = lean_ctor_get(v_toApplicative_2228_, 1);
lean_inc(v_toPure_2229_);
lean_dec_ref(v_toApplicative_2228_);
v___x_2230_ = lean_apply_2(v_toPure_2229_, lean_box(0), v_init_2221_);
return v___x_2230_;
}
else
{
lean_object* v___f_2231_; uint8_t v___x_2232_; 
lean_inc_ref(v_inst_2219_);
v___f_2231_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_2231_, 0, v_inst_2219_);
lean_closure_set(v___f_2231_, 1, v_inst_2220_);
lean_closure_set(v___f_2231_, 2, v_k_2223_);
lean_closure_set(v___f_2231_, 3, v_onErr_2224_);
v___x_2232_ = lean_nat_dec_le(v___x_2226_, v___x_2226_);
if (v___x_2232_ == 0)
{
if (v___x_2227_ == 0)
{
lean_object* v_toApplicative_2233_; lean_object* v_toPure_2234_; lean_object* v___x_2235_; 
lean_dec_ref(v___f_2231_);
lean_dec_ref(v_cfgs_2222_);
v_toApplicative_2233_ = lean_ctor_get(v_inst_2219_, 0);
lean_inc_ref(v_toApplicative_2233_);
lean_dec_ref(v_inst_2219_);
v_toPure_2234_ = lean_ctor_get(v_toApplicative_2233_, 1);
lean_inc(v_toPure_2234_);
lean_dec_ref(v_toApplicative_2233_);
v___x_2235_ = lean_apply_2(v_toPure_2234_, lean_box(0), v_init_2221_);
return v___x_2235_;
}
else
{
size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = lean_usize_of_nat(v___x_2226_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2219_, v___f_2231_, v_cfgs_2222_, v___x_2236_, v___x_2237_, v_init_2221_);
return v___x_2238_;
}
}
else
{
size_t v___x_2239_; size_t v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = ((size_t)0ULL);
v___x_2240_ = lean_usize_of_nat(v___x_2226_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2219_, v___f_2231_, v_cfgs_2222_, v___x_2239_, v___x_2240_, v_init_2221_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_init_2244_, lean_object* v_cfg_2245_, lean_object* v_k_2246_, lean_object* v_onErr_2247_){
_start:
{
lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2245_);
v___x_2267_ = l_Lean_Syntax_isOfKind(v_cfg_2245_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2268_ = l_Lean_Syntax_getNumArgs(v_cfg_2245_);
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_dec_eq(v___x_2268_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___f_2271_; lean_object* v_atomAsIdent_2272_; uint8_t v___x_2273_; 
v___f_2271_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3));
v_atomAsIdent_2272_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4));
v___x_2273_ = lean_nat_dec_le(v___x_2269_, v___x_2268_);
if (v___x_2273_ == 0)
{
lean_dec(v___x_2268_);
if (lean_obj_tag(v_cfg_2245_) == 2)
{
lean_object* v_info_2274_; lean_object* v_val_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec(v_onErr_2247_);
lean_dec_ref(v_inst_2243_);
lean_dec_ref(v_inst_2242_);
v_info_2274_ = lean_ctor_get(v_cfg_2245_, 0);
v_val_2275_ = lean_ctor_get(v_cfg_2245_, 1);
lean_inc_ref(v_val_2275_);
lean_inc(v_info_2274_);
v___x_2276_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(v___f_2271_, v_info_2274_, v_val_2275_);
v___x_2277_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2278_ = l_Lean_mkCIdentFrom(v_cfg_2245_, v___x_2277_, v___x_2270_);
v___x_2279_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2280_ = l_Lean_TSyntax_getId(v___x_2276_);
v___x_2281_ = l_Lean_Name_eraseMacroScopes(v___x_2280_);
lean_dec(v___x_2280_);
v___x_2282_ = lean_box(0);
lean_inc(v___x_2276_);
v___x_2283_ = l_Lean_Syntax_identComponents(v___x_2276_, v___x_2282_);
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2285_, 0, v_cfg_2245_);
lean_ctor_set(v___x_2285_, 1, v___x_2276_);
lean_ctor_set(v___x_2285_, 2, v___x_2278_);
lean_ctor_set(v___x_2285_, 3, v___x_2279_);
lean_ctor_set(v___x_2285_, 4, v___x_2281_);
lean_ctor_set(v___x_2285_, 5, v___x_2283_);
lean_ctor_set(v___x_2285_, 6, v___x_2284_);
v___x_2286_ = lean_apply_2(v_k_2246_, v_init_2244_, v___x_2285_);
return v___x_2286_;
}
else
{
lean_dec(v_k_2246_);
goto v___jp_2259_;
}
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_unsigned_to_nat(0u);
v___x_2288_ = l_Lean_Syntax_getArg(v_cfg_2245_, v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 2)
{
lean_object* v_val_2289_; lean_object* v___y_2291_; uint8_t v_val_2292_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_val_2289_ = lean_ctor_get(v___x_2288_, 1);
lean_inc_ref(v_val_2289_);
v___x_2303_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2304_ = lean_string_dec_eq(v_val_2289_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2306_ = lean_string_dec_eq(v_val_2289_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
lean_dec_ref_known(v___x_2288_, 2);
v___x_2307_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2308_ = lean_string_dec_eq(v_val_2289_, v___x_2307_);
lean_dec_ref(v_val_2289_);
if (v___x_2308_ == 0)
{
lean_dec(v___x_2268_);
lean_dec(v_k_2246_);
goto v___jp_2259_;
}
else
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = lean_unsigned_to_nat(5u);
v___x_2310_ = lean_nat_dec_le(v___x_2268_, v___x_2309_);
lean_dec(v___x_2268_);
if (v___x_2310_ == 0)
{
lean_dec(v_k_2246_);
goto v___jp_2259_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = l_Lean_Syntax_getArg(v_cfg_2245_, v___x_2269_);
v___x_2312_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2272_, v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 1)
{
lean_object* v_val_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec(v_onErr_2247_);
lean_dec_ref(v_inst_2243_);
lean_dec_ref(v_inst_2242_);
v_val_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc_n(v_val_2313_, 2);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2314_ = lean_unsigned_to_nat(3u);
v___x_2315_ = l_Lean_Syntax_getArg(v_cfg_2245_, v___x_2314_);
v___x_2316_ = lean_box(0);
v___x_2317_ = l_Lean_TSyntax_getId(v_val_2313_);
v___x_2318_ = l_Lean_Name_eraseMacroScopes(v___x_2317_);
lean_dec(v___x_2317_);
v___x_2319_ = l_Lean_Syntax_identComponents(v_val_2313_, v___x_2316_);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2321_, 0, v_cfg_2245_);
lean_ctor_set(v___x_2321_, 1, v_val_2313_);
lean_ctor_set(v___x_2321_, 2, v___x_2315_);
lean_ctor_set(v___x_2321_, 3, v___x_2316_);
lean_ctor_set(v___x_2321_, 4, v___x_2318_);
lean_ctor_set(v___x_2321_, 5, v___x_2319_);
lean_ctor_set(v___x_2321_, 6, v___x_2320_);
v___x_2322_ = lean_apply_2(v_k_2246_, v_init_2244_, v___x_2321_);
return v___x_2322_;
}
else
{
lean_dec(v___x_2312_);
lean_dec(v_k_2246_);
goto v___jp_2259_;
}
}
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec_ref(v_val_2289_);
v___x_2323_ = lean_box(v___x_2270_);
v___x_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
v___y_2291_ = v___x_2324_;
v_val_2292_ = v___x_2270_;
goto v___jp_2290_;
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v_val_2289_);
v___x_2325_ = lean_box(v___x_2304_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
v___y_2291_ = v___x_2326_;
v_val_2292_ = v___x_2304_;
goto v___jp_2290_;
}
v___jp_2290_:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_unsigned_to_nat(2u);
v___x_2294_ = lean_nat_dec_eq(v___x_2268_, v___x_2293_);
lean_dec(v___x_2268_);
if (v___x_2294_ == 0)
{
lean_dec(v___y_2291_);
lean_dec_ref_known(v___x_2288_, 2);
lean_dec(v_k_2246_);
goto v___jp_2259_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = l_Lean_Syntax_getArg(v_cfg_2245_, v___x_2269_);
v___x_2296_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2272_, v___x_2295_);
if (lean_obj_tag(v___x_2296_) == 1)
{
lean_dec(v_onErr_2247_);
lean_dec_ref(v_inst_2243_);
lean_dec_ref(v_inst_2242_);
if (v_val_2292_ == 0)
{
lean_object* v_val_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_val_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_val_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2299_ = l_Lean_mkCIdentFrom(v___x_2288_, v___x_2298_, v___x_2270_);
lean_dec_ref_known(v___x_2288_, 2);
v___y_2249_ = v___y_2291_;
v___y_2250_ = v_val_2297_;
v___y_2251_ = v___x_2299_;
goto v___jp_2248_;
}
else
{
lean_object* v_val_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_val_2300_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2301_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2302_ = l_Lean_mkCIdentFrom(v___x_2288_, v___x_2301_, v___x_2270_);
lean_dec_ref_known(v___x_2288_, 2);
v___y_2249_ = v___y_2291_;
v___y_2250_ = v_val_2300_;
v___y_2251_ = v___x_2302_;
goto v___jp_2248_;
}
}
else
{
lean_dec(v___x_2296_);
lean_dec(v___y_2291_);
lean_dec_ref_known(v___x_2288_, 2);
lean_dec(v_k_2246_);
goto v___jp_2259_;
}
}
}
}
else
{
lean_dec(v___x_2288_);
lean_dec(v___x_2268_);
lean_dec(v_k_2246_);
goto v___jp_2259_;
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec(v___x_2268_);
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = l_Lean_Syntax_getArg(v_cfg_2245_, v___x_2327_);
lean_dec(v_cfg_2245_);
v_cfg_2245_ = v___x_2328_;
goto _start;
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = l_Lean_Syntax_getArgs(v_cfg_2245_);
lean_dec(v_cfg_2245_);
v___x_2331_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2242_, v_inst_2243_, v_init_2244_, v___x_2330_, v_k_2246_, v_onErr_2247_);
return v___x_2331_;
}
v___jp_2248_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2252_ = l_Lean_TSyntax_getId(v___y_2250_);
v___x_2253_ = l_Lean_Name_eraseMacroScopes(v___x_2252_);
lean_dec(v___x_2252_);
v___x_2254_ = lean_box(0);
lean_inc(v___y_2250_);
v___x_2255_ = l_Lean_Syntax_identComponents(v___y_2250_, v___x_2254_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2257_, 0, v_cfg_2245_);
lean_ctor_set(v___x_2257_, 1, v___y_2250_);
lean_ctor_set(v___x_2257_, 2, v___y_2251_);
lean_ctor_set(v___x_2257_, 3, v___y_2249_);
lean_ctor_set(v___x_2257_, 4, v___x_2253_);
lean_ctor_set(v___x_2257_, 5, v___x_2255_);
lean_ctor_set(v___x_2257_, 6, v___x_2256_);
v___x_2258_ = lean_apply_2(v_k_2246_, v_init_2244_, v___x_2257_);
return v___x_2258_;
}
v___jp_2259_:
{
lean_object* v_toBind_2260_; lean_object* v_getRef_2261_; lean_object* v_withRef_2262_; lean_object* v___x_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; 
v_toBind_2260_ = lean_ctor_get(v_inst_2242_, 1);
lean_inc(v_toBind_2260_);
lean_dec_ref(v_inst_2242_);
v_getRef_2261_ = lean_ctor_get(v_inst_2243_, 0);
lean_inc(v_getRef_2261_);
v_withRef_2262_ = lean_ctor_get(v_inst_2243_, 1);
lean_inc(v_withRef_2262_);
lean_dec_ref(v_inst_2243_);
lean_inc(v_cfg_2245_);
v___x_2263_ = lean_apply_2(v_onErr_2247_, v_init_2244_, v_cfg_2245_);
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2264_, 0, v_cfg_2245_);
lean_closure_set(v___f_2264_, 1, v_withRef_2262_);
lean_closure_set(v___f_2264_, 2, v___x_2263_);
v___x_2265_ = lean_apply_4(v_toBind_2260_, lean_box(0), lean_box(0), v_getRef_2261_, v___f_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_k_2334_, lean_object* v_onErr_2335_, lean_object* v_x_2336_, lean_object* v_cfg_x27_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2332_, v_inst_2333_, v_x_2336_, v_cfg_x27_2337_, v_k_2334_, v_onErr_2335_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object* v_00_u03b1_2339_, lean_object* v_m_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_init_2343_, lean_object* v_cfg_2344_, lean_object* v_k_2345_, lean_object* v_onErr_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2341_, v_inst_2342_, v_init_2343_, v_cfg_2344_, v_k_2345_, v_onErr_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object* v_00_u03b1_2348_, lean_object* v_m_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_init_2352_, lean_object* v_cfgs_2353_, lean_object* v_k_2354_, lean_object* v_onErr_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2350_, v_inst_2351_, v_init_2352_, v_cfgs_2353_, v_k_2354_, v_onErr_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v___y_2365_, uint8_t v_suppressElabErrors_2366_, lean_object* v_x_2367_){
_start:
{
if (lean_obj_tag(v_x_2367_) == 1)
{
lean_object* v_pre_2368_; 
v_pre_2368_ = lean_ctor_get(v_x_2367_, 0);
switch(lean_obj_tag(v_pre_2368_))
{
case 1:
{
lean_object* v_pre_2369_; 
v_pre_2369_ = lean_ctor_get(v_pre_2368_, 0);
switch(lean_obj_tag(v_pre_2369_))
{
case 0:
{
lean_object* v_str_2370_; lean_object* v_str_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v_str_2370_ = lean_ctor_get(v_x_2367_, 1);
v_str_2371_ = lean_ctor_get(v_pre_2368_, 1);
v___x_2372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_2373_ = lean_string_dec_eq(v_str_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_2375_ = lean_string_dec_eq(v_str_2371_, v___x_2374_);
if (v___x_2375_ == 0)
{
return v___y_2365_;
}
else
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_2377_ = lean_string_dec_eq(v_str_2370_, v___x_2376_);
if (v___x_2377_ == 0)
{
return v___y_2365_;
}
else
{
return v_suppressElabErrors_2366_;
}
}
}
else
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_2379_ = lean_string_dec_eq(v_str_2370_, v___x_2378_);
if (v___x_2379_ == 0)
{
return v___y_2365_;
}
else
{
return v_suppressElabErrors_2366_;
}
}
}
case 1:
{
lean_object* v_pre_2380_; 
v_pre_2380_ = lean_ctor_get(v_pre_2369_, 0);
if (lean_obj_tag(v_pre_2380_) == 0)
{
lean_object* v_str_2381_; lean_object* v_str_2382_; lean_object* v_str_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_str_2381_ = lean_ctor_get(v_x_2367_, 1);
v_str_2382_ = lean_ctor_get(v_pre_2368_, 1);
v_str_2383_ = lean_ctor_get(v_pre_2369_, 1);
v___x_2384_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_2385_ = lean_string_dec_eq(v_str_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
return v___y_2365_;
}
else
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_2387_ = lean_string_dec_eq(v_str_2382_, v___x_2386_);
if (v___x_2387_ == 0)
{
return v___y_2365_;
}
else
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_2389_ = lean_string_dec_eq(v_str_2381_, v___x_2388_);
if (v___x_2389_ == 0)
{
return v___y_2365_;
}
else
{
return v_suppressElabErrors_2366_;
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
lean_object* v_str_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_str_2390_ = lean_ctor_get(v_x_2367_, 1);
v___x_2391_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_2392_ = lean_string_dec_eq(v_str_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
return v___y_2365_;
}
else
{
return v_suppressElabErrors_2366_;
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_2393_, lean_object* v_suppressElabErrors_2394_, lean_object* v_x_2395_){
_start:
{
uint8_t v___y_6697__boxed_2396_; uint8_t v_suppressElabErrors_boxed_2397_; uint8_t v_res_2398_; lean_object* v_r_2399_; 
v___y_6697__boxed_2396_ = lean_unbox(v___y_2393_);
v_suppressElabErrors_boxed_2397_ = lean_unbox(v_suppressElabErrors_2394_);
v_res_2398_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v___y_6697__boxed_2396_, v_suppressElabErrors_boxed_2397_, v_x_2395_);
lean_dec(v_x_2395_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2400_, lean_object* v_msgData_2401_, uint8_t v_severity_2402_, uint8_t v_isSilent_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___y_2410_; uint8_t v___y_2411_; lean_object* v___y_2412_; uint8_t v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2446_; uint8_t v___y_2447_; uint8_t v___y_2448_; lean_object* v___y_2449_; uint8_t v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2471_; uint8_t v___y_2472_; lean_object* v___y_2473_; uint8_t v___y_2474_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2482_; uint8_t v___y_2483_; uint8_t v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; uint8_t v___y_2488_; uint8_t v___x_2493_; lean_object* v___y_2495_; uint8_t v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; uint8_t v___y_2500_; uint8_t v___y_2501_; uint8_t v___y_2503_; uint8_t v___x_2518_; 
v___x_2493_ = 2;
v___x_2518_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2402_, v___x_2493_);
if (v___x_2518_ == 0)
{
v___y_2503_ = v___x_2518_;
goto v___jp_2502_;
}
else
{
uint8_t v___x_2519_; 
lean_inc_ref(v_msgData_2401_);
v___x_2519_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2401_);
v___y_2503_ = v___x_2519_;
goto v___jp_2502_;
}
v___jp_2409_:
{
lean_object* v___x_2419_; lean_object* v_currNamespace_2420_; lean_object* v_openDecls_2421_; lean_object* v_env_2422_; lean_object* v_nextMacroScope_2423_; lean_object* v_ngen_2424_; lean_object* v_auxDeclNGen_2425_; lean_object* v_traceState_2426_; lean_object* v_cache_2427_; lean_object* v_messages_2428_; lean_object* v_infoState_2429_; lean_object* v_snapshotTasks_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2444_; 
v___x_2419_ = lean_st_ref_take(v___y_2418_);
v_currNamespace_2420_ = lean_ctor_get(v___y_2417_, 6);
v_openDecls_2421_ = lean_ctor_get(v___y_2417_, 7);
v_env_2422_ = lean_ctor_get(v___x_2419_, 0);
v_nextMacroScope_2423_ = lean_ctor_get(v___x_2419_, 1);
v_ngen_2424_ = lean_ctor_get(v___x_2419_, 2);
v_auxDeclNGen_2425_ = lean_ctor_get(v___x_2419_, 3);
v_traceState_2426_ = lean_ctor_get(v___x_2419_, 4);
v_cache_2427_ = lean_ctor_get(v___x_2419_, 5);
v_messages_2428_ = lean_ctor_get(v___x_2419_, 6);
v_infoState_2429_ = lean_ctor_get(v___x_2419_, 7);
v_snapshotTasks_2430_ = lean_ctor_get(v___x_2419_, 8);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2432_ = v___x_2419_;
v_isShared_2433_ = v_isSharedCheck_2444_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_snapshotTasks_2430_);
lean_inc(v_infoState_2429_);
lean_inc(v_messages_2428_);
lean_inc(v_cache_2427_);
lean_inc(v_traceState_2426_);
lean_inc(v_auxDeclNGen_2425_);
lean_inc(v_ngen_2424_);
lean_inc(v_nextMacroScope_2423_);
lean_inc(v_env_2422_);
lean_dec(v___x_2419_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2444_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
lean_inc(v_openDecls_2421_);
lean_inc(v_currNamespace_2420_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_currNamespace_2420_);
lean_ctor_set(v___x_2434_, 1, v_openDecls_2421_);
v___x_2435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v___y_2414_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v___y_2415_);
v___x_2436_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2436_, 0, v___y_2415_);
lean_ctor_set(v___x_2436_, 1, v___y_2416_);
lean_ctor_set(v___x_2436_, 2, v___y_2412_);
lean_ctor_set(v___x_2436_, 3, v___y_2410_);
lean_ctor_set(v___x_2436_, 4, v___x_2435_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*5, v___y_2411_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*5 + 1, v___y_2413_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*5 + 2, v_isSilent_2403_);
v___x_2437_ = l_Lean_MessageLog_add(v___x_2436_, v_messages_2428_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 6, v___x_2437_);
v___x_2439_ = v___x_2432_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_env_2422_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_nextMacroScope_2423_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_ngen_2424_);
lean_ctor_set(v_reuseFailAlloc_2443_, 3, v_auxDeclNGen_2425_);
lean_ctor_set(v_reuseFailAlloc_2443_, 4, v_traceState_2426_);
lean_ctor_set(v_reuseFailAlloc_2443_, 5, v_cache_2427_);
lean_ctor_set(v_reuseFailAlloc_2443_, 6, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2443_, 7, v_infoState_2429_);
lean_ctor_set(v_reuseFailAlloc_2443_, 8, v_snapshotTasks_2430_);
v___x_2439_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = lean_st_ref_set(v___y_2418_, v___x_2439_);
v___x_2441_ = lean_box(0);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
}
v___jp_2445_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2469_; 
v___x_2454_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2401_);
v___x_2455_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_2454_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2469_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2469_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_inc_ref_n(v___y_2449_, 2);
v___x_2460_ = l_Lean_FileMap_toPosition(v___y_2449_, v___y_2452_);
lean_dec(v___y_2452_);
v___x_2461_ = l_Lean_FileMap_toPosition(v___y_2449_, v___y_2453_);
lean_dec(v___y_2453_);
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
v___x_2463_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
if (v___y_2448_ == 0)
{
lean_del_object(v___x_2458_);
lean_dec_ref(v___y_2446_);
v___y_2410_ = v___x_2463_;
v___y_2411_ = v___y_2447_;
v___y_2412_ = v___x_2462_;
v___y_2413_ = v___y_2450_;
v___y_2414_ = v_a_2456_;
v___y_2415_ = v___y_2451_;
v___y_2416_ = v___x_2460_;
v___y_2417_ = v___y_2406_;
v___y_2418_ = v___y_2407_;
goto v___jp_2409_;
}
else
{
uint8_t v___x_2464_; 
lean_inc(v_a_2456_);
v___x_2464_ = l_Lean_MessageData_hasTag(v___y_2446_, v_a_2456_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_dec_ref_known(v___x_2462_, 1);
lean_dec_ref(v___x_2460_);
lean_dec(v_a_2456_);
v___x_2465_ = lean_box(0);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2465_);
v___x_2467_ = v___x_2458_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
else
{
lean_del_object(v___x_2458_);
v___y_2410_ = v___x_2463_;
v___y_2411_ = v___y_2447_;
v___y_2412_ = v___x_2462_;
v___y_2413_ = v___y_2450_;
v___y_2414_ = v_a_2456_;
v___y_2415_ = v___y_2451_;
v___y_2416_ = v___x_2460_;
v___y_2417_ = v___y_2406_;
v___y_2418_ = v___y_2407_;
goto v___jp_2409_;
}
}
}
}
v___jp_2470_:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Syntax_getTailPos_x3f(v___y_2473_, v___y_2472_);
lean_dec(v___y_2473_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_inc(v___y_2478_);
v___y_2446_ = v___y_2471_;
v___y_2447_ = v___y_2472_;
v___y_2448_ = v___y_2474_;
v___y_2449_ = v___y_2475_;
v___y_2450_ = v___y_2476_;
v___y_2451_ = v___y_2477_;
v___y_2452_ = v___y_2478_;
v___y_2453_ = v___y_2478_;
goto v___jp_2445_;
}
else
{
lean_object* v_val_2480_; 
v_val_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v___y_2446_ = v___y_2471_;
v___y_2447_ = v___y_2472_;
v___y_2448_ = v___y_2474_;
v___y_2449_ = v___y_2475_;
v___y_2450_ = v___y_2476_;
v___y_2451_ = v___y_2477_;
v___y_2452_ = v___y_2478_;
v___y_2453_ = v_val_2480_;
goto v___jp_2445_;
}
}
v___jp_2481_:
{
lean_object* v_ref_2489_; lean_object* v___x_2490_; 
v_ref_2489_ = l_Lean_replaceRef(v_ref_2400_, v___y_2485_);
v___x_2490_ = l_Lean_Syntax_getPos_x3f(v_ref_2489_, v___y_2483_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_unsigned_to_nat(0u);
v___y_2471_ = v___y_2482_;
v___y_2472_ = v___y_2483_;
v___y_2473_ = v_ref_2489_;
v___y_2474_ = v___y_2484_;
v___y_2475_ = v___y_2486_;
v___y_2476_ = v___y_2488_;
v___y_2477_ = v___y_2487_;
v___y_2478_ = v___x_2491_;
goto v___jp_2470_;
}
else
{
lean_object* v_val_2492_; 
v_val_2492_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_val_2492_);
lean_dec_ref_known(v___x_2490_, 1);
v___y_2471_ = v___y_2482_;
v___y_2472_ = v___y_2483_;
v___y_2473_ = v_ref_2489_;
v___y_2474_ = v___y_2484_;
v___y_2475_ = v___y_2486_;
v___y_2476_ = v___y_2488_;
v___y_2477_ = v___y_2487_;
v___y_2478_ = v_val_2492_;
goto v___jp_2470_;
}
}
v___jp_2494_:
{
if (v___y_2501_ == 0)
{
v___y_2482_ = v___y_2495_;
v___y_2483_ = v___y_2500_;
v___y_2484_ = v___y_2496_;
v___y_2485_ = v___y_2497_;
v___y_2486_ = v___y_2498_;
v___y_2487_ = v___y_2499_;
v___y_2488_ = v_severity_2402_;
goto v___jp_2481_;
}
else
{
v___y_2482_ = v___y_2495_;
v___y_2483_ = v___y_2500_;
v___y_2484_ = v___y_2496_;
v___y_2485_ = v___y_2497_;
v___y_2486_ = v___y_2498_;
v___y_2487_ = v___y_2499_;
v___y_2488_ = v___x_2493_;
goto v___jp_2481_;
}
}
v___jp_2502_:
{
if (v___y_2503_ == 0)
{
lean_object* v_fileName_2504_; lean_object* v_fileMap_2505_; lean_object* v_options_2506_; lean_object* v_ref_2507_; uint8_t v_suppressElabErrors_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___f_2511_; uint8_t v___x_2512_; uint8_t v___x_2513_; 
v_fileName_2504_ = lean_ctor_get(v___y_2406_, 0);
v_fileMap_2505_ = lean_ctor_get(v___y_2406_, 1);
v_options_2506_ = lean_ctor_get(v___y_2406_, 2);
v_ref_2507_ = lean_ctor_get(v___y_2406_, 5);
v_suppressElabErrors_2508_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*14 + 1);
v___x_2509_ = lean_box(v___y_2503_);
v___x_2510_ = lean_box(v_suppressElabErrors_2508_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2511_, 0, v___x_2509_);
lean_closure_set(v___f_2511_, 1, v___x_2510_);
v___x_2512_ = 1;
v___x_2513_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2402_, v___x_2512_);
if (v___x_2513_ == 0)
{
v___y_2495_ = v___f_2511_;
v___y_2496_ = v_suppressElabErrors_2508_;
v___y_2497_ = v_ref_2507_;
v___y_2498_ = v_fileMap_2505_;
v___y_2499_ = v_fileName_2504_;
v___y_2500_ = v___y_2503_;
v___y_2501_ = v___x_2513_;
goto v___jp_2494_;
}
else
{
lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = l_Lean_warningAsError;
v___x_2515_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_2506_, v___x_2514_);
v___y_2495_ = v___f_2511_;
v___y_2496_ = v_suppressElabErrors_2508_;
v___y_2497_ = v_ref_2507_;
v___y_2498_ = v_fileMap_2505_;
v___y_2499_ = v_fileName_2504_;
v___y_2500_ = v___y_2503_;
v___y_2501_ = v___x_2515_;
goto v___jp_2494_;
}
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_dec_ref(v_msgData_2401_);
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2520_, lean_object* v_msgData_2521_, lean_object* v_severity_2522_, lean_object* v_isSilent_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
uint8_t v_severity_boxed_2529_; uint8_t v_isSilent_boxed_2530_; lean_object* v_res_2531_; 
v_severity_boxed_2529_ = lean_unbox(v_severity_2522_);
v_isSilent_boxed_2530_ = lean_unbox(v_isSilent_2523_);
v_res_2531_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2520_, v_msgData_2521_, v_severity_boxed_2529_, v_isSilent_boxed_2530_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v_ref_2520_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object* v_msgData_2532_, uint8_t v_severity_2533_, uint8_t v_isSilent_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_ref_2542_; lean_object* v___x_2543_; 
v_ref_2542_ = lean_ctor_get(v___y_2539_, 5);
v___x_2543_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2542_, v_msgData_2532_, v_severity_2533_, v_isSilent_2534_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2544_, lean_object* v_severity_2545_, lean_object* v_isSilent_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
uint8_t v_severity_boxed_2554_; uint8_t v_isSilent_boxed_2555_; lean_object* v_res_2556_; 
v_severity_boxed_2554_ = lean_unbox(v_severity_2545_);
v_isSilent_boxed_2555_ = lean_unbox(v_isSilent_2546_);
v_res_2556_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2544_, v_severity_boxed_2554_, v_isSilent_boxed_2555_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object* v_msgData_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
uint8_t v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = 2;
v___x_2566_ = 0;
v___x_2567_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2557_, v___x_2565_, v___x_2566_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1___boxed(lean_object* v_msgData_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v_msgData_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object* v_ref_2577_, lean_object* v_msgData_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
uint8_t v___x_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = 2;
v___x_2587_ = 0;
v___x_2588_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2577_, v_msgData_2578_, v___x_2586_, v___x_2587_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object* v_ref_2589_, lean_object* v_msgData_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2589_, v_msgData_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v_ref_2589_);
return v_res_2598_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0));
v___x_2601_ = l_Lean_stringToMessageData(v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object* v_ex_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
if (lean_obj_tag(v_ex_2602_) == 0)
{
lean_object* v_ref_2610_; lean_object* v_msg_2611_; lean_object* v___x_2612_; 
v_ref_2610_ = lean_ctor_get(v_ex_2602_, 0);
lean_inc(v_ref_2610_);
v_msg_2611_ = lean_ctor_get(v_ex_2602_, 1);
lean_inc_ref(v_msg_2611_);
lean_dec_ref_known(v_ex_2602_, 2);
v___x_2612_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2610_, v_msg_2611_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v_ref_2610_);
return v___x_2612_;
}
else
{
lean_object* v_id_2613_; uint8_t v___y_2615_; uint8_t v___x_2637_; 
v_id_2613_ = lean_ctor_get(v_ex_2602_, 0);
lean_inc(v_id_2613_);
v___x_2637_ = l_Lean_Elab_isAbortExceptionId(v_id_2613_);
if (v___x_2637_ == 0)
{
uint8_t v___x_2638_; 
v___x_2638_ = l_Lean_Exception_isInterrupt(v_ex_2602_);
lean_dec_ref_known(v_ex_2602_, 2);
v___y_2615_ = v___x_2638_;
goto v___jp_2614_;
}
else
{
lean_dec_ref_known(v_ex_2602_, 2);
v___y_2615_ = v___x_2637_;
goto v___jp_2614_;
}
v___jp_2614_:
{
if (v___y_2615_ == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_InternalExceptionId_getName(v_id_2613_);
lean_dec(v_id_2613_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
v___x_2619_ = l_Lean_MessageData_ofName(v_a_2617_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_2620_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2621_;
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2634_; 
v_a_2622_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2624_ = v___x_2616_;
v_isShared_2625_ = v_isSharedCheck_2634_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2616_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2634_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_ref_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v_ref_2626_ = lean_ctor_get(v___y_2607_, 5);
v___x_2627_ = lean_io_error_to_string(v_a_2622_);
v___x_2628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v___x_2629_ = l_Lean_MessageData_ofFormat(v___x_2628_);
lean_inc(v_ref_2626_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_ref_2626_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2630_);
v___x_2632_ = v___x_2624_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
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
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec(v_id_2613_);
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object* v_ex_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object* v_a_2648_, lean_object* v_config_2649_, lean_object* v_____r_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_2648_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2658_, 0);
lean_dec(v_unused_2667_);
v___x_2660_ = v___x_2658_;
v_isShared_2661_ = v_isSharedCheck_2666_;
goto v_resetjp_2659_;
}
else
{
lean_dec(v___x_2658_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2666_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_config_2649_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2662_);
v___x_2664_ = v___x_2660_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
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
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_config_2649_);
v_a_2668_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2658_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2658_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object* v_a_2676_, lean_object* v_config_2677_, lean_object* v_____r_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2676_, v_config_2677_, v_____r_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object* v___f_2687_, lean_object* v_x_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_box(0);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___y_2690_);
lean_inc_ref(v___y_2689_);
v___x_2697_ = lean_apply_8(v___f_2687_, v___x_2696_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, lean_box(0));
return v___x_2697_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object* v_eval_2708_, lean_object* v_config_2709_, lean_object* v_item_2710_, uint8_t v_logExceptions_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object* v_eval_2761_, lean_object* v_config_2762_, lean_object* v_item_2763_, lean_object* v_logExceptions_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
uint8_t v_logExceptions_boxed_2772_; lean_object* v_res_2773_; 
v_logExceptions_boxed_2772_ = lean_unbox(v_logExceptions_2764_);
v_res_2773_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2761_, v_config_2762_, v_item_2763_, v_logExceptions_boxed_2772_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object* v_00_u03b1_2774_, lean_object* v_eval_2775_, lean_object* v_config_2776_, lean_object* v_item_2777_, uint8_t v_logExceptions_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2775_, v_config_2776_, v_item_2777_, v_logExceptions_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_eval_2788_, lean_object* v_config_2789_, lean_object* v_item_2790_, lean_object* v_logExceptions_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
uint8_t v_logExceptions_boxed_2799_; lean_object* v_res_2800_; 
v_logExceptions_boxed_2799_ = lean_unbox(v_logExceptions_2791_);
v_res_2800_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(v_00_u03b1_2787_, v_eval_2788_, v_config_2789_, v_item_2790_, v_logExceptions_boxed_2799_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object* v_ref_2801_, lean_object* v_msgData_2802_, uint8_t v_severity_2803_, uint8_t v_isSilent_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2801_, v_msgData_2802_, v_severity_2803_, v_isSilent_2804_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2813_, lean_object* v_msgData_2814_, lean_object* v_severity_2815_, lean_object* v_isSilent_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
uint8_t v_severity_boxed_2824_; uint8_t v_isSilent_boxed_2825_; lean_object* v_res_2826_; 
v_severity_boxed_2824_ = lean_unbox(v_severity_2815_);
v_isSilent_boxed_2825_ = lean_unbox(v_isSilent_2816_);
v_res_2826_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2813_, v_msgData_2814_, v_severity_boxed_2824_, v_isSilent_boxed_2825_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v_ref_2813_);
return v_res_2826_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = lean_box(0);
v___x_2828_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2827_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg(){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
v___x_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object* v_00_u03b1_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object* v_00_u03b1_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
return v_res_2852_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = l_Lean_Level_ofNat(v___x_2856_);
return v___x_2857_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2);
v___x_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v___x_2858_);
return v___x_2860_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3);
v___x_2862_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1));
v___x_2863_ = l_Lean_Expr_const___override(v___x_2862_, v___x_2861_);
return v___x_2863_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_box(0);
v___x_2868_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6));
v___x_2869_ = l_Lean_Expr_const___override(v___x_2868_, v___x_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object* v_cfg_2873_, lean_object* v_cfgItem_2874_, lean_object* v_cfgType_x3f_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; 
if (lean_obj_tag(v_cfgType_x3f_2875_) == 1)
{
lean_object* v_val_2893_; lean_object* v___x_2894_; lean_object* v_infoState_2895_; uint8_t v_enabled_2896_; 
v_val_2893_ = lean_ctor_get(v_cfgType_x3f_2875_, 0);
lean_inc(v_val_2893_);
lean_dec_ref_known(v_cfgType_x3f_2875_, 1);
v___x_2894_ = lean_st_ref_get(v_a_2881_);
v_infoState_2895_ = lean_ctor_get(v___x_2894_, 7);
lean_inc_ref(v_infoState_2895_);
lean_dec(v___x_2894_);
v_enabled_2896_ = lean_ctor_get_uint8(v_infoState_2895_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2895_);
if (v_enabled_2896_ == 0)
{
lean_dec(v_val_2893_);
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
v___y_2886_ = v_a_2878_;
v___y_2887_ = v_a_2879_;
v___y_2888_ = v_a_2880_;
v___y_2889_ = v_a_2881_;
goto v___jp_2883_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___y_2900_; uint8_t v___x_2912_; 
v___x_2897_ = lean_unsigned_to_nat(0u);
v___x_2898_ = l_Lean_Syntax_getArg(v_cfgItem_2874_, v___x_2897_);
v___x_2912_ = l_Lean_Syntax_isAtom(v___x_2898_);
if (v___x_2912_ == 0)
{
v___y_2900_ = v___x_2912_;
goto v___jp_2899_;
}
else
{
lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = l_Lean_Syntax_getArg(v_cfgItem_2874_, v___x_2913_);
v___x_2915_ = l_Lean_Syntax_isMissing(v___x_2914_);
lean_dec(v___x_2914_);
v___y_2900_ = v___x_2915_;
goto v___jp_2899_;
}
v___jp_2899_:
{
if (v___y_2900_ == 0)
{
lean_dec(v___x_2898_);
lean_dec(v_val_2893_);
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
v___y_2886_ = v_a_2878_;
v___y_2887_ = v_a_2879_;
v___y_2888_ = v_a_2880_;
v___y_2889_ = v_a_2881_;
goto v___jp_2883_;
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2901_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
v___x_2902_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
v___x_2903_ = l_Lean_mkAppB(v___x_2901_, v_val_2893_, v___x_2902_);
v___x_2904_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9));
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
lean_ctor_set(v___x_2905_, 1, v___x_2898_);
v___x_2906_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2);
v___x_2907_ = lean_box(0);
v___x_2908_ = 0;
v___x_2909_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2909_, 0, v___x_2905_);
lean_ctor_set(v___x_2909_, 1, v___x_2906_);
lean_ctor_set(v___x_2909_, 2, v___x_2907_);
lean_ctor_set(v___x_2909_, 3, v___x_2903_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*4, v___x_2908_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*4 + 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2907_);
v___x_2911_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2910_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
lean_dec_ref(v___x_2911_);
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
v___y_2886_ = v_a_2878_;
v___y_2887_ = v_a_2879_;
v___y_2888_ = v_a_2880_;
v___y_2889_ = v_a_2881_;
goto v___jp_2883_;
}
}
}
}
else
{
lean_dec(v_cfgType_x3f_2875_);
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
v___y_2886_ = v_a_2878_;
v___y_2887_ = v_a_2879_;
v___y_2888_ = v_a_2880_;
v___y_2889_ = v_a_2881_;
goto v___jp_2883_;
}
v___jp_2883_:
{
uint8_t v___x_2890_; 
v___x_2890_ = l_Lean_Syntax_hasMissing(v_cfgItem_2874_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
lean_dec(v_cfg_2873_);
v___x_2891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_cfg_2873_);
return v___x_2892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object* v_cfg_2916_, lean_object* v_cfgItem_2917_, lean_object* v_cfgType_x3f_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2916_, v_cfgItem_2917_, v_cfgType_x3f_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_cfgItem_2917_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object* v_00_u03b1_2927_, lean_object* v_cfg_2928_, lean_object* v_cfgItem_2929_, lean_object* v_cfgType_x3f_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2928_, v_cfgItem_2929_, v_cfgType_x3f_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object* v_00_u03b1_2939_, lean_object* v_cfg_2940_, lean_object* v_cfgItem_2941_, lean_object* v_cfgType_x3f_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(v_00_u03b1_2939_, v_cfg_2940_, v_cfgItem_2941_, v_cfgType_x3f_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_cfgItem_2941_);
return v_res_2950_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_s_2951_, lean_object* v_a_2952_, uint8_t v_b_2953_){
_start:
{
lean_object* v_str_2954_; lean_object* v_startInclusive_2955_; lean_object* v_endExclusive_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v_str_2954_ = lean_ctor_get(v_s_2951_, 0);
v_startInclusive_2955_ = lean_ctor_get(v_s_2951_, 1);
v_endExclusive_2956_ = lean_ctor_get(v_s_2951_, 2);
v___x_2957_ = lean_nat_sub(v_endExclusive_2956_, v_startInclusive_2955_);
v___x_2958_ = lean_nat_dec_eq(v_a_2952_, v___x_2957_);
lean_dec(v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; uint32_t v___x_2960_; uint32_t v___x_2961_; uint8_t v___x_2962_; 
v___x_2959_ = lean_nat_add(v_startInclusive_2955_, v_a_2952_);
lean_dec(v_a_2952_);
v___x_2960_ = lean_string_utf8_get_fast(v_str_2954_, v___x_2959_);
v___x_2961_ = 46;
v___x_2962_ = lean_uint32_dec_eq(v___x_2960_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = lean_string_utf8_next_fast(v_str_2954_, v___x_2959_);
lean_dec(v___x_2959_);
v___x_2964_ = lean_nat_sub(v___x_2963_, v_startInclusive_2955_);
v_a_2952_ = v___x_2964_;
v_b_2953_ = v___x_2962_;
goto _start;
}
else
{
lean_dec(v___x_2959_);
return v___x_2962_;
}
}
else
{
lean_dec(v_a_2952_);
return v_b_2953_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_s_2966_, lean_object* v_a_2967_, lean_object* v_b_2968_){
_start:
{
uint8_t v_b_boxed_2969_; uint8_t v_res_2970_; lean_object* v_r_2971_; 
v_b_boxed_2969_ = lean_unbox(v_b_2968_);
v_res_2970_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2966_, v_a_2967_, v_b_boxed_2969_);
lean_dec_ref(v_s_2966_);
v_r_2971_ = lean_box(v_res_2970_);
return v_r_2971_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object* v_s_2972_){
_start:
{
lean_object* v_searcher_2973_; uint8_t v___x_2974_; uint8_t v___x_2975_; 
v_searcher_2973_ = lean_unsigned_to_nat(0u);
v___x_2974_ = 0;
v___x_2975_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2972_, v_searcher_2973_, v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object* v_s_2976_){
_start:
{
uint8_t v_res_2977_; lean_object* v_r_2978_; 
v_res_2977_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2976_);
lean_dec_ref(v_s_2976_);
v_r_2978_ = lean_box(v_res_2977_);
return v_r_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object* v_si_2979_, lean_object* v_val_2980_){
_start:
{
lean_object* v___y_2982_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2988_ = lean_unsigned_to_nat(0u);
v___x_2989_ = lean_string_utf8_byte_size(v_val_2980_);
lean_inc_ref(v_val_2980_);
v___x_2990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2990_, 0, v_val_2980_);
lean_ctor_set(v___x_2990_, 1, v___x_2988_);
lean_ctor_set(v___x_2990_, 2, v___x_2989_);
v___x_2991_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_2990_);
lean_dec_ref_known(v___x_2990_, 3);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_box(0);
lean_inc_ref(v_val_2980_);
v___x_2993_ = l_Lean_Name_str___override(v___x_2992_, v_val_2980_);
v___y_2982_ = v___x_2993_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_2994_; 
lean_inc_ref(v_val_2980_);
v___x_2994_ = l_String_toName(v_val_2980_);
v___y_2982_ = v___x_2994_;
goto v___jp_2981_;
}
v___jp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = lean_string_utf8_byte_size(v_val_2980_);
v___x_2985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2985_, 0, v_val_2980_);
lean_ctor_set(v___x_2985_, 1, v___x_2983_);
lean_ctor_set(v___x_2985_, 2, v___x_2984_);
v___x_2986_ = lean_box(0);
v___x_2987_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2987_, 0, v_si_2979_);
lean_ctor_set(v___x_2987_, 1, v___x_2985_);
lean_ctor_set(v___x_2987_, 2, v___y_2982_);
lean_ctor_set(v___x_2987_, 3, v___x_2986_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object* v_eval_2996_, uint8_t v_logExceptions_2997_, lean_object* v_onErr_2998_, lean_object* v_init_2999_, lean_object* v_cfgs_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = lean_array_get_size(v_cfgs_3000_);
v___x_3010_ = lean_nat_dec_lt(v___x_3008_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
lean_dec_ref(v_onErr_2998_);
lean_dec_ref(v_eval_2996_);
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_init_2999_);
return v___x_3011_;
}
else
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_nat_dec_le(v___x_3009_, v___x_3009_);
if (v___x_3012_ == 0)
{
if (v___x_3010_ == 0)
{
lean_object* v___x_3013_; 
lean_dec_ref(v_onErr_2998_);
lean_dec_ref(v_eval_2996_);
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_init_2999_);
return v___x_3013_;
}
else
{
size_t v___x_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((size_t)0ULL);
v___x_3015_ = lean_usize_of_nat(v___x_3009_);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_2996_, v_logExceptions_2997_, v_onErr_2998_, v_cfgs_3000_, v___x_3014_, v___x_3015_, v_init_2999_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
return v___x_3016_;
}
}
else
{
size_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = ((size_t)0ULL);
v___x_3018_ = lean_usize_of_nat(v___x_3009_);
v___x_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_2996_, v_logExceptions_2997_, v_onErr_2998_, v_cfgs_3000_, v___x_3017_, v___x_3018_, v_init_2999_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
return v___x_3019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object* v_eval_3020_, uint8_t v_logExceptions_3021_, lean_object* v_onErr_3022_, lean_object* v_init_3023_, lean_object* v_cfg_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_3024_);
v___x_3064_ = l_Lean_Syntax_isOfKind(v_cfg_3024_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3065_ = l_Lean_Syntax_getNumArgs(v_cfg_3024_);
v___x_3066_ = lean_unsigned_to_nat(1u);
v___x_3067_ = lean_nat_dec_eq(v___x_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v_atomAsIdent_3068_; uint8_t v___x_3069_; 
v_atomAsIdent_3068_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0));
v___x_3069_ = lean_nat_dec_le(v___x_3066_, v___x_3065_);
if (v___x_3069_ == 0)
{
lean_dec(v___x_3065_);
if (lean_obj_tag(v_cfg_3024_) == 2)
{
lean_object* v_info_3070_; lean_object* v_val_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec_ref(v_onErr_3022_);
v_info_3070_ = lean_ctor_get(v_cfg_3024_, 0);
v_val_3071_ = lean_ctor_get(v_cfg_3024_, 1);
lean_inc_ref(v_val_3071_);
lean_inc(v_info_3070_);
v___x_3072_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_3070_, v_val_3071_);
v___x_3073_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_3074_ = l_Lean_mkCIdentFrom(v_cfg_3024_, v___x_3073_, v___x_3067_);
v___x_3075_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_3076_ = l_Lean_TSyntax_getId(v___x_3072_);
v___x_3077_ = l_Lean_Name_eraseMacroScopes(v___x_3076_);
lean_dec(v___x_3076_);
v___x_3078_ = lean_box(0);
lean_inc(v___x_3072_);
v___x_3079_ = l_Lean_Syntax_identComponents(v___x_3072_, v___x_3078_);
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3081_, 0, v_cfg_3024_);
lean_ctor_set(v___x_3081_, 1, v___x_3072_);
lean_ctor_set(v___x_3081_, 2, v___x_3074_);
lean_ctor_set(v___x_3081_, 3, v___x_3075_);
lean_ctor_set(v___x_3081_, 4, v___x_3077_);
lean_ctor_set(v___x_3081_, 5, v___x_3079_);
lean_ctor_set(v___x_3081_, 6, v___x_3080_);
v___x_3082_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3020_, v_init_3023_, v___x_3081_, v_logExceptions_3021_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v___x_3082_;
}
else
{
lean_dec_ref(v_eval_3020_);
goto v___jp_3043_;
}
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = l_Lean_Syntax_getArg(v_cfg_3024_, v___x_3083_);
if (lean_obj_tag(v___x_3084_) == 2)
{
lean_object* v_val_3085_; lean_object* v___y_3087_; uint8_t v_val_3088_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_val_3085_ = lean_ctor_get(v___x_3084_, 1);
lean_inc_ref(v_val_3085_);
v___x_3099_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_3100_ = lean_string_dec_eq(v_val_3085_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_3102_ = lean_string_dec_eq(v_val_3085_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; uint8_t v___x_3104_; 
lean_dec_ref_known(v___x_3084_, 2);
v___x_3103_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_3104_ = lean_string_dec_eq(v_val_3085_, v___x_3103_);
lean_dec_ref(v_val_3085_);
if (v___x_3104_ == 0)
{
lean_dec(v___x_3065_);
lean_dec_ref(v_eval_3020_);
goto v___jp_3043_;
}
else
{
lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3105_ = lean_unsigned_to_nat(5u);
v___x_3106_ = lean_nat_dec_le(v___x_3065_, v___x_3105_);
lean_dec(v___x_3065_);
if (v___x_3106_ == 0)
{
lean_dec_ref(v_eval_3020_);
goto v___jp_3043_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = l_Lean_Syntax_getArg(v_cfg_3024_, v___x_3066_);
v___x_3108_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_3068_, v___x_3107_);
if (lean_obj_tag(v___x_3108_) == 1)
{
lean_object* v_val_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec_ref(v_onErr_3022_);
v_val_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc_n(v_val_3109_, 2);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = lean_unsigned_to_nat(3u);
v___x_3111_ = l_Lean_Syntax_getArg(v_cfg_3024_, v___x_3110_);
v___x_3112_ = lean_box(0);
v___x_3113_ = l_Lean_TSyntax_getId(v_val_3109_);
v___x_3114_ = l_Lean_Name_eraseMacroScopes(v___x_3113_);
lean_dec(v___x_3113_);
v___x_3115_ = l_Lean_Syntax_identComponents(v_val_3109_, v___x_3112_);
v___x_3116_ = lean_box(0);
v___x_3117_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3117_, 0, v_cfg_3024_);
lean_ctor_set(v___x_3117_, 1, v_val_3109_);
lean_ctor_set(v___x_3117_, 2, v___x_3111_);
lean_ctor_set(v___x_3117_, 3, v___x_3112_);
lean_ctor_set(v___x_3117_, 4, v___x_3114_);
lean_ctor_set(v___x_3117_, 5, v___x_3115_);
lean_ctor_set(v___x_3117_, 6, v___x_3116_);
v___x_3118_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3020_, v_init_3023_, v___x_3117_, v_logExceptions_3021_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v___x_3118_;
}
else
{
lean_dec(v___x_3108_);
lean_dec_ref(v_eval_3020_);
goto v___jp_3043_;
}
}
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec_ref(v_val_3085_);
v___x_3119_ = lean_box(v___x_3067_);
v___x_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
v___y_3087_ = v___x_3120_;
v_val_3088_ = v___x_3067_;
goto v___jp_3086_;
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_dec_ref(v_val_3085_);
v___x_3121_ = lean_box(v___x_3100_);
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
v___y_3087_ = v___x_3122_;
v_val_3088_ = v___x_3100_;
goto v___jp_3086_;
}
v___jp_3086_:
{
lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = lean_unsigned_to_nat(2u);
v___x_3090_ = lean_nat_dec_eq(v___x_3065_, v___x_3089_);
lean_dec(v___x_3065_);
if (v___x_3090_ == 0)
{
lean_dec(v___y_3087_);
lean_dec_ref_known(v___x_3084_, 2);
lean_dec_ref(v_eval_3020_);
goto v___jp_3043_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = l_Lean_Syntax_getArg(v_cfg_3024_, v___x_3066_);
v___x_3092_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_3068_, v___x_3091_);
if (lean_obj_tag(v___x_3092_) == 1)
{
lean_dec_ref(v_onErr_3022_);
if (v_val_3088_ == 0)
{
lean_object* v_val_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_val_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_val_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_3095_ = l_Lean_mkCIdentFrom(v___x_3084_, v___x_3094_, v___x_3067_);
lean_dec_ref_known(v___x_3084_, 2);
v___y_3033_ = v___y_3087_;
v___y_3034_ = v_val_3093_;
v___y_3035_ = v___x_3095_;
goto v___jp_3032_;
}
else
{
lean_object* v_val_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_val_3096_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3097_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_3098_ = l_Lean_mkCIdentFrom(v___x_3084_, v___x_3097_, v___x_3067_);
lean_dec_ref_known(v___x_3084_, 2);
v___y_3033_ = v___y_3087_;
v___y_3034_ = v_val_3096_;
v___y_3035_ = v___x_3098_;
goto v___jp_3032_;
}
}
else
{
lean_dec(v___x_3092_);
lean_dec(v___y_3087_);
lean_dec_ref_known(v___x_3084_, 2);
lean_dec_ref(v_eval_3020_);
goto v___jp_3043_;
}
}
}
}
else
{
lean_dec(v___x_3084_);
lean_dec(v___x_3065_);
lean_dec_ref(v_eval_3020_);
goto v___jp_3043_;
}
}
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_dec(v___x_3065_);
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = l_Lean_Syntax_getArg(v_cfg_3024_, v___x_3123_);
lean_dec(v_cfg_3024_);
v_cfg_3024_ = v___x_3124_;
goto _start;
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = l_Lean_Syntax_getArgs(v_cfg_3024_);
lean_dec(v_cfg_3024_);
v___x_3127_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3020_, v_logExceptions_3021_, v_onErr_3022_, v_init_3023_, v___x_3126_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec_ref(v___x_3126_);
return v___x_3127_;
}
v___jp_3032_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3036_ = l_Lean_TSyntax_getId(v___y_3034_);
v___x_3037_ = l_Lean_Name_eraseMacroScopes(v___x_3036_);
lean_dec(v___x_3036_);
v___x_3038_ = lean_box(0);
lean_inc(v___y_3034_);
v___x_3039_ = l_Lean_Syntax_identComponents(v___y_3034_, v___x_3038_);
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3041_, 0, v_cfg_3024_);
lean_ctor_set(v___x_3041_, 1, v___y_3034_);
lean_ctor_set(v___x_3041_, 2, v___y_3035_);
lean_ctor_set(v___x_3041_, 3, v___y_3033_);
lean_ctor_set(v___x_3041_, 4, v___x_3037_);
lean_ctor_set(v___x_3041_, 5, v___x_3039_);
lean_ctor_set(v___x_3041_, 6, v___x_3040_);
v___x_3042_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3020_, v_init_3023_, v___x_3041_, v_logExceptions_3021_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v___x_3042_;
}
v___jp_3043_:
{
lean_object* v_fileName_3044_; lean_object* v_fileMap_3045_; lean_object* v_options_3046_; lean_object* v_currRecDepth_3047_; lean_object* v_maxRecDepth_3048_; lean_object* v_ref_3049_; lean_object* v_currNamespace_3050_; lean_object* v_openDecls_3051_; lean_object* v_initHeartbeats_3052_; lean_object* v_maxHeartbeats_3053_; lean_object* v_quotContext_3054_; lean_object* v_currMacroScope_3055_; uint8_t v_diag_3056_; lean_object* v_cancelTk_x3f_3057_; uint8_t v_suppressElabErrors_3058_; lean_object* v_inheritedTraceOptions_3059_; lean_object* v_ref_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_fileName_3044_ = lean_ctor_get(v___y_3029_, 0);
v_fileMap_3045_ = lean_ctor_get(v___y_3029_, 1);
v_options_3046_ = lean_ctor_get(v___y_3029_, 2);
v_currRecDepth_3047_ = lean_ctor_get(v___y_3029_, 3);
v_maxRecDepth_3048_ = lean_ctor_get(v___y_3029_, 4);
v_ref_3049_ = lean_ctor_get(v___y_3029_, 5);
v_currNamespace_3050_ = lean_ctor_get(v___y_3029_, 6);
v_openDecls_3051_ = lean_ctor_get(v___y_3029_, 7);
v_initHeartbeats_3052_ = lean_ctor_get(v___y_3029_, 8);
v_maxHeartbeats_3053_ = lean_ctor_get(v___y_3029_, 9);
v_quotContext_3054_ = lean_ctor_get(v___y_3029_, 10);
v_currMacroScope_3055_ = lean_ctor_get(v___y_3029_, 11);
v_diag_3056_ = lean_ctor_get_uint8(v___y_3029_, sizeof(void*)*14);
v_cancelTk_x3f_3057_ = lean_ctor_get(v___y_3029_, 12);
v_suppressElabErrors_3058_ = lean_ctor_get_uint8(v___y_3029_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3059_ = lean_ctor_get(v___y_3029_, 13);
v_ref_3060_ = l_Lean_replaceRef(v_cfg_3024_, v_ref_3049_);
lean_inc_ref(v_inheritedTraceOptions_3059_);
lean_inc(v_cancelTk_x3f_3057_);
lean_inc(v_currMacroScope_3055_);
lean_inc(v_quotContext_3054_);
lean_inc(v_maxHeartbeats_3053_);
lean_inc(v_initHeartbeats_3052_);
lean_inc(v_openDecls_3051_);
lean_inc(v_currNamespace_3050_);
lean_inc(v_maxRecDepth_3048_);
lean_inc(v_currRecDepth_3047_);
lean_inc_ref(v_options_3046_);
lean_inc_ref(v_fileMap_3045_);
lean_inc_ref(v_fileName_3044_);
v___x_3061_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3061_, 0, v_fileName_3044_);
lean_ctor_set(v___x_3061_, 1, v_fileMap_3045_);
lean_ctor_set(v___x_3061_, 2, v_options_3046_);
lean_ctor_set(v___x_3061_, 3, v_currRecDepth_3047_);
lean_ctor_set(v___x_3061_, 4, v_maxRecDepth_3048_);
lean_ctor_set(v___x_3061_, 5, v_ref_3060_);
lean_ctor_set(v___x_3061_, 6, v_currNamespace_3050_);
lean_ctor_set(v___x_3061_, 7, v_openDecls_3051_);
lean_ctor_set(v___x_3061_, 8, v_initHeartbeats_3052_);
lean_ctor_set(v___x_3061_, 9, v_maxHeartbeats_3053_);
lean_ctor_set(v___x_3061_, 10, v_quotContext_3054_);
lean_ctor_set(v___x_3061_, 11, v_currMacroScope_3055_);
lean_ctor_set(v___x_3061_, 12, v_cancelTk_x3f_3057_);
lean_ctor_set(v___x_3061_, 13, v_inheritedTraceOptions_3059_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*14, v_diag_3056_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*14 + 1, v_suppressElabErrors_3058_);
lean_inc(v___y_3030_);
lean_inc(v___y_3028_);
lean_inc_ref(v___y_3027_);
lean_inc(v___y_3026_);
lean_inc_ref(v___y_3025_);
v___x_3062_ = lean_apply_9(v_onErr_3022_, v_init_3023_, v_cfg_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___x_3061_, v___y_3030_, lean_box(0));
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object* v_eval_3128_, uint8_t v_logExceptions_3129_, lean_object* v_onErr_3130_, lean_object* v_as_3131_, size_t v_i_3132_, size_t v_stop_3133_, lean_object* v_b_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
uint8_t v___x_3142_; 
v___x_3142_ = lean_usize_dec_eq(v_i_3132_, v_stop_3133_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_array_uget_borrowed(v_as_3131_, v_i_3132_);
lean_inc(v___x_3143_);
lean_inc_ref(v_onErr_3130_);
lean_inc_ref(v_eval_3128_);
v___x_3144_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3128_, v_logExceptions_3129_, v_onErr_3130_, v_b_3134_, v___x_3143_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; size_t v___x_3146_; size_t v___x_3147_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = ((size_t)1ULL);
v___x_3147_ = lean_usize_add(v_i_3132_, v___x_3146_);
v_i_3132_ = v___x_3147_;
v_b_3134_ = v_a_3145_;
goto _start;
}
else
{
lean_dec_ref(v_onErr_3130_);
lean_dec_ref(v_eval_3128_);
return v___x_3144_;
}
}
else
{
lean_object* v___x_3149_; 
lean_dec_ref(v_onErr_3130_);
lean_dec_ref(v_eval_3128_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_b_3134_);
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_eval_3150_, lean_object* v_logExceptions_3151_, lean_object* v_onErr_3152_, lean_object* v_as_3153_, lean_object* v_i_3154_, lean_object* v_stop_3155_, lean_object* v_b_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_logExceptions_boxed_3164_; size_t v_i_boxed_3165_; size_t v_stop_boxed_3166_; lean_object* v_res_3167_; 
v_logExceptions_boxed_3164_ = lean_unbox(v_logExceptions_3151_);
v_i_boxed_3165_ = lean_unbox_usize(v_i_3154_);
lean_dec(v_i_3154_);
v_stop_boxed_3166_ = lean_unbox_usize(v_stop_3155_);
lean_dec(v_stop_3155_);
v_res_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3150_, v_logExceptions_boxed_3164_, v_onErr_3152_, v_as_3153_, v_i_boxed_3165_, v_stop_boxed_3166_, v_b_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec_ref(v_as_3153_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object* v_eval_3168_, lean_object* v_logExceptions_3169_, lean_object* v_onErr_3170_, lean_object* v_init_3171_, lean_object* v_cfgs_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v_logExceptions_boxed_3180_; lean_object* v_res_3181_; 
v_logExceptions_boxed_3180_ = lean_unbox(v_logExceptions_3169_);
v_res_3181_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3168_, v_logExceptions_boxed_3180_, v_onErr_3170_, v_init_3171_, v_cfgs_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v_cfgs_3172_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object* v_eval_3182_, lean_object* v_logExceptions_3183_, lean_object* v_onErr_3184_, lean_object* v_init_3185_, lean_object* v_cfg_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_logExceptions_boxed_3194_; lean_object* v_res_3195_; 
v_logExceptions_boxed_3194_ = lean_unbox(v_logExceptions_3183_);
v_res_3195_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3182_, v_logExceptions_boxed_3194_, v_onErr_3184_, v_init_3185_, v_cfg_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object* v_eval_3196_, lean_object* v_init_3197_, lean_object* v_cfg_3198_, lean_object* v_onErr_3199_, uint8_t v_logExceptions_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3196_, v_logExceptions_3200_, v_onErr_3199_, v_init_3197_, v_cfg_3198_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object* v_eval_3209_, lean_object* v_init_3210_, lean_object* v_cfg_3211_, lean_object* v_onErr_3212_, lean_object* v_logExceptions_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
uint8_t v_logExceptions_boxed_3221_; lean_object* v_res_3222_; 
v_logExceptions_boxed_3221_ = lean_unbox(v_logExceptions_3213_);
v_res_3222_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3209_, v_init_3210_, v_cfg_3211_, v_onErr_3212_, v_logExceptions_boxed_3221_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object* v_00_u03b1_3223_, lean_object* v_eval_3224_, lean_object* v_init_3225_, lean_object* v_cfg_3226_, lean_object* v_onErr_3227_, uint8_t v_logExceptions_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3224_, v_logExceptions_3228_, v_onErr_3227_, v_init_3225_, v_cfg_3226_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object* v_00_u03b1_3237_, lean_object* v_eval_3238_, lean_object* v_init_3239_, lean_object* v_cfg_3240_, lean_object* v_onErr_3241_, lean_object* v_logExceptions_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
uint8_t v_logExceptions_boxed_3250_; lean_object* v_res_3251_; 
v_logExceptions_boxed_3250_ = lean_unbox(v_logExceptions_3242_);
v_res_3251_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(v_00_u03b1_3237_, v_eval_3238_, v_init_3239_, v_cfg_3240_, v_onErr_3241_, v_logExceptions_boxed_3250_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3243_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object* v_00_u03b1_3252_, lean_object* v_eval_3253_, uint8_t v_logExceptions_3254_, lean_object* v_onErr_3255_, lean_object* v_init_3256_, lean_object* v_cfg_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3253_, v_logExceptions_3254_, v_onErr_3255_, v_init_3256_, v_cfg_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
return v___x_3265_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object* v_00_u03b1_3281_, lean_object* v_eval_3282_, uint8_t v_logExceptions_3283_, lean_object* v_onErr_3284_, lean_object* v_init_3285_, lean_object* v_cfgs_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3282_, v_logExceptions_3283_, v_onErr_3284_, v_init_3285_, v_cfgs_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3295_, lean_object* v_eval_3296_, lean_object* v_logExceptions_3297_, lean_object* v_onErr_3298_, lean_object* v_init_3299_, lean_object* v_cfgs_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v_logExceptions_boxed_3308_; lean_object* v_res_3309_; 
v_logExceptions_boxed_3308_ = lean_unbox(v_logExceptions_3297_);
v_res_3309_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_3295_, v_eval_3296_, v_logExceptions_boxed_3308_, v_onErr_3298_, v_init_3299_, v_cfgs_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec_ref(v_cfgs_3300_);
return v_res_3309_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object* v_s_3310_, lean_object* v_inst_3311_, lean_object* v_R_3312_, lean_object* v_a_3313_, uint8_t v_b_3314_, lean_object* v_c_3315_){
_start:
{
uint8_t v___x_3316_; 
v___x_3316_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_3310_, v_a_3313_, v_b_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_s_3317_, lean_object* v_inst_3318_, lean_object* v_R_3319_, lean_object* v_a_3320_, lean_object* v_b_3321_, lean_object* v_c_3322_){
_start:
{
uint8_t v_b_boxed_3323_; uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_b_boxed_3323_ = lean_unbox(v_b_3321_);
v_res_3324_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3317_, v_inst_3318_, v_R_3319_, v_a_3320_, v_b_boxed_3323_, v_c_3322_);
lean_dec_ref(v_s_3317_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3326_, lean_object* v_eval_3327_, uint8_t v_logExceptions_3328_, lean_object* v_onErr_3329_, lean_object* v_as_3330_, size_t v_i_3331_, size_t v_stop_3332_, lean_object* v_b_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3327_, v_logExceptions_3328_, v_onErr_3329_, v_as_3330_, v_i_3331_, v_stop_3332_, v_b_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3342_, lean_object* v_eval_3343_, lean_object* v_logExceptions_3344_, lean_object* v_onErr_3345_, lean_object* v_as_3346_, lean_object* v_i_3347_, lean_object* v_stop_3348_, lean_object* v_b_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v_logExceptions_boxed_3357_; size_t v_i_boxed_3358_; size_t v_stop_boxed_3359_; lean_object* v_res_3360_; 
v_logExceptions_boxed_3357_ = lean_unbox(v_logExceptions_3344_);
v_i_boxed_3358_ = lean_unbox_usize(v_i_3347_);
lean_dec(v_i_3347_);
v_stop_boxed_3359_ = lean_unbox_usize(v_stop_3348_);
lean_dec(v_stop_3348_);
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_3342_, v_eval_3343_, v_logExceptions_boxed_3357_, v_onErr_3345_, v_as_3346_, v_i_boxed_3358_, v_stop_boxed_3359_, v_b_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec_ref(v_as_3346_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object* v_eval_3361_, lean_object* v_init_3362_, lean_object* v_cfgs_3363_, lean_object* v_onErr_3364_, uint8_t v_logExceptions_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3361_, v_logExceptions_3365_, v_onErr_3364_, v_init_3362_, v_cfgs_3363_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object* v_eval_3374_, lean_object* v_init_3375_, lean_object* v_cfgs_3376_, lean_object* v_onErr_3377_, lean_object* v_logExceptions_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
uint8_t v_logExceptions_boxed_3386_; lean_object* v_res_3387_; 
v_logExceptions_boxed_3386_ = lean_unbox(v_logExceptions_3378_);
v_res_3387_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3374_, v_init_3375_, v_cfgs_3376_, v_onErr_3377_, v_logExceptions_boxed_3386_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec_ref(v_cfgs_3376_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object* v_00_u03b1_3388_, lean_object* v_eval_3389_, lean_object* v_init_3390_, lean_object* v_cfgs_3391_, lean_object* v_onErr_3392_, uint8_t v_logExceptions_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3389_, v_logExceptions_3393_, v_onErr_3392_, v_init_3390_, v_cfgs_3391_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object* v_00_u03b1_3402_, lean_object* v_eval_3403_, lean_object* v_init_3404_, lean_object* v_cfgs_3405_, lean_object* v_onErr_3406_, lean_object* v_logExceptions_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_){
_start:
{
uint8_t v_logExceptions_boxed_3415_; lean_object* v_res_3416_; 
v_logExceptions_boxed_3415_ = lean_unbox(v_logExceptions_3407_);
v_res_3416_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(v_00_u03b1_3402_, v_eval_3403_, v_init_3404_, v_cfgs_3405_, v_onErr_3406_, v_logExceptions_boxed_3415_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec_ref(v_cfgs_3405_);
return v_res_3416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object* v_x_3417_){
_start:
{
uint8_t v___x_3418_; 
v___x_3418_ = 0;
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object* v_x_3419_){
_start:
{
uint8_t v_res_3420_; lean_object* v_r_3421_; 
v_res_3420_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3419_);
lean_dec(v_x_3419_);
v_r_3421_ = lean_box(v_res_3420_);
return v_r_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(lean_object* v___x_3422_, lean_object* v_ctx_x3f_3423_, size_t v_sz_3424_, size_t v_i_3425_, lean_object* v_bs_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_usize_dec_lt(v_i_3425_, v_sz_3424_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
lean_dec_ref(v_ctx_x3f_3423_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v_bs_3426_);
return v___x_3435_;
}
else
{
lean_object* v_assignment_3436_; lean_object* v___x_3437_; 
v_assignment_3436_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_ctx_x3f_3423_);
lean_inc(v___y_3432_);
lean_inc_ref(v___y_3431_);
lean_inc(v___y_3430_);
lean_inc_ref(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc_ref(v___y_3427_);
v___x_3437_ = lean_apply_7(v_ctx_x3f_3423_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, lean_box(0));
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v_v_3439_; lean_object* v___x_3440_; lean_object* v_bs_x27_3441_; lean_object* v_a_3443_; lean_object* v_tree_3448_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v_v_3439_ = lean_array_uget(v_bs_3426_, v_i_3425_);
v___x_3440_ = lean_unsigned_to_nat(0u);
v_bs_x27_3441_ = lean_array_uset(v_bs_3426_, v_i_3425_, v___x_3440_);
v_tree_3448_ = l_Lean_Elab_InfoTree_substitute(v_v_3439_, v_assignment_3436_);
if (lean_obj_tag(v_a_3438_) == 0)
{
v_a_3443_ = v_tree_3448_;
goto v___jp_3442_;
}
else
{
lean_object* v_val_3449_; lean_object* v___x_3450_; 
v_val_3449_ = lean_ctor_get(v_a_3438_, 0);
lean_inc(v_val_3449_);
lean_dec_ref_known(v_a_3438_, 1);
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v_val_3449_);
lean_ctor_set(v___x_3450_, 1, v_tree_3448_);
v_a_3443_ = v___x_3450_;
goto v___jp_3442_;
}
v___jp_3442_:
{
size_t v___x_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = ((size_t)1ULL);
v___x_3445_ = lean_usize_add(v_i_3425_, v___x_3444_);
v___x_3446_ = lean_array_uset(v_bs_x27_3441_, v_i_3425_, v_a_3443_);
v_i_3425_ = v___x_3445_;
v_bs_3426_ = v___x_3446_;
goto _start;
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v_bs_3426_);
lean_dec_ref(v_ctx_x3f_3423_);
v_a_3451_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3437_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3437_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v___x_3459_, lean_object* v_ctx_x3f_3460_, lean_object* v_sz_3461_, lean_object* v_i_3462_, lean_object* v_bs_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
size_t v_sz_boxed_3471_; size_t v_i_boxed_3472_; lean_object* v_res_3473_; 
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3461_);
lean_dec(v_sz_3461_);
v_i_boxed_3472_ = lean_unbox_usize(v_i_3462_);
lean_dec(v_i_3462_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3459_, v_ctx_x3f_3460_, v_sz_boxed_3471_, v_i_boxed_3472_, v_bs_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec_ref(v___x_3459_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(lean_object* v___x_3474_, lean_object* v_ctx_x3f_3475_, lean_object* v_x_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
if (lean_obj_tag(v_x_3476_) == 0)
{
lean_object* v_cs_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3510_; 
v_cs_3484_ = lean_ctor_get(v_x_3476_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_x_3476_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3486_ = v_x_3476_;
v_isShared_3487_ = v_isSharedCheck_3510_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_cs_3484_);
lean_dec(v_x_3476_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3510_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
size_t v_sz_3488_; size_t v___x_3489_; lean_object* v___x_3490_; 
v_sz_3488_ = lean_array_size(v_cs_3484_);
v___x_3489_ = ((size_t)0ULL);
v___x_3490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3474_, v_ctx_x3f_3475_, v_sz_3488_, v___x_3489_, v_cs_3484_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3501_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3501_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3501_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v_a_3491_);
v___x_3496_ = v___x_3486_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3498_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3496_);
v___x_3498_ = v___x_3493_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_del_object(v___x_3486_);
v_a_3502_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3490_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3490_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
else
{
lean_object* v_vs_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3537_; 
v_vs_3511_ = lean_ctor_get(v_x_3476_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_x_3476_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3513_ = v_x_3476_;
v_isShared_3514_ = v_isSharedCheck_3537_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_vs_3511_);
lean_dec(v_x_3476_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3537_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
size_t v_sz_3515_; size_t v___x_3516_; lean_object* v___x_3517_; 
v_sz_3515_ = lean_array_size(v_vs_3511_);
v___x_3516_ = ((size_t)0ULL);
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3474_, v_ctx_x3f_3475_, v_sz_3515_, v___x_3516_, v_vs_3511_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3528_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3528_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v_a_3518_);
v___x_3523_ = v___x_3513_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3523_);
v___x_3525_ = v___x_3520_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_del_object(v___x_3513_);
v_a_3529_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3517_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3517_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v___x_3538_, lean_object* v_ctx_x3f_3539_, size_t v_sz_3540_, size_t v_i_3541_, lean_object* v_bs_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
uint8_t v___x_3550_; 
v___x_3550_ = lean_usize_dec_lt(v_i_3541_, v_sz_3540_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref(v_ctx_x3f_3539_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v_bs_3542_);
return v___x_3551_;
}
else
{
lean_object* v_v_3552_; lean_object* v___x_3553_; 
v_v_3552_ = lean_array_uget_borrowed(v_bs_3542_, v_i_3541_);
lean_inc(v_v_3552_);
lean_inc_ref(v_ctx_x3f_3539_);
v___x_3553_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3538_, v_ctx_x3f_3539_, v_v_3552_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; lean_object* v_bs_x27_3556_; size_t v___x_3557_; size_t v___x_3558_; lean_object* v___x_3559_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = lean_unsigned_to_nat(0u);
v_bs_x27_3556_ = lean_array_uset(v_bs_3542_, v_i_3541_, v___x_3555_);
v___x_3557_ = ((size_t)1ULL);
v___x_3558_ = lean_usize_add(v_i_3541_, v___x_3557_);
v___x_3559_ = lean_array_uset(v_bs_x27_3556_, v_i_3541_, v_a_3554_);
v_i_3541_ = v___x_3558_;
v_bs_3542_ = v___x_3559_;
goto _start;
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref(v_bs_3542_);
lean_dec_ref(v_ctx_x3f_3539_);
v_a_3561_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3553_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3553_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v___x_3569_, lean_object* v_ctx_x3f_3570_, lean_object* v_sz_3571_, lean_object* v_i_3572_, lean_object* v_bs_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
size_t v_sz_boxed_3581_; size_t v_i_boxed_3582_; lean_object* v_res_3583_; 
v_sz_boxed_3581_ = lean_unbox_usize(v_sz_3571_);
lean_dec(v_sz_3571_);
v_i_boxed_3582_ = lean_unbox_usize(v_i_3572_);
lean_dec(v_i_3572_);
v_res_3583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3569_, v_ctx_x3f_3570_, v_sz_boxed_3581_, v_i_boxed_3582_, v_bs_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec_ref(v___x_3569_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v___x_3584_, lean_object* v_ctx_x3f_3585_, lean_object* v_x_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3584_, v_ctx_x3f_3585_, v_x_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v___x_3584_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object* v___x_3595_, lean_object* v_ctx_x3f_3596_, lean_object* v_t_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_root_3605_; lean_object* v_tail_3606_; lean_object* v_size_3607_; size_t v_shift_3608_; lean_object* v_tailOff_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3645_; 
v_root_3605_ = lean_ctor_get(v_t_3597_, 0);
v_tail_3606_ = lean_ctor_get(v_t_3597_, 1);
v_size_3607_ = lean_ctor_get(v_t_3597_, 2);
v_shift_3608_ = lean_ctor_get_usize(v_t_3597_, 4);
v_tailOff_3609_ = lean_ctor_get(v_t_3597_, 3);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_t_3597_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3611_ = v_t_3597_;
v_isShared_3612_ = v_isSharedCheck_3645_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_tailOff_3609_);
lean_inc(v_size_3607_);
lean_inc(v_tail_3606_);
lean_inc(v_root_3605_);
lean_dec(v_t_3597_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3645_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; 
lean_inc_ref(v_ctx_x3f_3596_);
v___x_3613_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3595_, v_ctx_x3f_3596_, v_root_3605_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; size_t v_sz_3615_; size_t v___x_3616_; lean_object* v___x_3617_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v_sz_3615_ = lean_array_size(v_tail_3606_);
v___x_3616_ = ((size_t)0ULL);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3595_, v_ctx_x3f_3596_, v_sz_3615_, v___x_3616_, v_tail_3606_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3628_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3628_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 1, v_a_3618_);
lean_ctor_set(v___x_3611_, 0, v_a_3614_);
v___x_3623_ = v___x_3611_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3614_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_a_3618_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_size_3607_);
lean_ctor_set(v_reuseFailAlloc_3627_, 3, v_tailOff_3609_);
lean_ctor_set_usize(v_reuseFailAlloc_3627_, 4, v_shift_3608_);
v___x_3623_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3625_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v___x_3623_);
v___x_3625_ = v___x_3620_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec(v_a_3614_);
lean_del_object(v___x_3611_);
lean_dec(v_tailOff_3609_);
lean_dec(v_size_3607_);
v_a_3629_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3617_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3617_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
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
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_del_object(v___x_3611_);
lean_dec(v_tailOff_3609_);
lean_dec(v_size_3607_);
lean_dec_ref(v_tail_3606_);
lean_dec_ref(v_ctx_x3f_3596_);
v_a_3637_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3613_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3613_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object* v___x_3646_, lean_object* v_ctx_x3f_3647_, lean_object* v_t_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3646_, v_ctx_x3f_3647_, v_t_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec_ref(v___x_3646_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3657_, lean_object* v_ctx_x3f_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v_a_3664_, lean_object* v_a_x3f_3665_){
_start:
{
lean_object* v___x_3667_; lean_object* v_infoState_3668_; lean_object* v_trees_3669_; lean_object* v___x_3670_; 
v___x_3667_ = lean_st_ref_get(v___y_3657_);
v_infoState_3668_ = lean_ctor_get(v___x_3667_, 7);
lean_inc_ref(v_infoState_3668_);
lean_dec(v___x_3667_);
v_trees_3669_ = lean_ctor_get(v_infoState_3668_, 2);
lean_inc_ref(v_trees_3669_);
v___x_3670_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_3668_, v_ctx_x3f_3658_, v_trees_3669_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3657_);
lean_dec_ref(v_infoState_3668_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3709_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3709_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3709_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v_infoState_3676_; lean_object* v_env_3677_; lean_object* v_nextMacroScope_3678_; lean_object* v_ngen_3679_; lean_object* v_auxDeclNGen_3680_; lean_object* v_traceState_3681_; lean_object* v_cache_3682_; lean_object* v_messages_3683_; lean_object* v_snapshotTasks_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3708_; 
v___x_3675_ = lean_st_ref_take(v___y_3657_);
v_infoState_3676_ = lean_ctor_get(v___x_3675_, 7);
v_env_3677_ = lean_ctor_get(v___x_3675_, 0);
v_nextMacroScope_3678_ = lean_ctor_get(v___x_3675_, 1);
v_ngen_3679_ = lean_ctor_get(v___x_3675_, 2);
v_auxDeclNGen_3680_ = lean_ctor_get(v___x_3675_, 3);
v_traceState_3681_ = lean_ctor_get(v___x_3675_, 4);
v_cache_3682_ = lean_ctor_get(v___x_3675_, 5);
v_messages_3683_ = lean_ctor_get(v___x_3675_, 6);
v_snapshotTasks_3684_ = lean_ctor_get(v___x_3675_, 8);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3686_ = v___x_3675_;
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_snapshotTasks_3684_);
lean_inc(v_infoState_3676_);
lean_inc(v_messages_3683_);
lean_inc(v_cache_3682_);
lean_inc(v_traceState_3681_);
lean_inc(v_auxDeclNGen_3680_);
lean_inc(v_ngen_3679_);
lean_inc(v_nextMacroScope_3678_);
lean_inc(v_env_3677_);
lean_dec(v___x_3675_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3708_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
uint8_t v_enabled_3688_; lean_object* v_assignment_3689_; lean_object* v_lazyAssignment_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3706_; 
v_enabled_3688_ = lean_ctor_get_uint8(v_infoState_3676_, sizeof(void*)*3);
v_assignment_3689_ = lean_ctor_get(v_infoState_3676_, 0);
v_lazyAssignment_3690_ = lean_ctor_get(v_infoState_3676_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_infoState_3676_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; 
v_unused_3707_ = lean_ctor_get(v_infoState_3676_, 2);
lean_dec(v_unused_3707_);
v___x_3692_ = v_infoState_3676_;
v_isShared_3693_ = v_isSharedCheck_3706_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_lazyAssignment_3690_);
lean_inc(v_assignment_3689_);
lean_dec(v_infoState_3676_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3706_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3694_ = l_Lean_PersistentArray_append___redArg(v_a_3664_, v_a_3671_);
lean_dec(v_a_3671_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 2, v___x_3694_);
v___x_3696_ = v___x_3692_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_assignment_3689_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_lazyAssignment_3690_);
lean_ctor_set(v_reuseFailAlloc_3705_, 2, v___x_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3705_, sizeof(void*)*3, v_enabled_3688_);
v___x_3696_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 7, v___x_3696_);
v___x_3698_ = v___x_3686_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_env_3677_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_nextMacroScope_3678_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_ngen_3679_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_auxDeclNGen_3680_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_traceState_3681_);
lean_ctor_set(v_reuseFailAlloc_3704_, 5, v_cache_3682_);
lean_ctor_set(v_reuseFailAlloc_3704_, 6, v_messages_3683_);
lean_ctor_set(v_reuseFailAlloc_3704_, 7, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3704_, 8, v_snapshotTasks_3684_);
v___x_3698_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3699_ = lean_st_ref_set(v___y_3657_, v___x_3698_);
v___x_3700_ = lean_box(0);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3700_);
v___x_3702_ = v___x_3673_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec_ref(v_a_3664_);
v_a_3710_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3670_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3670_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3718_, lean_object* v_ctx_x3f_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v_a_3725_, lean_object* v_a_x3f_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3718_, v_ctx_x3f_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v_a_3725_, v_a_x3f_3726_);
lean_dec(v_a_x3f_3726_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3718_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; lean_object* v_infoState_3732_; lean_object* v_trees_3733_; lean_object* v___x_3734_; lean_object* v_infoState_3735_; lean_object* v_env_3736_; lean_object* v_nextMacroScope_3737_; lean_object* v_ngen_3738_; lean_object* v_auxDeclNGen_3739_; lean_object* v_traceState_3740_; lean_object* v_cache_3741_; lean_object* v_messages_3742_; lean_object* v_snapshotTasks_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3766_; 
v___x_3731_ = lean_st_ref_get(v___y_3729_);
v_infoState_3732_ = lean_ctor_get(v___x_3731_, 7);
lean_inc_ref(v_infoState_3732_);
lean_dec(v___x_3731_);
v_trees_3733_ = lean_ctor_get(v_infoState_3732_, 2);
lean_inc_ref(v_trees_3733_);
lean_dec_ref(v_infoState_3732_);
v___x_3734_ = lean_st_ref_take(v___y_3729_);
v_infoState_3735_ = lean_ctor_get(v___x_3734_, 7);
v_env_3736_ = lean_ctor_get(v___x_3734_, 0);
v_nextMacroScope_3737_ = lean_ctor_get(v___x_3734_, 1);
v_ngen_3738_ = lean_ctor_get(v___x_3734_, 2);
v_auxDeclNGen_3739_ = lean_ctor_get(v___x_3734_, 3);
v_traceState_3740_ = lean_ctor_get(v___x_3734_, 4);
v_cache_3741_ = lean_ctor_get(v___x_3734_, 5);
v_messages_3742_ = lean_ctor_get(v___x_3734_, 6);
v_snapshotTasks_3743_ = lean_ctor_get(v___x_3734_, 8);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3745_ = v___x_3734_;
v_isShared_3746_ = v_isSharedCheck_3766_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_snapshotTasks_3743_);
lean_inc(v_infoState_3735_);
lean_inc(v_messages_3742_);
lean_inc(v_cache_3741_);
lean_inc(v_traceState_3740_);
lean_inc(v_auxDeclNGen_3739_);
lean_inc(v_ngen_3738_);
lean_inc(v_nextMacroScope_3737_);
lean_inc(v_env_3736_);
lean_dec(v___x_3734_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3766_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
uint8_t v_enabled_3747_; lean_object* v_assignment_3748_; lean_object* v_lazyAssignment_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3764_; 
v_enabled_3747_ = lean_ctor_get_uint8(v_infoState_3735_, sizeof(void*)*3);
v_assignment_3748_ = lean_ctor_get(v_infoState_3735_, 0);
v_lazyAssignment_3749_ = lean_ctor_get(v_infoState_3735_, 1);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_infoState_3735_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; 
v_unused_3765_ = lean_ctor_get(v_infoState_3735_, 2);
lean_dec(v_unused_3765_);
v___x_3751_ = v_infoState_3735_;
v_isShared_3752_ = v_isSharedCheck_3764_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_lazyAssignment_3749_);
lean_inc(v_assignment_3748_);
lean_dec(v_infoState_3735_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3764_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
v___x_3753_ = lean_unsigned_to_nat(32u);
v___x_3754_ = lean_mk_empty_array_with_capacity(v___x_3753_);
lean_dec_ref(v___x_3754_);
v___x_3755_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 2, v___x_3755_);
v___x_3757_ = v___x_3751_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_assignment_3748_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_lazyAssignment_3749_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v___x_3755_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*3, v_enabled_3747_);
v___x_3757_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 7, v___x_3757_);
v___x_3759_ = v___x_3745_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_env_3736_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_nextMacroScope_3737_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_ngen_3738_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_auxDeclNGen_3739_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_traceState_3740_);
lean_ctor_set(v_reuseFailAlloc_3762_, 5, v_cache_3741_);
lean_ctor_set(v_reuseFailAlloc_3762_, 6, v_messages_3742_);
lean_ctor_set(v_reuseFailAlloc_3762_, 7, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3762_, 8, v_snapshotTasks_3743_);
v___x_3759_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_st_ref_set(v___y_3729_, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_trees_3733_);
return v___x_3761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3767_);
lean_dec(v___y_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object* v_x_3770_, lean_object* v_ctx_x3f_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; lean_object* v_infoState_3780_; uint8_t v_enabled_3781_; uint8_t v___x_3782_; 
v___x_3779_ = lean_st_ref_get(v___y_3777_);
v_infoState_3780_ = lean_ctor_get(v___x_3779_, 7);
lean_inc_ref(v_infoState_3780_);
lean_dec(v___x_3779_);
v_enabled_3781_ = lean_ctor_get_uint8(v_infoState_3780_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3780_);
v___x_3782_ = lean_bool_not(v_enabled_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; lean_object* v_a_3784_; lean_object* v_r_3785_; 
v___x_3783_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3777_);
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref(v___x_3783_);
lean_inc(v___y_3777_);
lean_inc_ref(v___y_3776_);
lean_inc(v___y_3775_);
lean_inc_ref(v___y_3774_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
v_r_3785_ = lean_apply_7(v_x_3770_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, lean_box(0));
if (lean_obj_tag(v_r_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3810_; 
v_a_3786_ = lean_ctor_get(v_r_3785_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_r_3785_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3788_ = v_r_3785_;
v_isShared_3789_ = v_isSharedCheck_3810_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v_r_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3810_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
lean_inc(v_a_3786_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set_tag(v___x_3788_, 1);
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3792_; 
v___x_3792_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3777_, v_ctx_x3f_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v_a_3784_, v___x_3791_);
lean_dec_ref(v___x_3791_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3800_);
v___x_3794_ = v___x_3792_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v_a_3786_);
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3786_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec(v_a_3786_);
v_a_3801_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3792_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3792_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_a_3811_ = lean_ctor_get(v_r_3785_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v_r_3785_, 1);
v___x_3812_ = lean_box(0);
v___x_3813_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3777_, v_ctx_x3f_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v_a_3784_, v___x_3812_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v___x_3813_, 0);
lean_dec(v_unused_3821_);
v___x_3815_ = v___x_3813_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_dec(v___x_3813_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
lean_ctor_set_tag(v___x_3815_, 1);
lean_ctor_set(v___x_3815_, 0, v_a_3811_);
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3811_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec(v_a_3811_);
v_a_3822_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3813_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3813_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
else
{
lean_object* v___x_3830_; 
lean_dec_ref(v_ctx_x3f_3771_);
lean_inc(v___y_3777_);
lean_inc_ref(v___y_3776_);
lean_inc(v___y_3775_);
lean_inc_ref(v___y_3774_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
v___x_3830_ = lean_apply_7(v_x_3770_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, lean_box(0));
return v___x_3830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_3831_, lean_object* v_ctx_x3f_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3831_, v_ctx_x3f_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; lean_object* v_env_3846_; lean_object* v___x_3847_; lean_object* v_mctx_3848_; lean_object* v_options_3849_; lean_object* v_currNamespace_3850_; lean_object* v_openDecls_3851_; lean_object* v___x_3852_; lean_object* v_ngen_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3845_ = lean_st_ref_get(v___y_3843_);
v_env_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc_ref(v_env_3846_);
lean_dec(v___x_3845_);
v___x_3847_ = lean_st_ref_get(v___y_3841_);
v_mctx_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc_ref(v_mctx_3848_);
lean_dec(v___x_3847_);
v_options_3849_ = lean_ctor_get(v___y_3842_, 2);
v_currNamespace_3850_ = lean_ctor_get(v___y_3842_, 6);
v_openDecls_3851_ = lean_ctor_get(v___y_3842_, 7);
v___x_3852_ = lean_st_ref_get(v___y_3843_);
v_ngen_3853_ = lean_ctor_get(v___x_3852_, 2);
lean_inc_ref(v_ngen_3853_);
lean_dec(v___x_3852_);
v___x_3854_ = lean_box(0);
v___x_3855_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_3851_);
lean_inc(v_currNamespace_3850_);
lean_inc_ref(v_options_3849_);
v___x_3856_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3856_, 0, v_env_3846_);
lean_ctor_set(v___x_3856_, 1, v___x_3854_);
lean_ctor_set(v___x_3856_, 2, v___x_3855_);
lean_ctor_set(v___x_3856_, 3, v_mctx_3848_);
lean_ctor_set(v___x_3856_, 4, v_options_3849_);
lean_ctor_set(v___x_3856_, 5, v_currNamespace_3850_);
lean_ctor_set(v___x_3856_, 6, v_openDecls_3851_);
lean_ctor_set(v___x_3856_, 7, v_ngen_3853_);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v___x_3870_; lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3895_; 
v___x_3870_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3866_, v___y_3867_, v___y_3868_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3873_ = v___x_3870_;
v_isShared_3874_ = v_isSharedCheck_3895_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3895_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v_fileMap_3875_; lean_object* v_env_3876_; lean_object* v_mctx_3877_; lean_object* v_options_3878_; lean_object* v_currNamespace_3879_; lean_object* v_openDecls_3880_; lean_object* v_ngen_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3892_; 
v_fileMap_3875_ = lean_ctor_get(v___y_3867_, 1);
v_env_3876_ = lean_ctor_get(v_a_3871_, 0);
v_mctx_3877_ = lean_ctor_get(v_a_3871_, 3);
v_options_3878_ = lean_ctor_get(v_a_3871_, 4);
v_currNamespace_3879_ = lean_ctor_get(v_a_3871_, 5);
v_openDecls_3880_ = lean_ctor_get(v_a_3871_, 6);
v_ngen_3881_ = lean_ctor_get(v_a_3871_, 7);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_a_3871_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; lean_object* v_unused_3894_; 
v_unused_3893_ = lean_ctor_get(v_a_3871_, 2);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_a_3871_, 1);
lean_dec(v_unused_3894_);
v___x_3883_ = v_a_3871_;
v_isShared_3884_ = v_isSharedCheck_3892_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_ngen_3881_);
lean_inc(v_openDecls_3880_);
lean_inc(v_currNamespace_3879_);
lean_inc(v_options_3878_);
lean_inc(v_mctx_3877_);
lean_inc(v_env_3876_);
lean_dec(v_a_3871_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3892_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3885_ = lean_box(0);
lean_inc_ref(v_fileMap_3875_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 2, v_fileMap_3875_);
lean_ctor_set(v___x_3883_, 1, v___x_3885_);
v___x_3887_ = v___x_3883_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_env_3876_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_fileMap_3875_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_mctx_3877_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v_options_3878_);
lean_ctor_set(v_reuseFailAlloc_3891_, 5, v_currNamespace_3879_);
lean_ctor_set(v_reuseFailAlloc_3891_, 6, v_openDecls_3880_);
lean_ctor_set(v_reuseFailAlloc_3891_, 7, v_ngen_3881_);
v___x_3887_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3889_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 0, v___x_3887_);
v___x_3889_ = v___x_3873_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v___x_3911_; lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3921_; 
v___x_3911_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3914_ = v___x_3911_;
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_a_3912_);
v___x_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3917_);
v___x_3919_ = v___x_3914_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object* v_x_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v___f_3939_; lean_object* v___x_3940_; 
v___f_3939_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0));
v___x_3940_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3931_, v___f_3939_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object* v_x_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object* v_00_u03b1_3950_, lean_object* v_x_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object* v_00_u03b1_3960_, lean_object* v_x_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(v_00_u03b1_3960_, v_x_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
return v_res_3969_;
}
}
static uint64_t _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4(void){
_start:
{
lean_object* v___x_3987_; uint64_t v___x_3988_; 
v___x_3987_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3988_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3987_);
return v___x_3988_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5(void){
_start:
{
uint64_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = lean_uint64_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4);
v___x_3990_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3991_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set_uint64(v___x_3991_, sizeof(void*)*1, v___x_3989_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6(void){
_start:
{
uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3992_ = 1;
v___x_3993_ = lean_unsigned_to_nat(0u);
v___x_3994_ = lean_box(0);
v___x_3995_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1));
v___x_3996_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2);
v___x_3997_ = lean_box(1);
v___x_3998_ = 0;
v___x_3999_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5);
v___x_4000_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
lean_ctor_set(v___x_4000_, 1, v___x_3997_);
lean_ctor_set(v___x_4000_, 2, v___x_3996_);
lean_ctor_set(v___x_4000_, 3, v___x_3995_);
lean_ctor_set(v___x_4000_, 4, v___x_3994_);
lean_ctor_set(v___x_4000_, 5, v___x_3993_);
lean_ctor_set(v___x_4000_, 6, v___x_3994_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7, v___x_3998_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7 + 1, v___x_3998_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7 + 2, v___x_3998_);
lean_ctor_set_uint8(v___x_4000_, sizeof(void*)*7 + 3, v___x_3992_);
return v___x_4000_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_4002_ = lean_unsigned_to_nat(0u);
v___x_4003_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
lean_ctor_set(v___x_4003_, 2, v___x_4002_);
lean_ctor_set(v___x_4003_, 3, v___x_4002_);
lean_ctor_set(v___x_4003_, 4, v___x_4001_);
lean_ctor_set(v___x_4003_, 5, v___x_4001_);
lean_ctor_set(v___x_4003_, 6, v___x_4001_);
lean_ctor_set(v___x_4003_, 7, v___x_4001_);
lean_ctor_set(v___x_4003_, 8, v___x_4001_);
lean_ctor_set(v___x_4003_, 9, v___x_4001_);
return v___x_4003_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_4005_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
lean_ctor_set(v___x_4005_, 2, v___x_4004_);
lean_ctor_set(v___x_4005_, 3, v___x_4004_);
lean_ctor_set(v___x_4005_, 4, v___x_4004_);
lean_ctor_set(v___x_4005_, 5, v___x_4004_);
return v___x_4005_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_4007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
lean_ctor_set(v___x_4007_, 2, v___x_4006_);
lean_ctor_set(v___x_4007_, 3, v___x_4006_);
lean_ctor_set(v___x_4007_, 4, v___x_4006_);
return v___x_4007_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4008_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
v___x_4009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_4010_ = lean_box(1);
v___x_4011_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8);
v___x_4012_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7);
v___x_4013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
lean_ctor_set(v___x_4013_, 1, v___x_4011_);
lean_ctor_set(v___x_4013_, 2, v___x_4010_);
lean_ctor_set(v___x_4013_, 3, v___x_4009_);
lean_ctor_set(v___x_4013_, 4, v___x_4008_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object* v_mx_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4021_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2));
v___x_4022_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6);
v___x_4023_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10);
v___x_4024_ = lean_st_mk_ref(v___x_4023_);
v___x_4025_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4025_, 0, lean_box(0));
lean_closure_set(v___x_4025_, 1, v_mx_4017_);
v___x_4026_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11));
v___x_4027_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_4025_, v___x_4021_, v___x_4026_, v___x_4022_, v___x_4024_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4037_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4037_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4037_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; lean_object* v_fst_4033_; lean_object* v___x_4035_; 
v___x_4032_ = lean_st_ref_get(v___x_4024_);
lean_dec(v___x_4024_);
lean_dec(v___x_4032_);
v_fst_4033_ = lean_ctor_get(v_a_4028_, 0);
lean_inc(v_fst_4033_);
lean_dec(v_a_4028_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v_fst_4033_);
v___x_4035_ = v___x_4030_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_fst_4033_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v___x_4024_);
v_a_4038_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4027_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4027_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object* v_mx_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_4046_, v_a_4047_, v_a_4048_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object* v_00_u03b1_4051_, lean_object* v_mx_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_4052_, v_a_4053_, v_a_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object* v_00_u03b1_4057_, lean_object* v_mx_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_4057_, v_mx_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_4066_, v___y_4067_, v___y_4068_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_4084_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object* v_00_u03b1_4095_, lean_object* v_x_4096_, lean_object* v_ctx_x3f_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_4096_, v_ctx_x3f_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4106_, lean_object* v_x_4107_, lean_object* v_ctx_x3f_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_4106_, v_x_4107_, v_ctx_x3f_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object* v_eval_4117_, uint8_t v_logExceptions_4118_, lean_object* v_onErr_4119_, lean_object* v_init_4120_, lean_object* v_cfg_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_4117_, v_logExceptions_4118_, v_onErr_4119_, v_init_4120_, v_cfg_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object* v_eval_4130_, lean_object* v_logExceptions_4131_, lean_object* v_onErr_4132_, lean_object* v_init_4133_, lean_object* v_cfg_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
uint8_t v_logExceptions_boxed_4142_; lean_object* v_res_4143_; 
v_logExceptions_boxed_4142_ = lean_unbox(v_logExceptions_4131_);
v_res_4143_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4130_, v_logExceptions_boxed_4142_, v_onErr_4132_, v_init_4133_, v_cfg_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object* v_eval_4144_, lean_object* v_init_4145_, lean_object* v_cfg_4146_, lean_object* v_onErr_4147_, uint8_t v_logExceptions_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v___x_4152_; lean_object* v___f_4153_; uint8_t v___y_4155_; lean_object* v___x_4158_; uint8_t v___x_4159_; 
v___x_4152_ = lean_box(v_logExceptions_4148_);
lean_inc_n(v_cfg_4146_, 2);
lean_inc(v_init_4145_);
v___f_4153_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4153_, 0, v_eval_4144_);
lean_closure_set(v___f_4153_, 1, v___x_4152_);
lean_closure_set(v___f_4153_, 2, v_onErr_4147_);
lean_closure_set(v___f_4153_, 3, v_init_4145_);
lean_closure_set(v___f_4153_, 4, v_cfg_4146_);
v___x_4158_ = lean_unsigned_to_nat(0u);
v___x_4159_ = l_Lean_Syntax_matchesNull(v_cfg_4146_, v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; 
v___x_4160_ = l_Lean_Syntax_getNumArgs(v_cfg_4146_);
v___x_4161_ = lean_unsigned_to_nat(1u);
v___x_4162_ = lean_nat_dec_eq(v___x_4160_, v___x_4161_);
lean_dec(v___x_4160_);
if (v___x_4162_ == 0)
{
lean_dec(v_cfg_4146_);
v___y_4155_ = v___x_4162_;
goto v___jp_4154_;
}
else
{
lean_object* v___x_4163_; uint8_t v___x_4164_; 
v___x_4163_ = l_Lean_Syntax_getArg(v_cfg_4146_, v___x_4158_);
lean_dec(v_cfg_4146_);
v___x_4164_ = l_Lean_Syntax_matchesNull(v___x_4163_, v___x_4158_);
v___y_4155_ = v___x_4164_;
goto v___jp_4154_;
}
}
else
{
lean_dec(v_cfg_4146_);
v___y_4155_ = v___x_4159_;
goto v___jp_4154_;
}
v___jp_4154_:
{
if (v___y_4155_ == 0)
{
lean_object* v___x_4156_; 
lean_dec(v_init_4145_);
v___x_4156_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4153_, v_a_4149_, v_a_4150_);
return v___x_4156_;
}
else
{
lean_object* v___x_4157_; 
lean_dec_ref(v___f_4153_);
v___x_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_init_4145_);
return v___x_4157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object* v_eval_4165_, lean_object* v_init_4166_, lean_object* v_cfg_4167_, lean_object* v_onErr_4168_, lean_object* v_logExceptions_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
uint8_t v_logExceptions_boxed_4173_; lean_object* v_res_4174_; 
v_logExceptions_boxed_4173_ = lean_unbox(v_logExceptions_4169_);
v_res_4174_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4165_, v_init_4166_, v_cfg_4167_, v_onErr_4168_, v_logExceptions_boxed_4173_, v_a_4170_, v_a_4171_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object* v_00_u03b1_4175_, lean_object* v_eval_4176_, lean_object* v_init_4177_, lean_object* v_cfg_4178_, lean_object* v_onErr_4179_, uint8_t v_logExceptions_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4176_, v_init_4177_, v_cfg_4178_, v_onErr_4179_, v_logExceptions_4180_, v_a_4181_, v_a_4182_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object* v_00_u03b1_4185_, lean_object* v_eval_4186_, lean_object* v_init_4187_, lean_object* v_cfg_4188_, lean_object* v_onErr_4189_, lean_object* v_logExceptions_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
uint8_t v_logExceptions_boxed_4194_; lean_object* v_res_4195_; 
v_logExceptions_boxed_4194_ = lean_unbox(v_logExceptions_4190_);
v_res_4195_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(v_00_u03b1_4185_, v_eval_4186_, v_init_4187_, v_cfg_4188_, v_onErr_4189_, v_logExceptions_boxed_4194_, v_a_4191_, v_a_4192_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object* v_eval_4196_, uint8_t v_logExceptions_4197_, lean_object* v_onErr_4198_, lean_object* v_init_4199_, lean_object* v_cfgs_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_4196_, v_logExceptions_4197_, v_onErr_4198_, v_init_4199_, v_cfgs_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object* v_eval_4209_, lean_object* v_logExceptions_4210_, lean_object* v_onErr_4211_, lean_object* v_init_4212_, lean_object* v_cfgs_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
uint8_t v_logExceptions_boxed_4221_; lean_object* v_res_4222_; 
v_logExceptions_boxed_4221_ = lean_unbox(v_logExceptions_4210_);
v_res_4222_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4209_, v_logExceptions_boxed_4221_, v_onErr_4211_, v_init_4212_, v_cfgs_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v_cfgs_4213_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object* v_eval_4223_, lean_object* v_init_4224_, lean_object* v_cfgs_4225_, lean_object* v_onErr_4226_, uint8_t v_logExceptions_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; uint8_t v___x_4233_; 
v___x_4231_ = lean_array_get_size(v_cfgs_4225_);
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = lean_nat_dec_eq(v___x_4231_, v___x_4232_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; lean_object* v___f_4235_; lean_object* v___x_4236_; 
v___x_4234_ = lean_box(v_logExceptions_4227_);
v___f_4235_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4235_, 0, v_eval_4223_);
lean_closure_set(v___f_4235_, 1, v___x_4234_);
lean_closure_set(v___f_4235_, 2, v_onErr_4226_);
lean_closure_set(v___f_4235_, 3, v_init_4224_);
lean_closure_set(v___f_4235_, 4, v_cfgs_4225_);
v___x_4236_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4235_, v_a_4228_, v_a_4229_);
return v___x_4236_;
}
else
{
lean_object* v___x_4237_; 
lean_dec_ref(v_onErr_4226_);
lean_dec_ref(v_cfgs_4225_);
lean_dec_ref(v_eval_4223_);
v___x_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4237_, 0, v_init_4224_);
return v___x_4237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object* v_eval_4238_, lean_object* v_init_4239_, lean_object* v_cfgs_4240_, lean_object* v_onErr_4241_, lean_object* v_logExceptions_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_){
_start:
{
uint8_t v_logExceptions_boxed_4246_; lean_object* v_res_4247_; 
v_logExceptions_boxed_4246_ = lean_unbox(v_logExceptions_4242_);
v_res_4247_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4238_, v_init_4239_, v_cfgs_4240_, v_onErr_4241_, v_logExceptions_boxed_4246_, v_a_4243_, v_a_4244_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object* v_00_u03b1_4248_, lean_object* v_eval_4249_, lean_object* v_init_4250_, lean_object* v_cfgs_4251_, lean_object* v_onErr_4252_, uint8_t v_logExceptions_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4249_, v_init_4250_, v_cfgs_4251_, v_onErr_4252_, v_logExceptions_4253_, v_a_4254_, v_a_4255_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object* v_00_u03b1_4258_, lean_object* v_eval_4259_, lean_object* v_init_4260_, lean_object* v_cfgs_4261_, lean_object* v_onErr_4262_, lean_object* v_logExceptions_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
uint8_t v_logExceptions_boxed_4267_; lean_object* v_res_4268_; 
v_logExceptions_boxed_4267_ = lean_unbox(v_logExceptions_4263_);
v_res_4268_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(v_00_u03b1_4258_, v_eval_4259_, v_init_4260_, v_cfgs_4261_, v_onErr_4262_, v_logExceptions_boxed_4267_, v_a_4264_, v_a_4265_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
return v_res_4268_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

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
lean_object* lean_erase_macro_scopes(lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_inc(v___y_262_);
lean_inc(v___y_263_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
v___x_273_ = lean_apply_7(v___x_3802__overap_272_, v___y_264_, v___y_265_, v___y_261_, v___y_263_, v___y_260_, v___y_262_, lean_box(0));
return v___x_273_;
}
}
v___jp_275_:
{
if (v___y_285_ == 0)
{
if (lean_obj_tag(v___y_276_) == 0)
{
lean_dec_ref_known(v___y_276_, 2);
lean_dec_ref(v___y_278_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
return v___y_279_;
}
else
{
lean_object* v_id_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_300_; 
v_id_286_ = lean_ctor_get(v___y_276_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___y_276_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___y_276_, 1);
lean_dec(v_unused_301_);
v___x_288_ = v___y_276_;
v_isShared_289_ = v_isSharedCheck_300_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_id_286_);
lean_dec(v___y_276_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_300_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___x_290_; 
v___x_290_ = l_Lean_instBEqInternalExceptionId_beq(v___y_280_, v_id_286_);
lean_dec(v_id_286_);
if (v___x_290_ == 0)
{
lean_del_object(v___x_288_);
lean_dec_ref(v___y_278_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
return v___y_279_;
}
else
{
lean_dec_ref(v___y_279_);
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
v___y_260_ = v___y_278_;
v___y_261_ = v___y_277_;
v___y_262_ = v___y_281_;
v___y_263_ = v___y_283_;
v___y_264_ = v___y_282_;
v___y_265_ = v___y_284_;
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
v___y_260_ = v___y_278_;
v___y_261_ = v___y_277_;
v___y_262_ = v___y_281_;
v___y_263_ = v___y_283_;
v___y_264_ = v___y_282_;
v___y_265_ = v___y_284_;
v___y_266_ = v___x_299_;
goto v___jp_259_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_278_);
lean_dec_ref(v___y_276_);
lean_dec(v_a_258_);
lean_del_object(v___x_228_);
lean_dec(v_expectedType_x3f_226_);
lean_dec_ref_known(v___x_223_, 3);
lean_dec_ref(v___x_207_);
return v___y_279_;
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
v___y_276_ = v_a_310_;
v___y_277_ = v___y_305_;
v___y_278_ = v___y_307_;
v___y_279_ = v___x_309_;
v___y_280_ = v___x_311_;
v___y_281_ = v___y_308_;
v___y_282_ = v___y_303_;
v___y_283_ = v___y_306_;
v___y_284_ = v___y_304_;
v___y_285_ = v___x_313_;
goto v___jp_275_;
}
else
{
v___y_276_ = v_a_310_;
v___y_277_ = v___y_305_;
v___y_278_ = v___y_307_;
v___y_279_ = v___x_309_;
v___y_280_ = v___x_311_;
v___y_281_ = v___y_308_;
v___y_282_ = v___y_303_;
v___y_283_ = v___y_306_;
v___y_284_ = v___y_304_;
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
if (lean_obj_tag(v___y_963_) == 0)
{
lean_dec_ref_known(v___y_963_, 2);
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
return v___y_962_;
}
else
{
lean_object* v_id_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_977_; 
v_id_965_ = lean_ctor_get(v___y_963_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___y_963_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___y_963_, 1);
lean_dec(v_unused_978_);
v___x_967_ = v___y_963_;
v_isShared_968_ = v_isSharedCheck_977_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_id_965_);
lean_dec(v___y_963_);
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
return v___y_962_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec_ref(v___y_962_);
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
lean_dec_ref(v___y_963_);
lean_dec_ref(v_errMsg_952_);
lean_dec_ref(v_e_951_);
return v___y_962_;
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
v___y_962_ = v___y_980_;
v___y_963_ = v_a_981_;
v___y_964_ = v___x_983_;
goto v___jp_961_;
}
else
{
v___y_962_ = v___y_980_;
v___y_963_ = v_a_981_;
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
lean_object* v_options_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_options_1187_ = lean_ctor_get(v___y_1185_, 2);
v___x_1188_ = l_Lean_Elab_pp_macroStack;
v___x_1189_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec(v_macroStack_1184_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_msgData_1183_);
return v___x_1190_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_1210_, lean_object* v_macroStack_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1210_, v_macroStack_1211_, v___y_1212_);
lean_dec_ref(v___y_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(lean_object* v_msg_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_ref_1223_; lean_object* v___x_1224_; lean_object* v_a_1225_; lean_object* v_macroStack_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_ref_1223_ = lean_ctor_get(v___y_1220_, 5);
v___x_1224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v_msg_1215_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref(v___x_1224_);
v_macroStack_1226_ = lean_ctor_get(v___y_1216_, 1);
v___x_1227_ = l_Lean_Elab_getBetterRef(v_ref_1223_, v_macroStack_1226_);
lean_inc(v_macroStack_1226_);
v___x_1228_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_a_1225_, v_macroStack_1226_, v___y_1220_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1227_);
lean_ctor_set(v___x_1233_, 1, v_a_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 1);
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(lean_object* v_ref_1247_, lean_object* v_msg_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_fileName_1256_; lean_object* v_fileMap_1257_; lean_object* v_options_1258_; lean_object* v_currRecDepth_1259_; lean_object* v_maxRecDepth_1260_; lean_object* v_ref_1261_; lean_object* v_currNamespace_1262_; lean_object* v_openDecls_1263_; lean_object* v_initHeartbeats_1264_; lean_object* v_maxHeartbeats_1265_; lean_object* v_quotContext_1266_; lean_object* v_currMacroScope_1267_; uint8_t v_diag_1268_; lean_object* v_cancelTk_x3f_1269_; uint8_t v_suppressElabErrors_1270_; lean_object* v_inheritedTraceOptions_1271_; lean_object* v_ref_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_fileName_1256_ = lean_ctor_get(v___y_1253_, 0);
v_fileMap_1257_ = lean_ctor_get(v___y_1253_, 1);
v_options_1258_ = lean_ctor_get(v___y_1253_, 2);
v_currRecDepth_1259_ = lean_ctor_get(v___y_1253_, 3);
v_maxRecDepth_1260_ = lean_ctor_get(v___y_1253_, 4);
v_ref_1261_ = lean_ctor_get(v___y_1253_, 5);
v_currNamespace_1262_ = lean_ctor_get(v___y_1253_, 6);
v_openDecls_1263_ = lean_ctor_get(v___y_1253_, 7);
v_initHeartbeats_1264_ = lean_ctor_get(v___y_1253_, 8);
v_maxHeartbeats_1265_ = lean_ctor_get(v___y_1253_, 9);
v_quotContext_1266_ = lean_ctor_get(v___y_1253_, 10);
v_currMacroScope_1267_ = lean_ctor_get(v___y_1253_, 11);
v_diag_1268_ = lean_ctor_get_uint8(v___y_1253_, sizeof(void*)*14);
v_cancelTk_x3f_1269_ = lean_ctor_get(v___y_1253_, 12);
v_suppressElabErrors_1270_ = lean_ctor_get_uint8(v___y_1253_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1271_ = lean_ctor_get(v___y_1253_, 13);
v_ref_1272_ = l_Lean_replaceRef(v_ref_1247_, v_ref_1261_);
lean_inc_ref(v_inheritedTraceOptions_1271_);
lean_inc(v_cancelTk_x3f_1269_);
lean_inc(v_currMacroScope_1267_);
lean_inc(v_quotContext_1266_);
lean_inc(v_maxHeartbeats_1265_);
lean_inc(v_initHeartbeats_1264_);
lean_inc(v_openDecls_1263_);
lean_inc(v_currNamespace_1262_);
lean_inc(v_maxRecDepth_1260_);
lean_inc(v_currRecDepth_1259_);
lean_inc_ref(v_options_1258_);
lean_inc_ref(v_fileMap_1257_);
lean_inc_ref(v_fileName_1256_);
v___x_1273_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1273_, 0, v_fileName_1256_);
lean_ctor_set(v___x_1273_, 1, v_fileMap_1257_);
lean_ctor_set(v___x_1273_, 2, v_options_1258_);
lean_ctor_set(v___x_1273_, 3, v_currRecDepth_1259_);
lean_ctor_set(v___x_1273_, 4, v_maxRecDepth_1260_);
lean_ctor_set(v___x_1273_, 5, v_ref_1272_);
lean_ctor_set(v___x_1273_, 6, v_currNamespace_1262_);
lean_ctor_set(v___x_1273_, 7, v_openDecls_1263_);
lean_ctor_set(v___x_1273_, 8, v_initHeartbeats_1264_);
lean_ctor_set(v___x_1273_, 9, v_maxHeartbeats_1265_);
lean_ctor_set(v___x_1273_, 10, v_quotContext_1266_);
lean_ctor_set(v___x_1273_, 11, v_currMacroScope_1267_);
lean_ctor_set(v___x_1273_, 12, v_cancelTk_x3f_1269_);
lean_ctor_set(v___x_1273_, 13, v_inheritedTraceOptions_1271_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*14, v_diag_1268_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*14 + 1, v_suppressElabErrors_1270_);
v___x_1274_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___x_1273_, v___y_1254_);
lean_dec_ref_known(v___x_1273_, 14);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg___boxed(lean_object* v_ref_1275_, lean_object* v_msg_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1275_, v_msg_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v_ref_1275_);
return v_res_1284_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__0));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__2));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object* v_item_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_bool_x3f_1299_; 
v_bool_x3f_1299_ = lean_ctor_get(v_item_1291_, 3);
if (lean_obj_tag(v_bool_x3f_1299_) == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v_item_1291_);
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
else
{
lean_object* v_option_1302_; lean_object* v_origOptionName_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_option_1302_ = lean_ctor_get(v_item_1291_, 1);
lean_inc(v_option_1302_);
v_origOptionName_1303_ = lean_ctor_get(v_item_1291_, 4);
lean_inc(v_origOptionName_1303_);
lean_dec_ref(v_item_1291_);
v___x_1304_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__1);
v___x_1305_ = l_Lean_MessageData_ofName(v_origOptionName_1303_);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___closed__3);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1302_, v___x_1308_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_option_1302_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool___boxed(lean_object* v_item_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(lean_object* v_00_u03b1_1319_, lean_object* v_ref_1320_, lean_object* v_msg_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1320_, v_msg_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_ref_1331_, lean_object* v_msg_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0(v_00_u03b1_1330_, v_ref_1331_, v_msg_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v_ref_1331_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(lean_object* v_00_u03b1_1341_, lean_object* v_msg_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___redArg(v_msg_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_msg_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0(v_00_u03b1_1351_, v_msg_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(lean_object* v_msgData_1361_, lean_object* v_macroStack_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___redArg(v_msgData_1361_, v_macroStack_1362_, v___y_1367_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1371_, lean_object* v_macroStack_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1(v_msgData_1371_, v_macroStack_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1380_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__0));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__2));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__4));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object* v_item_1390_, lean_object* v_structName_x3f_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_option_1399_; lean_object* v_origOptionName_1400_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1409_; uint8_t v___x_1418_; 
v_option_1399_ = lean_ctor_get(v_item_1390_, 1);
lean_inc(v_option_1399_);
v_origOptionName_1400_ = lean_ctor_get(v_item_1390_, 4);
lean_inc(v_origOptionName_1400_);
lean_dec_ref(v_item_1390_);
v___x_1418_ = l_Lean_Name_isAnonymous(v_origOptionName_1400_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1419_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1420_ = l_Lean_MessageData_ofName(v_origOptionName_1400_);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___y_1409_ = v___x_1423_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1424_; 
lean_dec(v_origOptionName_1400_);
v___x_1424_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1409_ = v___x_1424_;
goto v___jp_1408_;
}
v___jp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1404_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__1);
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v___y_1402_);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___y_1403_);
v___x_1407_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1399_, v___x_1406_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_option_1399_);
return v___x_1407_;
}
v___jp_1408_:
{
if (lean_obj_tag(v_structName_x3f_1391_) == 1)
{
lean_object* v_val_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_val_1410_ = lean_ctor_get(v_structName_x3f_1391_, 0);
lean_inc(v_val_1410_);
lean_dec_ref_known(v_structName_x3f_1391_, 1);
v___x_1411_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1412_ = 0;
v___x_1413_ = l_Lean_MessageData_ofConstName(v_val_1410_, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1411_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___y_1402_ = v___y_1409_;
v___y_1403_ = v___x_1416_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_structName_x3f_1391_);
v___x_1417_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1402_ = v___y_1409_;
v___y_1403_ = v___x_1417_;
goto v___jp_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___boxed(lean_object* v_item_1425_, lean_object* v_structName_x3f_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1425_, v_structName_x3f_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(lean_object* v_00_u03b1_1435_, lean_object* v_item_1436_, lean_object* v_structName_x3f_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1436_, v_structName_x3f_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___boxed(lean_object* v_00_u03b1_1446_, lean_object* v_item_1447_, lean_object* v_structName_x3f_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption(v_00_u03b1_1446_, v_item_1447_, v_structName_x3f_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
return v_res_1456_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__0));
v___x_1459_ = l_Lean_stringToMessageData(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__2));
v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(lean_object* v_item_1463_, lean_object* v_structName_x3f_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_option_1472_; lean_object* v_origOptionName_1473_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1484_; uint8_t v___x_1493_; 
v_option_1472_ = lean_ctor_get(v_item_1463_, 1);
lean_inc(v_option_1472_);
v_origOptionName_1473_ = lean_ctor_get(v_item_1463_, 4);
lean_inc(v_origOptionName_1473_);
lean_dec_ref(v_item_1463_);
v___x_1493_ = l_Lean_Name_isAnonymous(v_origOptionName_1473_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1494_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__5);
v___x_1495_ = l_Lean_MessageData_ofName(v_origOptionName_1473_);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___y_1484_ = v___x_1498_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1499_; 
lean_dec(v_origOptionName_1473_);
v___x_1499_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1484_ = v___x_1499_;
goto v___jp_1483_;
}
v___jp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1477_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__1);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___y_1475_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___y_1476_);
v___x_1480_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___closed__3);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_option_1472_, v___x_1481_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_option_1472_);
return v___x_1482_;
}
v___jp_1483_:
{
if (lean_obj_tag(v_structName_x3f_1464_) == 1)
{
lean_object* v_val_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_val_1485_ = lean_ctor_get(v_structName_x3f_1464_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v_structName_x3f_1464_, 1);
v___x_1486_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3, &l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg___closed__3);
v___x_1487_ = 0;
v___x_1488_ = l_Lean_MessageData_ofConstName(v_val_1485_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1486_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___y_1475_ = v___y_1484_;
v___y_1476_ = v___x_1491_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_structName_x3f_1464_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__30);
v___y_1475_ = v___y_1484_;
v___y_1476_ = v___x_1492_;
goto v___jp_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg___boxed(lean_object* v_item_1500_, lean_object* v_structName_x3f_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1500_, v_structName_x3f_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(lean_object* v_00_u03b1_1510_, lean_object* v_item_1511_, lean_object* v_structName_x3f_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___redArg(v_item_1511_, v_structName_x3f_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_item_1522_, lean_object* v_structName_x3f_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Elab_ConfigEval_ConfigItem_throwCannotSetOption(v_00_u03b1_1521_, v_item_1522_, v_structName_x3f_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
lean_ctor_set(v___x_1537_, 2, v___x_1536_);
lean_ctor_set(v___x_1537_, 3, v___x_1536_);
lean_ctor_set(v___x_1537_, 4, v___x_1535_);
lean_ctor_set(v___x_1537_, 5, v___x_1535_);
lean_ctor_set(v___x_1537_, 6, v___x_1535_);
lean_ctor_set(v___x_1537_, 7, v___x_1535_);
lean_ctor_set(v___x_1537_, 8, v___x_1535_);
lean_ctor_set(v___x_1537_, 9, v___x_1535_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_unsigned_to_nat(32u);
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1538_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1541_ = ((size_t)5ULL);
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_unsigned_to_nat(32u);
v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
v___x_1545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1546_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1544_);
lean_ctor_set(v___x_1546_, 2, v___x_1542_);
lean_ctor_set(v___x_1546_, 3, v___x_1542_);
lean_ctor_set_usize(v___x_1546_, 4, v___x_1541_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1547_ = lean_box(1);
v___x_1548_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1548_);
lean_ctor_set(v___x_1550_, 2, v___x_1547_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1556_ = l_Lean_stringToMessageData(v___x_1555_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_1568_ = l_Lean_stringToMessageData(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1572_, lean_object* v_declHint_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; lean_object* v_env_1577_; uint8_t v___x_1578_; 
v___x_1576_ = lean_st_ref_get(v___y_1574_);
v_env_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc_ref(v_env_1577_);
lean_dec(v___x_1576_);
v___x_1578_ = l_Lean_Name_isAnonymous(v_declHint_1573_);
if (v___x_1578_ == 0)
{
uint8_t v_isExporting_1579_; 
v_isExporting_1579_ = lean_ctor_get_uint8(v_env_1577_, sizeof(void*)*8);
if (v_isExporting_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v_env_1577_);
lean_dec(v_declHint_1573_);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_msg_1572_);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
lean_inc_ref(v_env_1577_);
v___x_1581_ = l_Lean_Environment_setExporting(v_env_1577_, v___x_1578_);
lean_inc(v_declHint_1573_);
lean_inc_ref(v___x_1581_);
v___x_1582_ = l_Lean_Environment_contains(v___x_1581_, v_declHint_1573_, v_isExporting_1579_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v___x_1581_);
lean_dec_ref(v_env_1577_);
lean_dec(v_declHint_1573_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_msg_1572_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_c_1589_; lean_object* v___x_1590_; 
v___x_1584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1585_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1586_ = l_Lean_Options_empty;
v___x_1587_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1581_);
lean_ctor_set(v___x_1587_, 1, v___x_1584_);
lean_ctor_set(v___x_1587_, 2, v___x_1585_);
lean_ctor_set(v___x_1587_, 3, v___x_1586_);
lean_inc(v_declHint_1573_);
v___x_1588_ = l_Lean_MessageData_ofConstName(v_declHint_1573_, v___x_1578_);
v_c_1589_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1589_, 0, v___x_1587_);
lean_ctor_set(v_c_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1577_, v_declHint_1573_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec_ref(v_env_1577_);
lean_dec(v_declHint_1573_);
v___x_1591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v_c_1589_);
v___x_1593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_MessageData_note(v___x_1594_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_msg_1572_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1633_; 
v_val_1598_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1600_ = v___x_1590_;
v_isShared_1601_ = v_isSharedCheck_1633_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v___x_1590_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1633_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_mod_1605_; uint8_t v___x_1606_; 
v___x_1602_ = lean_box(0);
v___x_1603_ = l_Lean_Environment_header(v_env_1577_);
lean_dec_ref(v_env_1577_);
v___x_1604_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1603_);
v_mod_1605_ = lean_array_get(v___x_1602_, v___x_1604_, v_val_1598_);
lean_dec(v_val_1598_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = l_Lean_isPrivateName(v_declHint_1573_);
lean_dec(v_declHint_1573_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_c_1589_);
v___x_1609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_MessageData_ofName(v_mod_1605_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_MessageData_note(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_msg_1572_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1616_);
v___x_1618_ = v___x_1600_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v_c_1589_);
v___x_1622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_MessageData_ofName(v_mod_1605_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l_Lean_MessageData_note(v___x_1627_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_msg_1572_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1629_);
v___x_1631_ = v___x_1600_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1634_; 
lean_dec_ref(v_env_1577_);
lean_dec(v_declHint_1573_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_msg_1572_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1635_, lean_object* v_declHint_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1635_, v_declHint_1636_, v___y_1637_);
lean_dec(v___y_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_1640_, lean_object* v_declHint_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1659_; 
v___x_1649_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1640_, v_declHint_1641_, v___y_1647_);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1654_ = l_Lean_unknownIdentifierMessageTag;
v___x_1655_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v_a_1650_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1655_);
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_1660_, lean_object* v_declHint_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1660_, v_declHint_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_1670_, lean_object* v_msg_1671_, lean_object* v_declHint_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1682_; 
v___x_1680_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_1671_, v_declHint_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0___redArg(v_ref_1670_, v_a_1681_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1683_, lean_object* v_msg_1684_, lean_object* v_declHint_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1683_, v_msg_1684_, v_declHint_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v_ref_1683_);
return v_res_1693_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1696_ = l_Lean_stringToMessageData(v___x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_1697_, lean_object* v_constName_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1706_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1707_ = 0;
lean_inc(v_constName_1698_);
v___x_1708_ = l_Lean_MessageData_ofConstName(v_constName_1698_, v___x_1707_);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1706_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28, &l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__28);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_1697_, v___x_1711_, v_constName_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_1713_, lean_object* v_constName_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1713_, v_constName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v_ref_1713_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_ref_1731_; lean_object* v___x_1732_; 
v_ref_1731_ = lean_ctor_get(v___y_1728_, 5);
v___x_1732_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_1731_, v_constName_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(lean_object* v_constName_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v_env_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = lean_st_ref_get(v___y_1748_);
v_env_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_env_1751_);
lean_dec(v___x_1750_);
v___x_1752_ = 0;
lean_inc(v_constName_1742_);
v___x_1753_ = l_Lean_Environment_findConstVal_x3f(v_env_1751_, v_constName_1742_, v___x_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1754_;
}
else
{
lean_object* v_val_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_constName_1742_);
v_val_1755_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1753_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_val_1755_);
lean_dec(v___x_1753_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 0);
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_val_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = l_List_reverse___redArg(v_a_1773_);
return v___x_1774_;
}
else
{
lean_object* v_head_1775_; lean_object* v_tail_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1785_; 
v_head_1775_ = lean_ctor_get(v_a_1772_, 0);
v_tail_1776_ = lean_ctor_get(v_a_1772_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1778_ = v_a_1772_;
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_tail_1776_);
lean_inc(v_head_1775_);
lean_dec(v_a_1772_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = l_Lean_mkLevelParam(v_head_1775_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 1, v_a_1773_);
lean_ctor_set(v___x_1778_, 0, v___x_1780_);
v___x_1782_ = v___x_1778_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_a_1773_);
v___x_1782_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
v_a_1772_ = v_tail_1776_;
v_a_1773_ = v___x_1782_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(lean_object* v_constName_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
lean_inc(v_constName_1786_);
v___x_1794_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1(v_constName_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1806_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1806_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1806_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_levelParams_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v_levelParams_1799_ = lean_ctor_get(v_a_1795_, 1);
lean_inc(v_levelParams_1799_);
lean_dec(v_a_1795_);
v___x_1800_ = lean_box(0);
v___x_1801_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__2(v_levelParams_1799_, v___x_1800_);
v___x_1802_ = l_Lean_mkConst(v_constName_1786_, v___x_1801_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1802_);
v___x_1804_ = v___x_1797_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_constName_1786_);
v_a_1807_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1794_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1794_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0___boxed(lean_object* v_constName_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_constName_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v_infoState_1828_; uint8_t v_enabled_1829_; 
v___x_1827_ = lean_st_ref_get(v___y_1825_);
v_infoState_1828_ = lean_ctor_get(v___x_1827_, 7);
lean_inc_ref(v_infoState_1828_);
lean_dec(v___x_1827_);
v_enabled_1829_ = lean_ctor_get_uint8(v_infoState_1828_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1828_);
if (v_enabled_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_t_1824_);
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; lean_object* v_infoState_1833_; lean_object* v_env_1834_; lean_object* v_nextMacroScope_1835_; lean_object* v_ngen_1836_; lean_object* v_auxDeclNGen_1837_; lean_object* v_traceState_1838_; lean_object* v_cache_1839_; lean_object* v_messages_1840_; lean_object* v_snapshotTasks_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1863_; 
v___x_1832_ = lean_st_ref_take(v___y_1825_);
v_infoState_1833_ = lean_ctor_get(v___x_1832_, 7);
v_env_1834_ = lean_ctor_get(v___x_1832_, 0);
v_nextMacroScope_1835_ = lean_ctor_get(v___x_1832_, 1);
v_ngen_1836_ = lean_ctor_get(v___x_1832_, 2);
v_auxDeclNGen_1837_ = lean_ctor_get(v___x_1832_, 3);
v_traceState_1838_ = lean_ctor_get(v___x_1832_, 4);
v_cache_1839_ = lean_ctor_get(v___x_1832_, 5);
v_messages_1840_ = lean_ctor_get(v___x_1832_, 6);
v_snapshotTasks_1841_ = lean_ctor_get(v___x_1832_, 8);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1843_ = v___x_1832_;
v_isShared_1844_ = v_isSharedCheck_1863_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snapshotTasks_1841_);
lean_inc(v_infoState_1833_);
lean_inc(v_messages_1840_);
lean_inc(v_cache_1839_);
lean_inc(v_traceState_1838_);
lean_inc(v_auxDeclNGen_1837_);
lean_inc(v_ngen_1836_);
lean_inc(v_nextMacroScope_1835_);
lean_inc(v_env_1834_);
lean_dec(v___x_1832_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1863_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
uint8_t v_enabled_1845_; lean_object* v_assignment_1846_; lean_object* v_lazyAssignment_1847_; lean_object* v_trees_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1862_; 
v_enabled_1845_ = lean_ctor_get_uint8(v_infoState_1833_, sizeof(void*)*3);
v_assignment_1846_ = lean_ctor_get(v_infoState_1833_, 0);
v_lazyAssignment_1847_ = lean_ctor_get(v_infoState_1833_, 1);
v_trees_1848_ = lean_ctor_get(v_infoState_1833_, 2);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_infoState_1833_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1850_ = v_infoState_1833_;
v_isShared_1851_ = v_isSharedCheck_1862_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_trees_1848_);
lean_inc(v_lazyAssignment_1847_);
lean_inc(v_assignment_1846_);
lean_dec(v_infoState_1833_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1862_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = l_Lean_PersistentArray_push___redArg(v_trees_1848_, v_t_1824_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 2, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_assignment_1846_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_lazyAssignment_1847_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v___x_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*3, v_enabled_1845_);
v___x_1854_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 7, v___x_1854_);
v___x_1856_ = v___x_1843_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_env_1834_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_nextMacroScope_1835_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_ngen_1836_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_auxDeclNGen_1837_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_traceState_1838_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_cache_1839_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_messages_1840_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v_snapshotTasks_1841_);
v___x_1856_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_st_ref_set(v___y_1825_, v___x_1856_);
v___x_1858_ = lean_box(0);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1864_, v___y_1865_);
lean_dec(v___y_1865_);
return v_res_1867_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_unsigned_to_nat(32u);
v___x_1869_ = lean_mk_empty_array_with_capacity(v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1871_ = ((size_t)5ULL);
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = lean_unsigned_to_nat(32u);
v___x_1874_ = lean_mk_empty_array_with_capacity(v___x_1873_);
v___x_1875_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__0);
v___x_1876_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1874_);
lean_ctor_set(v___x_1876_, 2, v___x_1872_);
lean_ctor_set(v___x_1876_, 3, v___x_1872_);
lean_ctor_set_usize(v___x_1876_, 4, v___x_1871_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(lean_object* v_t_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; lean_object* v_infoState_1886_; uint8_t v_enabled_1887_; 
v___x_1885_ = lean_st_ref_get(v___y_1883_);
v_infoState_1886_ = lean_ctor_get(v___x_1885_, 7);
lean_inc_ref(v_infoState_1886_);
lean_dec(v___x_1885_);
v_enabled_1887_ = lean_ctor_get_uint8(v_infoState_1886_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1886_);
if (v_enabled_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_t_1877_);
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
v___x_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_t_1877_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v___x_1891_, v___y_1883_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___boxed(lean_object* v_t_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v_t_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(lean_object* v_stx_1902_, lean_object* v_n_1903_, lean_object* v_expectedType_x3f_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0(v_n_1903_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_stx_1902_);
v___x_1916_ = l_Lean_LocalContext_empty;
v___x_1917_ = 0;
v___x_1918_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1918_, 0, v___x_1915_);
lean_ctor_set(v___x_1918_, 1, v___x_1916_);
lean_ctor_set(v___x_1918_, 2, v_expectedType_x3f_1904_);
lean_ctor_set(v___x_1918_, 3, v_a_1913_);
lean_ctor_set_uint8(v___x_1918_, sizeof(void*)*4, v___x_1917_);
lean_ctor_set_uint8(v___x_1918_, sizeof(void*)*4 + 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
v___x_1920_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_1919_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1920_;
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_expectedType_x3f_1904_);
lean_dec(v_stx_1902_);
v_a_1921_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1912_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1912_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0___boxed(lean_object* v_stx_1929_, lean_object* v_n_1930_, lean_object* v_expectedType_x3f_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v_stx_1929_, v_n_1930_, v_expectedType_x3f_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object* v_item_1940_, lean_object* v_projFn_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v___x_1949_; lean_object* v_infoState_1950_; uint8_t v_enabled_1951_; 
v___x_1949_ = lean_st_ref_get(v_a_1947_);
v_infoState_1950_ = lean_ctor_get(v___x_1949_, 7);
lean_inc_ref(v_infoState_1950_);
lean_dec(v___x_1949_);
v_enabled_1951_ = lean_ctor_get_uint8(v_infoState_1950_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1950_);
if (v_enabled_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v_projFn_1941_);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v_env_1955_; uint8_t v___x_1956_; 
v___x_1954_ = lean_st_ref_get(v_a_1947_);
v_env_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc_ref(v_env_1955_);
lean_dec(v___x_1954_);
lean_inc(v_projFn_1941_);
v___x_1956_ = l_Lean_Environment_contains(v_env_1955_, v_projFn_1941_, v_enabled_1951_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v_projFn_1941_);
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_1940_);
v___x_1960_ = lean_box(0);
v___x_1961_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0(v___x_1959_, v_projFn_1941_, v___x_1960_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
return v___x_1961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo___boxed(lean_object* v_item_1962_, lean_object* v_projFn_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1962_, v_projFn_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec_ref(v_item_1962_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(lean_object* v_t_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___redArg(v_t_1972_, v___y_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1_spec__4(v_t_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1990_, lean_object* v_constName_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_1999_;
}
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2010_, lean_object* v_ref_2011_, lean_object* v_constName_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2011_, v_constName_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2021_, lean_object* v_ref_2022_, lean_object* v_constName_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2021_, v_ref_2022_, v_constName_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v_ref_2022_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2032_, lean_object* v_ref_2033_, lean_object* v_msg_2034_, lean_object* v_declHint_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2033_, v_msg_2034_, v_declHint_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2044_, lean_object* v_ref_2045_, lean_object* v_msg_2046_, lean_object* v_declHint_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2044_, v_ref_2045_, v_msg_2046_, v_declHint_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v_ref_2045_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2056_, lean_object* v_declHint_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2056_, v_declHint_2057_, v___y_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2066_, lean_object* v_declHint_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2066_, v_declHint_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(lean_object* v_info_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_info_2076_);
v___x_2085_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1(v___x_2084_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0___boxed(lean_object* v_info_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v_info_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2094_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0(void){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__0);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2098_ = lean_box(1);
v___x_2099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2100_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_2101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2099_);
lean_ctor_set(v___x_2101_, 2, v___x_2098_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object* v_item_2102_, lean_object* v_structName_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v_infoState_2112_; uint8_t v_enabled_2113_; 
v___x_2111_ = lean_st_ref_get(v_a_2109_);
v_infoState_2112_ = lean_ctor_get(v___x_2111_, 7);
lean_inc_ref(v_infoState_2112_);
lean_dec(v___x_2111_);
v_enabled_2113_ = lean_ctor_get_uint8(v_infoState_2112_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2112_);
if (v_enabled_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v_structName_2103_);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; lean_object* v_env_2117_; uint8_t v___x_2118_; 
v___x_2116_ = lean_st_ref_get(v_a_2109_);
v_env_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_ref(v_env_2117_);
lean_dec(v___x_2116_);
lean_inc(v_structName_2103_);
v___x_2118_ = l_Lean_Environment_contains(v_env_2117_, v_structName_2103_, v_enabled_2113_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec(v_structName_2103_);
v___x_2119_ = lean_box(0);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2121_ = l_Lean_Elab_ConfigEval_ConfigItem_root(v_item_2102_);
v___x_2122_ = l_Lean_Syntax_getId(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
v___x_2124_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2);
v___x_2125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2121_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
lean_ctor_set(v___x_2125_, 2, v___x_2124_);
lean_ctor_set(v___x_2125_, 3, v_structName_2103_);
v___x_2126_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2125_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___boxed(lean_object* v_item_2127_, lean_object* v_structName_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_2127_, v_structName_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec_ref(v_item_2127_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(lean_object* v_cfg_2137_, lean_object* v_withRef_2138_, lean_object* v___x_2139_, lean_object* v_oldRef_2140_){
_start:
{
lean_object* v_ref_2141_; lean_object* v___x_2142_; 
v_ref_2141_ = l_Lean_replaceRef(v_cfg_2137_, v_oldRef_2140_);
v___x_2142_ = lean_apply_3(v_withRef_2138_, lean_box(0), v_ref_2141_, v___x_2139_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed(lean_object* v_cfg_2143_, lean_object* v_withRef_2144_, lean_object* v___x_2145_, lean_object* v_oldRef_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0(v_cfg_2143_, v_withRef_2144_, v___x_2145_, v_oldRef_2146_);
lean_dec(v_oldRef_2146_);
lean_dec(v_cfg_2143_);
return v_res_2147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(uint32_t v_x_2148_){
_start:
{
uint32_t v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = 46;
v___x_2150_ = lean_uint32_dec_eq(v_x_2148_, v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1___boxed(lean_object* v_x_2151_){
_start:
{
uint32_t v_x_1685__boxed_2152_; uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_x_1685__boxed_2152_ = lean_unbox_uint32(v_x_2151_);
lean_dec(v_x_2151_);
v_res_2153_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__1(v_x_1685__boxed_2152_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__2(lean_object* v___f_2155_, lean_object* v_s_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2155_);
v___x_2164_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2156_, v___x_2163_, v___y_2157_, lean_box(0), lean_box(0), v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(lean_object* v___f_2166_, lean_object* v_si_2167_, lean_object* v_val_2168_){
_start:
{
lean_object* v___y_2170_; lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___f_2176_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3___closed__0));
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = lean_string_utf8_byte_size(v_val_2168_);
lean_inc_ref(v_val_2168_);
v___x_2179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2179_, 0, v_val_2168_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
lean_ctor_set(v___x_2179_, 2, v___x_2178_);
v___x_2180_ = l_String_Slice_contains___redArg(v___f_2166_, v___x_2179_, v___f_2176_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_box(0);
lean_inc_ref(v_val_2168_);
v___x_2182_ = l_Lean_Name_str___override(v___x_2181_, v_val_2168_);
v___y_2170_ = v___x_2182_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2183_; 
lean_inc_ref(v_val_2168_);
v___x_2183_ = l_String_toName(v_val_2168_);
v___y_2170_ = v___x_2183_;
goto v___jp_2169_;
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_string_utf8_byte_size(v_val_2168_);
v___x_2173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2173_, 0, v_val_2168_);
lean_ctor_set(v___x_2173_, 1, v___x_2171_);
lean_ctor_set(v___x_2173_, 2, v___x_2172_);
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2175_, 0, v_si_2167_);
lean_ctor_set(v___x_2175_, 1, v___x_2173_);
lean_ctor_set(v___x_2175_, 2, v___y_2170_);
lean_ctor_set(v___x_2175_, 3, v___x_2174_);
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(lean_object* v_atomAsIdent_2184_, lean_object* v_stx_2185_){
_start:
{
switch(lean_obj_tag(v_stx_2185_))
{
case 3:
{
lean_object* v___x_2186_; 
lean_dec_ref(v_atomAsIdent_2184_);
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_stx_2185_);
return v___x_2186_;
}
case 2:
{
lean_object* v_info_2187_; lean_object* v_val_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_info_2187_ = lean_ctor_get(v_stx_2185_, 0);
lean_inc(v_info_2187_);
v_val_2188_ = lean_ctor_get(v_stx_2185_, 1);
lean_inc_ref(v_val_2188_);
lean_dec_ref_known(v_stx_2185_, 2);
v___x_2189_ = lean_apply_2(v_atomAsIdent_2184_, v_info_2187_, v_val_2188_);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
default: 
{
lean_object* v___x_2191_; 
lean_dec(v_stx_2185_);
lean_dec_ref(v_atomAsIdent_2184_);
v___x_2191_ = lean_box(0);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg(lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_init_2217_, lean_object* v_cfgs_2218_, lean_object* v_k_2219_, lean_object* v_onErr_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_array_get_size(v_cfgs_2218_);
v___x_2223_ = lean_nat_dec_lt(v___x_2221_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v_toApplicative_2224_; lean_object* v_toPure_2225_; lean_object* v___x_2226_; 
lean_dec(v_onErr_2220_);
lean_dec(v_k_2219_);
lean_dec_ref(v_cfgs_2218_);
lean_dec_ref(v_inst_2216_);
v_toApplicative_2224_ = lean_ctor_get(v_inst_2215_, 0);
lean_inc_ref(v_toApplicative_2224_);
lean_dec_ref(v_inst_2215_);
v_toPure_2225_ = lean_ctor_get(v_toApplicative_2224_, 1);
lean_inc(v_toPure_2225_);
lean_dec_ref(v_toApplicative_2224_);
v___x_2226_ = lean_apply_2(v_toPure_2225_, lean_box(0), v_init_2217_);
return v___x_2226_;
}
else
{
lean_object* v___f_2227_; uint8_t v___x_2228_; 
lean_inc_ref(v_inst_2215_);
v___f_2227_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0), 6, 4);
lean_closure_set(v___f_2227_, 0, v_inst_2215_);
lean_closure_set(v___f_2227_, 1, v_inst_2216_);
lean_closure_set(v___f_2227_, 2, v_k_2219_);
lean_closure_set(v___f_2227_, 3, v_onErr_2220_);
v___x_2228_ = lean_nat_dec_le(v___x_2222_, v___x_2222_);
if (v___x_2228_ == 0)
{
if (v___x_2223_ == 0)
{
lean_object* v_toApplicative_2229_; lean_object* v_toPure_2230_; lean_object* v___x_2231_; 
lean_dec_ref(v___f_2227_);
lean_dec_ref(v_cfgs_2218_);
v_toApplicative_2229_ = lean_ctor_get(v_inst_2215_, 0);
lean_inc_ref(v_toApplicative_2229_);
lean_dec_ref(v_inst_2215_);
v_toPure_2230_ = lean_ctor_get(v_toApplicative_2229_, 1);
lean_inc(v_toPure_2230_);
lean_dec_ref(v_toApplicative_2229_);
v___x_2231_ = lean_apply_2(v_toPure_2230_, lean_box(0), v_init_2217_);
return v___x_2231_;
}
else
{
size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = lean_usize_of_nat(v___x_2222_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2215_, v___f_2227_, v_cfgs_2218_, v___x_2232_, v___x_2233_, v_init_2217_);
return v___x_2234_;
}
}
else
{
size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = lean_usize_of_nat(v___x_2222_);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2215_, v___f_2227_, v_cfgs_2218_, v___x_2235_, v___x_2236_, v_init_2217_);
return v___x_2237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___redArg(lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_init_2240_, lean_object* v_cfg_2241_, lean_object* v_k_2242_, lean_object* v_onErr_2243_){
_start:
{
lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_2241_);
v___x_2263_ = l_Lean_Syntax_isOfKind(v_cfg_2241_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2264_ = l_Lean_Syntax_getNumArgs(v_cfg_2241_);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = lean_nat_dec_eq(v___x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___f_2267_; lean_object* v_atomAsIdent_2268_; uint8_t v___x_2269_; 
v___f_2267_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__3));
v_atomAsIdent_2268_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__4));
v___x_2269_ = lean_nat_dec_le(v___x_2265_, v___x_2264_);
if (v___x_2269_ == 0)
{
lean_dec(v___x_2264_);
if (lean_obj_tag(v_cfg_2241_) == 2)
{
lean_object* v_info_2270_; lean_object* v_val_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v_onErr_2243_);
lean_dec_ref(v_inst_2239_);
lean_dec_ref(v_inst_2238_);
v_info_2270_ = lean_ctor_get(v_cfg_2241_, 0);
v_val_2271_ = lean_ctor_get(v_cfg_2241_, 1);
lean_inc_ref(v_val_2271_);
lean_inc(v_info_2270_);
v___x_2272_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__3(v___f_2267_, v_info_2270_, v_val_2271_);
v___x_2273_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2274_ = l_Lean_mkCIdentFrom(v_cfg_2241_, v___x_2273_, v___x_2266_);
v___x_2275_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_2276_ = l_Lean_TSyntax_getId(v___x_2272_);
v___x_2277_ = lean_erase_macro_scopes(v___x_2276_);
v___x_2278_ = lean_box(0);
lean_inc(v___x_2272_);
v___x_2279_ = l_Lean_Syntax_identComponents(v___x_2272_, v___x_2278_);
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2281_, 0, v_cfg_2241_);
lean_ctor_set(v___x_2281_, 1, v___x_2272_);
lean_ctor_set(v___x_2281_, 2, v___x_2274_);
lean_ctor_set(v___x_2281_, 3, v___x_2275_);
lean_ctor_set(v___x_2281_, 4, v___x_2277_);
lean_ctor_set(v___x_2281_, 5, v___x_2279_);
lean_ctor_set(v___x_2281_, 6, v___x_2280_);
v___x_2282_ = lean_apply_2(v_k_2242_, v_init_2240_, v___x_2281_);
return v___x_2282_;
}
else
{
lean_dec(v_k_2242_);
goto v___jp_2255_;
}
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = l_Lean_Syntax_getArg(v_cfg_2241_, v___x_2283_);
if (lean_obj_tag(v___x_2284_) == 2)
{
lean_object* v_val_2285_; lean_object* v___y_2287_; uint8_t v_val_2288_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_val_2285_ = lean_ctor_get(v___x_2284_, 1);
lean_inc_ref(v_val_2285_);
v___x_2299_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_2300_ = lean_string_dec_eq(v_val_2285_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_2302_ = lean_string_dec_eq(v_val_2285_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
lean_dec_ref_known(v___x_2284_, 2);
v___x_2303_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_2304_ = lean_string_dec_eq(v_val_2285_, v___x_2303_);
lean_dec_ref(v_val_2285_);
if (v___x_2304_ == 0)
{
lean_dec(v___x_2264_);
lean_dec(v_k_2242_);
goto v___jp_2255_;
}
else
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = lean_unsigned_to_nat(5u);
v___x_2306_ = lean_nat_dec_le(v___x_2264_, v___x_2305_);
lean_dec(v___x_2264_);
if (v___x_2306_ == 0)
{
lean_dec(v_k_2242_);
goto v___jp_2255_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = l_Lean_Syntax_getArg(v_cfg_2241_, v___x_2265_);
v___x_2308_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2268_, v___x_2307_);
if (lean_obj_tag(v___x_2308_) == 1)
{
lean_object* v_val_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec(v_onErr_2243_);
lean_dec_ref(v_inst_2239_);
lean_dec_ref(v_inst_2238_);
v_val_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_n(v_val_2309_, 2);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = lean_unsigned_to_nat(3u);
v___x_2311_ = l_Lean_Syntax_getArg(v_cfg_2241_, v___x_2310_);
v___x_2312_ = lean_box(0);
v___x_2313_ = l_Lean_TSyntax_getId(v_val_2309_);
v___x_2314_ = lean_erase_macro_scopes(v___x_2313_);
v___x_2315_ = l_Lean_Syntax_identComponents(v_val_2309_, v___x_2312_);
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2317_, 0, v_cfg_2241_);
lean_ctor_set(v___x_2317_, 1, v_val_2309_);
lean_ctor_set(v___x_2317_, 2, v___x_2311_);
lean_ctor_set(v___x_2317_, 3, v___x_2312_);
lean_ctor_set(v___x_2317_, 4, v___x_2314_);
lean_ctor_set(v___x_2317_, 5, v___x_2315_);
lean_ctor_set(v___x_2317_, 6, v___x_2316_);
v___x_2318_ = lean_apply_2(v_k_2242_, v_init_2240_, v___x_2317_);
return v___x_2318_;
}
else
{
lean_dec(v___x_2308_);
lean_dec(v_k_2242_);
goto v___jp_2255_;
}
}
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec_ref(v_val_2285_);
v___x_2319_ = lean_box(v___x_2266_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
v___y_2287_ = v___x_2320_;
v_val_2288_ = v___x_2266_;
goto v___jp_2286_;
}
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec_ref(v_val_2285_);
v___x_2321_ = lean_box(v___x_2300_);
v___x_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
v___y_2287_ = v___x_2322_;
v_val_2288_ = v___x_2300_;
goto v___jp_2286_;
}
v___jp_2286_:
{
lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = lean_unsigned_to_nat(2u);
v___x_2290_ = lean_nat_dec_eq(v___x_2264_, v___x_2289_);
lean_dec(v___x_2264_);
if (v___x_2290_ == 0)
{
lean_dec(v___y_2287_);
lean_dec_ref_known(v___x_2284_, 2);
lean_dec(v_k_2242_);
goto v___jp_2255_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = l_Lean_Syntax_getArg(v_cfg_2241_, v___x_2265_);
v___x_2292_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_2268_, v___x_2291_);
if (lean_obj_tag(v___x_2292_) == 1)
{
lean_dec(v_onErr_2243_);
lean_dec_ref(v_inst_2239_);
lean_dec_ref(v_inst_2238_);
if (v_val_2288_ == 0)
{
lean_object* v_val_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v_val_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_2295_ = l_Lean_mkCIdentFrom(v___x_2284_, v___x_2294_, v___x_2266_);
lean_dec_ref_known(v___x_2284_, 2);
v___y_2245_ = v_val_2293_;
v___y_2246_ = v___y_2287_;
v___y_2247_ = v___x_2295_;
goto v___jp_2244_;
}
else
{
lean_object* v_val_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_val_2296_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2297_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_2298_ = l_Lean_mkCIdentFrom(v___x_2284_, v___x_2297_, v___x_2266_);
lean_dec_ref_known(v___x_2284_, 2);
v___y_2245_ = v_val_2296_;
v___y_2246_ = v___y_2287_;
v___y_2247_ = v___x_2298_;
goto v___jp_2244_;
}
}
else
{
lean_dec(v___x_2292_);
lean_dec(v___y_2287_);
lean_dec_ref_known(v___x_2284_, 2);
lean_dec(v_k_2242_);
goto v___jp_2255_;
}
}
}
}
else
{
lean_dec(v___x_2284_);
lean_dec(v___x_2264_);
lean_dec(v_k_2242_);
goto v___jp_2255_;
}
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec(v___x_2264_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = l_Lean_Syntax_getArg(v_cfg_2241_, v___x_2323_);
lean_dec(v_cfg_2241_);
v_cfg_2241_ = v___x_2324_;
goto _start;
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = l_Lean_Syntax_getArgs(v_cfg_2241_);
lean_dec(v_cfg_2241_);
v___x_2327_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2238_, v_inst_2239_, v_init_2240_, v___x_2326_, v_k_2242_, v_onErr_2243_);
return v___x_2327_;
}
v___jp_2244_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2248_ = l_Lean_TSyntax_getId(v___y_2245_);
v___x_2249_ = lean_erase_macro_scopes(v___x_2248_);
v___x_2250_ = lean_box(0);
lean_inc(v___y_2245_);
v___x_2251_ = l_Lean_Syntax_identComponents(v___y_2245_, v___x_2250_);
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2253_, 0, v_cfg_2241_);
lean_ctor_set(v___x_2253_, 1, v___y_2245_);
lean_ctor_set(v___x_2253_, 2, v___y_2247_);
lean_ctor_set(v___x_2253_, 3, v___y_2246_);
lean_ctor_set(v___x_2253_, 4, v___x_2249_);
lean_ctor_set(v___x_2253_, 5, v___x_2251_);
lean_ctor_set(v___x_2253_, 6, v___x_2252_);
v___x_2254_ = lean_apply_2(v_k_2242_, v_init_2240_, v___x_2253_);
return v___x_2254_;
}
v___jp_2255_:
{
lean_object* v_toBind_2256_; lean_object* v_getRef_2257_; lean_object* v_withRef_2258_; lean_object* v___x_2259_; lean_object* v___f_2260_; lean_object* v___x_2261_; 
v_toBind_2256_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2256_);
lean_dec_ref(v_inst_2238_);
v_getRef_2257_ = lean_ctor_get(v_inst_2239_, 0);
lean_inc(v_getRef_2257_);
v_withRef_2258_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_withRef_2258_);
lean_dec_ref(v_inst_2239_);
lean_inc(v_cfg_2241_);
v___x_2259_ = lean_apply_2(v_onErr_2243_, v_init_2240_, v_cfg_2241_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2260_, 0, v_cfg_2241_);
lean_closure_set(v___f_2260_, 1, v_withRef_2258_);
lean_closure_set(v___f_2260_, 2, v___x_2259_);
v___x_2261_ = lean_apply_4(v_toBind_2256_, lean_box(0), lean_box(0), v_getRef_2257_, v___f_2260_);
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___redArg___lam__0(lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_k_2330_, lean_object* v_onErr_2331_, lean_object* v_x_2332_, lean_object* v_cfg_x27_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2328_, v_inst_2329_, v_x_2332_, v_cfg_x27_2333_, v_k_2330_, v_onErr_2331_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM(lean_object* v_00_u03b1_2335_, lean_object* v_m_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_init_2339_, lean_object* v_cfg_2340_, lean_object* v_k_2341_, lean_object* v_onErr_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg(v_inst_2337_, v_inst_2338_, v_init_2339_, v_cfg_2340_, v_k_2341_, v_onErr_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM(lean_object* v_00_u03b1_2344_, lean_object* v_m_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_init_2348_, lean_object* v_cfgs_2349_, lean_object* v_k_2350_, lean_object* v_onErr_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Elab_ConfigEval_foldConfigsM___redArg(v_inst_2346_, v_inst_2347_, v_init_2348_, v_cfgs_2349_, v_k_2350_, v_onErr_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v___y_2361_, uint8_t v_suppressElabErrors_2362_, lean_object* v_x_2363_){
_start:
{
if (lean_obj_tag(v_x_2363_) == 1)
{
lean_object* v_pre_2364_; 
v_pre_2364_ = lean_ctor_get(v_x_2363_, 0);
switch(lean_obj_tag(v_pre_2364_))
{
case 1:
{
lean_object* v_pre_2365_; 
v_pre_2365_ = lean_ctor_get(v_pre_2364_, 0);
switch(lean_obj_tag(v_pre_2365_))
{
case 0:
{
lean_object* v_str_2366_; lean_object* v_str_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_str_2366_ = lean_ctor_get(v_x_2363_, 1);
v_str_2367_ = lean_ctor_get(v_pre_2364_, 1);
v___x_2368_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_2369_ = lean_string_dec_eq(v_str_2367_, v___x_2368_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_2371_ = lean_string_dec_eq(v_str_2367_, v___x_2370_);
if (v___x_2371_ == 0)
{
return v___y_2361_;
}
else
{
lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_2373_ = lean_string_dec_eq(v_str_2366_, v___x_2372_);
if (v___x_2373_ == 0)
{
return v___y_2361_;
}
else
{
return v_suppressElabErrors_2362_;
}
}
}
else
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_2375_ = lean_string_dec_eq(v_str_2366_, v___x_2374_);
if (v___x_2375_ == 0)
{
return v___y_2361_;
}
else
{
return v_suppressElabErrors_2362_;
}
}
}
case 1:
{
lean_object* v_pre_2376_; 
v_pre_2376_ = lean_ctor_get(v_pre_2365_, 0);
if (lean_obj_tag(v_pre_2376_) == 0)
{
lean_object* v_str_2377_; lean_object* v_str_2378_; lean_object* v_str_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_str_2377_ = lean_ctor_get(v_x_2363_, 1);
v_str_2378_ = lean_ctor_get(v_pre_2364_, 1);
v_str_2379_ = lean_ctor_get(v_pre_2365_, 1);
v___x_2380_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_2381_ = lean_string_dec_eq(v_str_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
return v___y_2361_;
}
else
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_2383_ = lean_string_dec_eq(v_str_2378_, v___x_2382_);
if (v___x_2383_ == 0)
{
return v___y_2361_;
}
else
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_2385_ = lean_string_dec_eq(v_str_2377_, v___x_2384_);
if (v___x_2385_ == 0)
{
return v___y_2361_;
}
else
{
return v_suppressElabErrors_2362_;
}
}
}
}
else
{
return v___y_2361_;
}
}
default: 
{
return v___y_2361_;
}
}
}
case 0:
{
lean_object* v_str_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v_str_2386_ = lean_ctor_get(v_x_2363_, 1);
v___x_2387_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_2388_ = lean_string_dec_eq(v_str_2386_, v___x_2387_);
if (v___x_2388_ == 0)
{
return v___y_2361_;
}
else
{
return v_suppressElabErrors_2362_;
}
}
default: 
{
return v___y_2361_;
}
}
}
else
{
return v___y_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_2389_, lean_object* v_suppressElabErrors_2390_, lean_object* v_x_2391_){
_start:
{
uint8_t v___y_6697__boxed_2392_; uint8_t v_suppressElabErrors_boxed_2393_; uint8_t v_res_2394_; lean_object* v_r_2395_; 
v___y_6697__boxed_2392_ = lean_unbox(v___y_2389_);
v_suppressElabErrors_boxed_2393_ = lean_unbox(v_suppressElabErrors_2390_);
v_res_2394_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0(v___y_6697__boxed_2392_, v_suppressElabErrors_boxed_2393_, v_x_2391_);
lean_dec(v_x_2391_);
v_r_2395_ = lean_box(v_res_2394_);
return v_r_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2396_, lean_object* v_msgData_2397_, uint8_t v_severity_2398_, uint8_t v_isSilent_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; uint8_t v___y_2409_; lean_object* v___y_2410_; uint8_t v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2442_; lean_object* v___y_2443_; uint8_t v___y_2444_; lean_object* v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2447_; uint8_t v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; uint8_t v___y_2470_; uint8_t v___y_2471_; lean_object* v___y_2472_; uint8_t v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; uint8_t v___y_2484_; uint8_t v___x_2489_; lean_object* v___y_2491_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; uint8_t v___y_2496_; uint8_t v___y_2497_; uint8_t v___y_2499_; uint8_t v___x_2514_; 
v___x_2489_ = 2;
v___x_2514_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2398_, v___x_2489_);
if (v___x_2514_ == 0)
{
v___y_2499_ = v___x_2514_;
goto v___jp_2498_;
}
else
{
uint8_t v___x_2515_; 
lean_inc_ref(v_msgData_2397_);
v___x_2515_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2397_);
v___y_2499_ = v___x_2515_;
goto v___jp_2498_;
}
v___jp_2405_:
{
lean_object* v___x_2415_; lean_object* v_currNamespace_2416_; lean_object* v_openDecls_2417_; lean_object* v_env_2418_; lean_object* v_nextMacroScope_2419_; lean_object* v_ngen_2420_; lean_object* v_auxDeclNGen_2421_; lean_object* v_traceState_2422_; lean_object* v_cache_2423_; lean_object* v_messages_2424_; lean_object* v_infoState_2425_; lean_object* v_snapshotTasks_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2440_; 
v___x_2415_ = lean_st_ref_take(v___y_2414_);
v_currNamespace_2416_ = lean_ctor_get(v___y_2413_, 6);
v_openDecls_2417_ = lean_ctor_get(v___y_2413_, 7);
v_env_2418_ = lean_ctor_get(v___x_2415_, 0);
v_nextMacroScope_2419_ = lean_ctor_get(v___x_2415_, 1);
v_ngen_2420_ = lean_ctor_get(v___x_2415_, 2);
v_auxDeclNGen_2421_ = lean_ctor_get(v___x_2415_, 3);
v_traceState_2422_ = lean_ctor_get(v___x_2415_, 4);
v_cache_2423_ = lean_ctor_get(v___x_2415_, 5);
v_messages_2424_ = lean_ctor_get(v___x_2415_, 6);
v_infoState_2425_ = lean_ctor_get(v___x_2415_, 7);
v_snapshotTasks_2426_ = lean_ctor_get(v___x_2415_, 8);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2428_ = v___x_2415_;
v_isShared_2429_ = v_isSharedCheck_2440_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_snapshotTasks_2426_);
lean_inc(v_infoState_2425_);
lean_inc(v_messages_2424_);
lean_inc(v_cache_2423_);
lean_inc(v_traceState_2422_);
lean_inc(v_auxDeclNGen_2421_);
lean_inc(v_ngen_2420_);
lean_inc(v_nextMacroScope_2419_);
lean_inc(v_env_2418_);
lean_dec(v___x_2415_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2440_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2435_; 
lean_inc(v_openDecls_2417_);
lean_inc(v_currNamespace_2416_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_currNamespace_2416_);
lean_ctor_set(v___x_2430_, 1, v_openDecls_2417_);
v___x_2431_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v___y_2406_);
lean_inc_ref(v___y_2408_);
lean_inc_ref(v___y_2410_);
v___x_2432_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2432_, 0, v___y_2410_);
lean_ctor_set(v___x_2432_, 1, v___y_2407_);
lean_ctor_set(v___x_2432_, 2, v___y_2412_);
lean_ctor_set(v___x_2432_, 3, v___y_2408_);
lean_ctor_set(v___x_2432_, 4, v___x_2431_);
lean_ctor_set_uint8(v___x_2432_, sizeof(void*)*5, v___y_2409_);
lean_ctor_set_uint8(v___x_2432_, sizeof(void*)*5 + 1, v___y_2411_);
lean_ctor_set_uint8(v___x_2432_, sizeof(void*)*5 + 2, v_isSilent_2399_);
v___x_2433_ = l_Lean_MessageLog_add(v___x_2432_, v_messages_2424_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 6, v___x_2433_);
v___x_2435_ = v___x_2428_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_env_2418_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_nextMacroScope_2419_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v_ngen_2420_);
lean_ctor_set(v_reuseFailAlloc_2439_, 3, v_auxDeclNGen_2421_);
lean_ctor_set(v_reuseFailAlloc_2439_, 4, v_traceState_2422_);
lean_ctor_set(v_reuseFailAlloc_2439_, 5, v_cache_2423_);
lean_ctor_set(v_reuseFailAlloc_2439_, 6, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2439_, 7, v_infoState_2425_);
lean_ctor_set(v_reuseFailAlloc_2439_, 8, v_snapshotTasks_2426_);
v___x_2435_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_st_ref_set(v___y_2414_, v___x_2435_);
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
}
}
v___jp_2441_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2465_; 
v___x_2450_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2397_);
v___x_2451_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_EvalExpr_withWHNF_spec__0_spec__0(v___x_2450_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2465_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2465_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_inc_ref_n(v___y_2445_, 2);
v___x_2456_ = l_Lean_FileMap_toPosition(v___y_2445_, v___y_2443_);
lean_dec(v___y_2443_);
v___x_2457_ = l_Lean_FileMap_toPosition(v___y_2445_, v___y_2449_);
lean_dec(v___y_2449_);
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v___x_2459_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___redArg___closed__29));
if (v___y_2444_ == 0)
{
lean_del_object(v___x_2454_);
lean_dec_ref(v___y_2442_);
v___y_2406_ = v_a_2452_;
v___y_2407_ = v___x_2456_;
v___y_2408_ = v___x_2459_;
v___y_2409_ = v___y_2446_;
v___y_2410_ = v___y_2447_;
v___y_2411_ = v___y_2448_;
v___y_2412_ = v___x_2458_;
v___y_2413_ = v___y_2402_;
v___y_2414_ = v___y_2403_;
goto v___jp_2405_;
}
else
{
uint8_t v___x_2460_; 
lean_inc(v_a_2452_);
v___x_2460_ = l_Lean_MessageData_hasTag(v___y_2442_, v_a_2452_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_dec_ref_known(v___x_2458_, 1);
lean_dec_ref(v___x_2456_);
lean_dec(v_a_2452_);
v___x_2461_ = lean_box(0);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2461_);
v___x_2463_ = v___x_2454_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
else
{
lean_del_object(v___x_2454_);
v___y_2406_ = v_a_2452_;
v___y_2407_ = v___x_2456_;
v___y_2408_ = v___x_2459_;
v___y_2409_ = v___y_2446_;
v___y_2410_ = v___y_2447_;
v___y_2411_ = v___y_2448_;
v___y_2412_ = v___x_2458_;
v___y_2413_ = v___y_2402_;
v___y_2414_ = v___y_2403_;
goto v___jp_2405_;
}
}
}
}
v___jp_2466_:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Syntax_getTailPos_x3f(v___y_2468_, v___y_2471_);
lean_dec(v___y_2468_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_inc(v___y_2474_);
v___y_2442_ = v___y_2467_;
v___y_2443_ = v___y_2474_;
v___y_2444_ = v___y_2470_;
v___y_2445_ = v___y_2469_;
v___y_2446_ = v___y_2471_;
v___y_2447_ = v___y_2472_;
v___y_2448_ = v___y_2473_;
v___y_2449_ = v___y_2474_;
goto v___jp_2441_;
}
else
{
lean_object* v_val_2476_; 
v_val_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_val_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v___y_2442_ = v___y_2467_;
v___y_2443_ = v___y_2474_;
v___y_2444_ = v___y_2470_;
v___y_2445_ = v___y_2469_;
v___y_2446_ = v___y_2471_;
v___y_2447_ = v___y_2472_;
v___y_2448_ = v___y_2473_;
v___y_2449_ = v_val_2476_;
goto v___jp_2441_;
}
}
v___jp_2477_:
{
lean_object* v_ref_2485_; lean_object* v___x_2486_; 
v_ref_2485_ = l_Lean_replaceRef(v_ref_2396_, v___y_2483_);
v___x_2486_ = l_Lean_Syntax_getPos_x3f(v_ref_2485_, v___y_2481_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_unsigned_to_nat(0u);
v___y_2467_ = v___y_2478_;
v___y_2468_ = v_ref_2485_;
v___y_2469_ = v___y_2480_;
v___y_2470_ = v___y_2479_;
v___y_2471_ = v___y_2481_;
v___y_2472_ = v___y_2482_;
v___y_2473_ = v___y_2484_;
v___y_2474_ = v___x_2487_;
goto v___jp_2466_;
}
else
{
lean_object* v_val_2488_; 
v_val_2488_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v___x_2486_, 1);
v___y_2467_ = v___y_2478_;
v___y_2468_ = v_ref_2485_;
v___y_2469_ = v___y_2480_;
v___y_2470_ = v___y_2479_;
v___y_2471_ = v___y_2481_;
v___y_2472_ = v___y_2482_;
v___y_2473_ = v___y_2484_;
v___y_2474_ = v_val_2488_;
goto v___jp_2466_;
}
}
v___jp_2490_:
{
if (v___y_2497_ == 0)
{
v___y_2478_ = v___y_2491_;
v___y_2479_ = v___y_2493_;
v___y_2480_ = v___y_2492_;
v___y_2481_ = v___y_2496_;
v___y_2482_ = v___y_2494_;
v___y_2483_ = v___y_2495_;
v___y_2484_ = v_severity_2398_;
goto v___jp_2477_;
}
else
{
v___y_2478_ = v___y_2491_;
v___y_2479_ = v___y_2493_;
v___y_2480_ = v___y_2492_;
v___y_2481_ = v___y_2496_;
v___y_2482_ = v___y_2494_;
v___y_2483_ = v___y_2495_;
v___y_2484_ = v___x_2489_;
goto v___jp_2477_;
}
}
v___jp_2498_:
{
if (v___y_2499_ == 0)
{
lean_object* v_fileName_2500_; lean_object* v_fileMap_2501_; lean_object* v_options_2502_; lean_object* v_ref_2503_; uint8_t v_suppressElabErrors_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___f_2507_; uint8_t v___x_2508_; uint8_t v___x_2509_; 
v_fileName_2500_ = lean_ctor_get(v___y_2402_, 0);
v_fileMap_2501_ = lean_ctor_get(v___y_2402_, 1);
v_options_2502_ = lean_ctor_get(v___y_2402_, 2);
v_ref_2503_ = lean_ctor_get(v___y_2402_, 5);
v_suppressElabErrors_2504_ = lean_ctor_get_uint8(v___y_2402_, sizeof(void*)*14 + 1);
v___x_2505_ = lean_box(v___y_2499_);
v___x_2506_ = lean_box(v_suppressElabErrors_2504_);
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2507_, 0, v___x_2505_);
lean_closure_set(v___f_2507_, 1, v___x_2506_);
v___x_2508_ = 1;
v___x_2509_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2398_, v___x_2508_);
if (v___x_2509_ == 0)
{
v___y_2491_ = v___f_2507_;
v___y_2492_ = v_fileMap_2501_;
v___y_2493_ = v_suppressElabErrors_2504_;
v___y_2494_ = v_fileName_2500_;
v___y_2495_ = v_ref_2503_;
v___y_2496_ = v___y_2499_;
v___y_2497_ = v___x_2509_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = l_Lean_warningAsError;
v___x_2511_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_ConfigItem_checkNotBool_spec__0_spec__0_spec__1_spec__2(v_options_2502_, v___x_2510_);
v___y_2491_ = v___f_2507_;
v___y_2492_ = v_fileMap_2501_;
v___y_2493_ = v_suppressElabErrors_2504_;
v___y_2494_ = v_fileName_2500_;
v___y_2495_ = v_ref_2503_;
v___y_2496_ = v___y_2499_;
v___y_2497_ = v___x_2511_;
goto v___jp_2490_;
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec_ref(v_msgData_2397_);
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2516_, lean_object* v_msgData_2517_, lean_object* v_severity_2518_, lean_object* v_isSilent_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v_severity_boxed_2525_; uint8_t v_isSilent_boxed_2526_; lean_object* v_res_2527_; 
v_severity_boxed_2525_ = lean_unbox(v_severity_2518_);
v_isSilent_boxed_2526_ = lean_unbox(v_isSilent_2519_);
v_res_2527_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2516_, v_msgData_2517_, v_severity_boxed_2525_, v_isSilent_boxed_2526_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v_ref_2516_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(lean_object* v_msgData_2528_, uint8_t v_severity_2529_, uint8_t v_isSilent_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_ref_2538_; lean_object* v___x_2539_; 
v_ref_2538_ = lean_ctor_get(v___y_2535_, 5);
v___x_2539_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2538_, v_msgData_2528_, v_severity_2529_, v_isSilent_2530_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2540_, lean_object* v_severity_2541_, lean_object* v_isSilent_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
uint8_t v_severity_boxed_2550_; uint8_t v_isSilent_boxed_2551_; lean_object* v_res_2552_; 
v_severity_boxed_2550_ = lean_unbox(v_severity_2541_);
v_isSilent_boxed_2551_ = lean_unbox(v_isSilent_2542_);
v_res_2552_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2540_, v_severity_boxed_2550_, v_isSilent_boxed_2551_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(lean_object* v_msgData_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = 2;
v___x_2562_ = 0;
v___x_2563_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1_spec__3(v_msgData_2553_, v___x_2561_, v___x_2562_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
return v___x_2563_;
}
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
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(lean_object* v_ref_2573_, lean_object* v_msgData_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
uint8_t v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = 2;
v___x_2583_ = 0;
v___x_2584_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2573_, v_msgData_2574_, v___x_2582_, v___x_2583_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0___boxed(lean_object* v_ref_2585_, lean_object* v_msgData_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2585_, v_msgData_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v_ref_2585_);
return v_res_2594_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__0));
v___x_2597_ = l_Lean_stringToMessageData(v___x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(lean_object* v_ex_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
if (lean_obj_tag(v_ex_2598_) == 0)
{
lean_object* v_ref_2606_; lean_object* v_msg_2607_; lean_object* v___x_2608_; 
v_ref_2606_ = lean_ctor_get(v_ex_2598_, 0);
lean_inc(v_ref_2606_);
v_msg_2607_ = lean_ctor_get(v_ex_2598_, 1);
lean_inc_ref(v_msg_2607_);
lean_dec_ref_known(v_ex_2598_, 2);
v___x_2608_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0(v_ref_2606_, v_msg_2607_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v_ref_2606_);
return v___x_2608_;
}
else
{
lean_object* v_id_2609_; uint8_t v___y_2611_; uint8_t v___x_2633_; 
v_id_2609_ = lean_ctor_get(v_ex_2598_, 0);
lean_inc(v_id_2609_);
v___x_2633_ = l_Lean_Elab_isAbortExceptionId(v_id_2609_);
if (v___x_2633_ == 0)
{
uint8_t v___x_2634_; 
v___x_2634_ = l_Lean_Exception_isInterrupt(v_ex_2598_);
lean_dec_ref_known(v_ex_2598_, 2);
v___y_2611_ = v___x_2634_;
goto v___jp_2610_;
}
else
{
lean_dec_ref_known(v_ex_2598_, 2);
v___y_2611_ = v___x_2633_;
goto v___jp_2610_;
}
v___jp_2610_:
{
if (v___y_2611_ == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_InternalExceptionId_getName(v_id_2609_);
lean_dec(v_id_2609_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v___x_2614_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___closed__1);
v___x_2615_ = l_Lean_MessageData_ofName(v_a_2613_);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__1(v___x_2616_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2617_;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2630_; 
v_a_2618_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2620_ = v___x_2612_;
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2612_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v_ref_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v_ref_2622_ = lean_ctor_get(v___y_2603_, 5);
v___x_2623_ = lean_io_error_to_string(v_a_2618_);
v___x_2624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
v___x_2625_ = l_Lean_MessageData_ofFormat(v___x_2624_);
lean_inc(v_ref_2622_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_ref_2622_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2626_);
v___x_2628_ = v___x_2620_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec(v_id_2609_);
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0___boxed(lean_object* v_ex_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_ex_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(lean_object* v_a_2644_, lean_object* v_config_2645_, lean_object* v_____r_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0(v_a_2644_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2662_; 
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v___x_2654_, 0);
lean_dec(v_unused_2663_);
v___x_2656_ = v___x_2654_;
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v___x_2654_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_config_2645_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v_config_2645_);
v_a_2664_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2654_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2654_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed(lean_object* v_a_2672_, lean_object* v_config_2673_, lean_object* v_____r_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2672_, v_config_2673_, v_____r_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(lean_object* v___f_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_box(0);
lean_inc(v___y_2690_);
lean_inc_ref(v___y_2689_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
v___x_2693_ = lean_apply_8(v___f_2683_, v___x_2692_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, lean_box(0));
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1___boxed(lean_object* v___f_2694_, lean_object* v_x_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2694_, v_x_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec_ref(v_x_2695_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(lean_object* v_eval_2704_, lean_object* v_config_2705_, lean_object* v_item_2706_, uint8_t v_logExceptions_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v___y_2716_; lean_object* v___x_2734_; 
lean_inc(v_a_2713_);
lean_inc_ref(v_a_2712_);
lean_inc(v_a_2711_);
lean_inc_ref(v_a_2710_);
lean_inc(v_a_2709_);
lean_inc_ref(v_a_2708_);
lean_inc(v_config_2705_);
v___x_2734_ = lean_apply_9(v_eval_2704_, v_config_2705_, v_item_2706_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, lean_box(0));
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_dec(v_config_2705_);
return v___x_2734_;
}
else
{
lean_object* v_a_2735_; lean_object* v___f_2736_; uint8_t v___y_2738_; uint8_t v___x_2755_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc_n(v_a_2735_, 2);
lean_inc(v_config_2705_);
v___f_2736_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2736_, 0, v_a_2735_);
lean_closure_set(v___f_2736_, 1, v_config_2705_);
v___x_2755_ = l_Lean_Exception_isInterrupt(v_a_2735_);
if (v___x_2755_ == 0)
{
uint8_t v___x_2756_; 
lean_inc(v_a_2735_);
v___x_2756_ = l_Lean_Exception_isRuntime(v_a_2735_);
v___y_2738_ = v___x_2756_;
goto v___jp_2737_;
}
else
{
v___y_2738_ = v___x_2755_;
goto v___jp_2737_;
}
v___jp_2737_:
{
if (v___y_2738_ == 0)
{
if (v_logExceptions_2707_ == 0)
{
lean_dec_ref(v___f_2736_);
lean_dec(v_a_2735_);
lean_dec(v_config_2705_);
return v___x_2734_;
}
else
{
lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2753_; 
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; 
v_unused_2754_ = lean_ctor_get(v___x_2734_, 0);
lean_dec(v_unused_2754_);
v___x_2740_ = v___x_2734_;
v_isShared_2741_ = v_isSharedCheck_2753_;
goto v_resetjp_2739_;
}
else
{
lean_dec(v___x_2734_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2753_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
if (lean_obj_tag(v_a_2735_) == 1)
{
lean_object* v_extra_2742_; 
v_extra_2742_ = lean_ctor_get(v_a_2735_, 1);
if (lean_obj_tag(v_extra_2742_) == 0)
{
lean_object* v_id_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
lean_dec_ref(v___f_2736_);
v_id_2743_ = lean_ctor_get(v_a_2735_, 0);
v___x_2744_ = l_Lean_Elab_abortTermExceptionId;
v___x_2745_ = l_Lean_instBEqInternalExceptionId_beq(v_id_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_del_object(v___x_2740_);
v___x_2746_ = lean_box(0);
v___x_2747_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__0(v_a_2735_, v_config_2705_, v___x_2746_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
v___y_2716_ = v___x_2747_;
goto v___jp_2715_;
}
else
{
lean_object* v___x_2749_; 
lean_dec_ref_known(v_a_2735_, 2);
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 0);
lean_ctor_set(v___x_2740_, 0, v_config_2705_);
v___x_2749_ = v___x_2740_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_config_2705_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
lean_object* v___x_2751_; 
lean_del_object(v___x_2740_);
lean_dec(v_config_2705_);
v___x_2751_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2736_, v_a_2735_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec_ref_known(v_a_2735_, 2);
v___y_2716_ = v___x_2751_;
goto v___jp_2715_;
}
}
else
{
lean_object* v___x_2752_; 
lean_del_object(v___x_2740_);
lean_dec(v_config_2705_);
v___x_2752_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___lam__1(v___f_2736_, v_a_2735_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2735_);
v___y_2716_ = v___x_2752_;
goto v___jp_2715_;
}
}
}
}
else
{
lean_dec_ref(v___f_2736_);
lean_dec(v_a_2735_);
lean_dec(v_config_2705_);
return v___x_2734_;
}
}
}
v___jp_2715_:
{
if (lean_obj_tag(v___y_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2725_; 
v_a_2717_ = lean_ctor_get(v___y_2716_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___y_2716_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2719_ = v___y_2716_;
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___y_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_a_2721_; lean_object* v___x_2723_; 
v_a_2721_ = lean_ctor_get(v_a_2717_, 0);
lean_inc(v_a_2721_);
lean_dec(v_a_2717_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_a_2721_);
v___x_2723_ = v___x_2719_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
v_a_2726_ = lean_ctor_get(v___y_2716_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___y_2716_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___y_2716_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___y_2716_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg___boxed(lean_object* v_eval_2757_, lean_object* v_config_2758_, lean_object* v_item_2759_, lean_object* v_logExceptions_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
uint8_t v_logExceptions_boxed_2768_; lean_object* v_res_2769_; 
v_logExceptions_boxed_2768_ = lean_unbox(v_logExceptions_2760_);
v_res_2769_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2757_, v_config_2758_, v_item_2759_, v_logExceptions_boxed_2768_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(lean_object* v_00_u03b1_2770_, lean_object* v_eval_2771_, lean_object* v_config_2772_, lean_object* v_item_2773_, uint8_t v_logExceptions_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_2771_, v_config_2772_, v_item_2773_, v_logExceptions_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_eval_2784_, lean_object* v_config_2785_, lean_object* v_item_2786_, lean_object* v_logExceptions_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
uint8_t v_logExceptions_boxed_2795_; lean_object* v_res_2796_; 
v_logExceptions_boxed_2795_ = lean_unbox(v_logExceptions_2787_);
v_res_2796_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet(v_00_u03b1_2783_, v_eval_2784_, v_config_2785_, v_item_2786_, v_logExceptions_boxed_2795_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(lean_object* v_ref_2797_, lean_object* v_msgData_2798_, uint8_t v_severity_2799_, uint8_t v_isSilent_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___redArg(v_ref_2797_, v_msgData_2798_, v_severity_2799_, v_isSilent_2800_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2809_, lean_object* v_msgData_2810_, lean_object* v_severity_2811_, lean_object* v_isSilent_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
uint8_t v_severity_boxed_2820_; uint8_t v_isSilent_boxed_2821_; lean_object* v_res_2822_; 
v_severity_boxed_2820_ = lean_unbox(v_severity_2811_);
v_isSilent_boxed_2821_ = lean_unbox(v_isSilent_2812_);
v_res_2822_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_ConfigEval_EvalConfigItem_trySet_spec__0_spec__0_spec__1(v_ref_2809_, v_msgData_2810_, v_severity_boxed_2820_, v_isSilent_boxed_2821_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v_ref_2809_);
return v_res_2822_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_box(0);
v___x_2824_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
lean_ctor_set(v___x_2825_, 1, v___x_2823_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg(){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___closed__0);
v___x_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg___boxed(lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(lean_object* v_00_u03b1_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___boxed(lean_object* v_00_u03b1_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0(v_00_u03b1_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
return v_res_2848_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = l_Lean_Level_ofNat(v___x_2852_);
return v___x_2853_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__2);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2854_);
return v___x_2856_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__3);
v___x_2858_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__1));
v___x_2859_ = l_Lean_Expr_const___override(v___x_2858_, v___x_2857_);
return v___x_2859_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = lean_box(0);
v___x_2864_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__6));
v___x_2865_ = l_Lean_Expr_const___override(v___x_2864_, v___x_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object* v_cfg_2869_, lean_object* v_cfgItem_2870_, lean_object* v_cfgType_x3f_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; 
if (lean_obj_tag(v_cfgType_x3f_2871_) == 1)
{
lean_object* v_val_2889_; lean_object* v___x_2890_; lean_object* v_infoState_2891_; uint8_t v_enabled_2892_; 
v_val_2889_ = lean_ctor_get(v_cfgType_x3f_2871_, 0);
lean_inc(v_val_2889_);
lean_dec_ref_known(v_cfgType_x3f_2871_, 1);
v___x_2890_ = lean_st_ref_get(v_a_2877_);
v_infoState_2891_ = lean_ctor_get(v___x_2890_, 7);
lean_inc_ref(v_infoState_2891_);
lean_dec(v___x_2890_);
v_enabled_2892_ = lean_ctor_get_uint8(v_infoState_2891_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2891_);
if (v_enabled_2892_ == 0)
{
lean_dec(v_val_2889_);
v___y_2880_ = v_a_2872_;
v___y_2881_ = v_a_2873_;
v___y_2882_ = v_a_2874_;
v___y_2883_ = v_a_2875_;
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___y_2896_; uint8_t v___x_2908_; 
v___x_2893_ = lean_unsigned_to_nat(0u);
v___x_2894_ = l_Lean_Syntax_getArg(v_cfgItem_2870_, v___x_2893_);
v___x_2908_ = l_Lean_Syntax_isAtom(v___x_2894_);
if (v___x_2908_ == 0)
{
v___y_2896_ = v___x_2908_;
goto v___jp_2895_;
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = l_Lean_Syntax_getArg(v_cfgItem_2870_, v___x_2909_);
v___x_2911_ = l_Lean_Syntax_isMissing(v___x_2910_);
lean_dec(v___x_2910_);
v___y_2896_ = v___x_2911_;
goto v___jp_2895_;
}
v___jp_2895_:
{
if (v___y_2896_ == 0)
{
lean_dec(v___x_2894_);
lean_dec(v_val_2889_);
v___y_2880_ = v_a_2872_;
v___y_2881_ = v_a_2873_;
v___y_2882_ = v_a_2874_;
v___y_2883_ = v_a_2875_;
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2897_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__4);
v___x_2898_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7, &l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__7);
v___x_2899_ = l_Lean_mkAppB(v___x_2897_, v_val_2889_, v___x_2898_);
v___x_2900_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___closed__9));
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
lean_ctor_set(v___x_2901_, 1, v___x_2894_);
v___x_2902_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2);
v___x_2903_ = lean_box(0);
v___x_2904_ = 0;
v___x_2905_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2905_, 0, v___x_2901_);
lean_ctor_set(v___x_2905_, 1, v___x_2902_);
lean_ctor_set(v___x_2905_, 2, v___x_2903_);
lean_ctor_set(v___x_2905_, 3, v___x_2899_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*4, v___x_2904_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*4 + 1, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v___x_2903_);
v___x_2907_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo_spec__0(v___x_2906_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
lean_dec_ref(v___x_2907_);
v___y_2880_ = v_a_2872_;
v___y_2881_ = v_a_2873_;
v___y_2882_ = v_a_2874_;
v___y_2883_ = v_a_2875_;
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
goto v___jp_2879_;
}
}
}
}
else
{
lean_dec(v_cfgType_x3f_2871_);
v___y_2880_ = v_a_2872_;
v___y_2881_ = v_a_2873_;
v___y_2882_ = v_a_2874_;
v___y_2883_ = v_a_2875_;
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
goto v___jp_2879_;
}
v___jp_2879_:
{
uint8_t v___x_2886_; 
v___x_2886_ = l_Lean_Syntax_hasMissing(v_cfgItem_2870_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_dec(v_cfg_2869_);
v___x_2887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr_spec__0___redArg();
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_cfg_2869_);
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg___boxed(lean_object* v_cfg_2912_, lean_object* v_cfgItem_2913_, lean_object* v_cfgType_x3f_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2912_, v_cfgItem_2913_, v_cfgType_x3f_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_cfgItem_2913_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(lean_object* v_00_u03b1_2923_, lean_object* v_cfg_2924_, lean_object* v_cfgItem_2925_, lean_object* v_cfgType_x3f_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2924_, v_cfgItem_2925_, v_cfgType_x3f_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___boxed(lean_object* v_00_u03b1_2935_, lean_object* v_cfg_2936_, lean_object* v_cfgItem_2937_, lean_object* v_cfgType_x3f_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr(v_00_u03b1_2935_, v_cfg_2936_, v_cfgItem_2937_, v_cfgType_x3f_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_cfgItem_2937_);
return v_res_2946_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_s_2947_, lean_object* v_a_2948_, uint8_t v_b_2949_){
_start:
{
lean_object* v_str_2950_; lean_object* v_startInclusive_2951_; lean_object* v_endExclusive_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_str_2950_ = lean_ctor_get(v_s_2947_, 0);
v_startInclusive_2951_ = lean_ctor_get(v_s_2947_, 1);
v_endExclusive_2952_ = lean_ctor_get(v_s_2947_, 2);
v___x_2953_ = lean_nat_sub(v_endExclusive_2952_, v_startInclusive_2951_);
v___x_2954_ = lean_nat_dec_eq(v_a_2948_, v___x_2953_);
lean_dec(v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; uint32_t v___x_2956_; uint32_t v___x_2957_; uint8_t v___x_2958_; 
v___x_2955_ = lean_nat_add(v_startInclusive_2951_, v_a_2948_);
lean_dec(v_a_2948_);
v___x_2956_ = lean_string_utf8_get_fast(v_str_2950_, v___x_2955_);
v___x_2957_ = 46;
v___x_2958_ = lean_uint32_dec_eq(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_string_utf8_next_fast(v_str_2950_, v___x_2955_);
lean_dec(v___x_2955_);
v___x_2960_ = lean_nat_sub(v___x_2959_, v_startInclusive_2951_);
v_a_2948_ = v___x_2960_;
v_b_2949_ = v___x_2958_;
goto _start;
}
else
{
lean_dec(v___x_2955_);
return v___x_2958_;
}
}
else
{
lean_dec(v_a_2948_);
return v_b_2949_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_s_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_){
_start:
{
uint8_t v_b_boxed_2965_; uint8_t v_res_2966_; lean_object* v_r_2967_; 
v_b_boxed_2965_ = lean_unbox(v_b_2964_);
v_res_2966_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2962_, v_a_2963_, v_b_boxed_2965_);
lean_dec_ref(v_s_2962_);
v_r_2967_ = lean_box(v_res_2966_);
return v_r_2967_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(lean_object* v_s_2968_){
_start:
{
lean_object* v_searcher_2969_; uint8_t v___x_2970_; uint8_t v___x_2971_; 
v_searcher_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = 0;
v___x_2971_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_2968_, v_searcher_2969_, v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0___boxed(lean_object* v_s_2972_){
_start:
{
uint8_t v_res_2973_; lean_object* v_r_2974_; 
v_res_2973_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v_s_2972_);
lean_dec_ref(v_s_2972_);
v_r_2974_ = lean_box(v_res_2973_);
return v_r_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(lean_object* v_si_2975_, lean_object* v_val_2976_){
_start:
{
lean_object* v___y_2978_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_string_utf8_byte_size(v_val_2976_);
lean_inc_ref(v_val_2976_);
v___x_2986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2986_, 0, v_val_2976_);
lean_ctor_set(v___x_2986_, 1, v___x_2984_);
lean_ctor_set(v___x_2986_, 2, v___x_2985_);
v___x_2987_ = l_String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0(v___x_2986_);
lean_dec_ref_known(v___x_2986_, 3);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_box(0);
lean_inc_ref(v_val_2976_);
v___x_2989_ = l_Lean_Name_str___override(v___x_2988_, v_val_2976_);
v___y_2978_ = v___x_2989_;
goto v___jp_2977_;
}
else
{
lean_object* v___x_2990_; 
lean_inc_ref(v_val_2976_);
v___x_2990_ = l_String_toName(v_val_2976_);
v___y_2978_ = v___x_2990_;
goto v___jp_2977_;
}
v___jp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = lean_string_utf8_byte_size(v_val_2976_);
v___x_2981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2981_, 0, v_val_2976_);
lean_ctor_set(v___x_2981_, 1, v___x_2979_);
lean_ctor_set(v___x_2981_, 2, v___x_2980_);
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2983_, 0, v_si_2975_);
lean_ctor_set(v___x_2983_, 1, v___x_2981_);
lean_ctor_set(v___x_2983_, 2, v___y_2978_);
lean_ctor_set(v___x_2983_, 3, v___x_2982_);
return v___x_2983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(lean_object* v_eval_2992_, uint8_t v_logExceptions_2993_, lean_object* v_onErr_2994_, lean_object* v_init_2995_, lean_object* v_cfgs_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = lean_array_get_size(v_cfgs_2996_);
v___x_3006_ = lean_nat_dec_lt(v___x_3004_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_dec_ref(v_onErr_2994_);
lean_dec_ref(v_eval_2992_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_init_2995_);
return v___x_3007_;
}
else
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_nat_dec_le(v___x_3005_, v___x_3005_);
if (v___x_3008_ == 0)
{
if (v___x_3006_ == 0)
{
lean_object* v___x_3009_; 
lean_dec_ref(v_onErr_2994_);
lean_dec_ref(v_eval_2992_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_init_2995_);
return v___x_3009_;
}
else
{
size_t v___x_3010_; size_t v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = lean_usize_of_nat(v___x_3005_);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_2992_, v_logExceptions_2993_, v_onErr_2994_, v_cfgs_2996_, v___x_3010_, v___x_3011_, v_init_2995_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
return v___x_3012_;
}
}
else
{
size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = lean_usize_of_nat(v___x_3005_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_2992_, v_logExceptions_2993_, v_onErr_2994_, v_cfgs_2996_, v___x_3013_, v___x_3014_, v_init_2995_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(lean_object* v_eval_3016_, uint8_t v_logExceptions_3017_, lean_object* v_onErr_3018_, lean_object* v_init_3019_, lean_object* v_cfg_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__1));
lean_inc(v_cfg_3020_);
v___x_3060_ = l_Lean_Syntax_isOfKind(v_cfg_3020_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3061_ = l_Lean_Syntax_getNumArgs(v_cfg_3020_);
v___x_3062_ = lean_unsigned_to_nat(1u);
v___x_3063_ = lean_nat_dec_eq(v___x_3061_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v_atomAsIdent_3064_; uint8_t v___x_3065_; 
v_atomAsIdent_3064_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___closed__0));
v___x_3065_ = lean_nat_dec_le(v___x_3062_, v___x_3061_);
if (v___x_3065_ == 0)
{
lean_dec(v___x_3061_);
if (lean_obj_tag(v_cfg_3020_) == 2)
{
lean_object* v_info_3066_; lean_object* v_val_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec_ref(v_onErr_3018_);
v_info_3066_ = lean_ctor_get(v_cfg_3020_, 0);
v_val_3067_ = lean_ctor_get(v_cfg_3020_, 1);
lean_inc_ref(v_val_3067_);
lean_inc(v_info_3066_);
v___x_3068_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___lam__0(v_info_3066_, v_val_3067_);
v___x_3069_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_3070_ = l_Lean_mkCIdentFrom(v_cfg_3020_, v___x_3069_, v___x_3063_);
v___x_3071_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__8));
v___x_3072_ = l_Lean_TSyntax_getId(v___x_3068_);
v___x_3073_ = lean_erase_macro_scopes(v___x_3072_);
v___x_3074_ = lean_box(0);
lean_inc(v___x_3068_);
v___x_3075_ = l_Lean_Syntax_identComponents(v___x_3068_, v___x_3074_);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3077_, 0, v_cfg_3020_);
lean_ctor_set(v___x_3077_, 1, v___x_3068_);
lean_ctor_set(v___x_3077_, 2, v___x_3070_);
lean_ctor_set(v___x_3077_, 3, v___x_3071_);
lean_ctor_set(v___x_3077_, 4, v___x_3073_);
lean_ctor_set(v___x_3077_, 5, v___x_3075_);
lean_ctor_set(v___x_3077_, 6, v___x_3076_);
v___x_3078_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3016_, v_init_3019_, v___x_3077_, v_logExceptions_3017_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3078_;
}
else
{
lean_dec_ref(v_eval_3016_);
goto v___jp_3039_;
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = l_Lean_Syntax_getArg(v_cfg_3020_, v___x_3079_);
if (lean_obj_tag(v___x_3080_) == 2)
{
lean_object* v_val_3081_; lean_object* v___y_3083_; uint8_t v_val_3084_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v_val_3081_ = lean_ctor_get(v___x_3080_, 1);
lean_inc_ref(v_val_3081_);
v___x_3095_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__11));
v___x_3096_ = lean_string_dec_eq(v_val_3081_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3097_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__12));
v___x_3098_ = lean_string_dec_eq(v_val_3081_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
lean_dec_ref_known(v___x_3080_, 2);
v___x_3099_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__13));
v___x_3100_ = lean_string_dec_eq(v_val_3081_, v___x_3099_);
lean_dec_ref(v_val_3081_);
if (v___x_3100_ == 0)
{
lean_dec(v___x_3061_);
lean_dec_ref(v_eval_3016_);
goto v___jp_3039_;
}
else
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = lean_unsigned_to_nat(5u);
v___x_3102_ = lean_nat_dec_le(v___x_3061_, v___x_3101_);
lean_dec(v___x_3061_);
if (v___x_3102_ == 0)
{
lean_dec_ref(v_eval_3016_);
goto v___jp_3039_;
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = l_Lean_Syntax_getArg(v_cfg_3020_, v___x_3062_);
v___x_3104_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_3064_, v___x_3103_);
if (lean_obj_tag(v___x_3104_) == 1)
{
lean_object* v_val_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec_ref(v_onErr_3018_);
v_val_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc_n(v_val_3105_, 2);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = lean_unsigned_to_nat(3u);
v___x_3107_ = l_Lean_Syntax_getArg(v_cfg_3020_, v___x_3106_);
v___x_3108_ = lean_box(0);
v___x_3109_ = l_Lean_TSyntax_getId(v_val_3105_);
v___x_3110_ = lean_erase_macro_scopes(v___x_3109_);
v___x_3111_ = l_Lean_Syntax_identComponents(v_val_3105_, v___x_3108_);
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3113_, 0, v_cfg_3020_);
lean_ctor_set(v___x_3113_, 1, v_val_3105_);
lean_ctor_set(v___x_3113_, 2, v___x_3107_);
lean_ctor_set(v___x_3113_, 3, v___x_3108_);
lean_ctor_set(v___x_3113_, 4, v___x_3110_);
lean_ctor_set(v___x_3113_, 5, v___x_3111_);
lean_ctor_set(v___x_3113_, 6, v___x_3112_);
v___x_3114_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3016_, v_init_3019_, v___x_3113_, v_logExceptions_3017_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3114_;
}
else
{
lean_dec(v___x_3104_);
lean_dec_ref(v_eval_3016_);
goto v___jp_3039_;
}
}
}
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec_ref(v_val_3081_);
v___x_3115_ = lean_box(v___x_3063_);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
v___y_3083_ = v___x_3116_;
v_val_3084_ = v___x_3063_;
goto v___jp_3082_;
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec_ref(v_val_3081_);
v___x_3117_ = lean_box(v___x_3096_);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
v___y_3083_ = v___x_3118_;
v_val_3084_ = v___x_3096_;
goto v___jp_3082_;
}
v___jp_3082_:
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = lean_unsigned_to_nat(2u);
v___x_3086_ = lean_nat_dec_eq(v___x_3061_, v___x_3085_);
lean_dec(v___x_3061_);
if (v___x_3086_ == 0)
{
lean_dec(v___y_3083_);
lean_dec_ref_known(v___x_3080_, 2);
lean_dec_ref(v_eval_3016_);
goto v___jp_3039_;
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = l_Lean_Syntax_getArg(v_cfg_3020_, v___x_3062_);
v___x_3088_ = l_Lean_Elab_ConfigEval_foldConfigM___redArg___lam__4(v_atomAsIdent_3064_, v___x_3087_);
if (lean_obj_tag(v___x_3088_) == 1)
{
lean_dec_ref(v_onErr_3018_);
if (v_val_3084_ == 0)
{
lean_object* v_val_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_val_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_val_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3090_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__10));
v___x_3091_ = l_Lean_mkCIdentFrom(v___x_3080_, v___x_3090_, v___x_3063_);
lean_dec_ref_known(v___x_3080_, 2);
v___y_3029_ = v_val_3089_;
v___y_3030_ = v___y_3083_;
v___y_3031_ = v___x_3091_;
goto v___jp_3028_;
}
else
{
lean_object* v_val_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_val_3092_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3093_ = ((lean_object*)(l_Lean_Elab_ConfigEval_foldConfigM___redArg___closed__7));
v___x_3094_ = l_Lean_mkCIdentFrom(v___x_3080_, v___x_3093_, v___x_3063_);
lean_dec_ref_known(v___x_3080_, 2);
v___y_3029_ = v_val_3092_;
v___y_3030_ = v___y_3083_;
v___y_3031_ = v___x_3094_;
goto v___jp_3028_;
}
}
else
{
lean_dec(v___x_3088_);
lean_dec(v___y_3083_);
lean_dec_ref_known(v___x_3080_, 2);
lean_dec_ref(v_eval_3016_);
goto v___jp_3039_;
}
}
}
}
else
{
lean_dec(v___x_3080_);
lean_dec(v___x_3061_);
lean_dec_ref(v_eval_3016_);
goto v___jp_3039_;
}
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec(v___x_3061_);
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = l_Lean_Syntax_getArg(v_cfg_3020_, v___x_3119_);
lean_dec(v_cfg_3020_);
v_cfg_3020_ = v___x_3120_;
goto _start;
}
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = l_Lean_Syntax_getArgs(v_cfg_3020_);
lean_dec(v_cfg_3020_);
v___x_3123_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3016_, v_logExceptions_3017_, v_onErr_3018_, v_init_3019_, v___x_3122_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec_ref(v___x_3122_);
return v___x_3123_;
}
v___jp_3028_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3032_ = l_Lean_TSyntax_getId(v___y_3029_);
v___x_3033_ = lean_erase_macro_scopes(v___x_3032_);
v___x_3034_ = lean_box(0);
lean_inc(v___y_3029_);
v___x_3035_ = l_Lean_Syntax_identComponents(v___y_3029_, v___x_3034_);
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3037_, 0, v_cfg_3020_);
lean_ctor_set(v___x_3037_, 1, v___y_3029_);
lean_ctor_set(v___x_3037_, 2, v___y_3031_);
lean_ctor_set(v___x_3037_, 3, v___y_3030_);
lean_ctor_set(v___x_3037_, 4, v___x_3033_);
lean_ctor_set(v___x_3037_, 5, v___x_3035_);
lean_ctor_set(v___x_3037_, 6, v___x_3036_);
v___x_3038_ = l_Lean_Elab_ConfigEval_EvalConfigItem_trySet___redArg(v_eval_3016_, v_init_3019_, v___x_3037_, v_logExceptions_3017_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3038_;
}
v___jp_3039_:
{
lean_object* v_fileName_3040_; lean_object* v_fileMap_3041_; lean_object* v_options_3042_; lean_object* v_currRecDepth_3043_; lean_object* v_maxRecDepth_3044_; lean_object* v_ref_3045_; lean_object* v_currNamespace_3046_; lean_object* v_openDecls_3047_; lean_object* v_initHeartbeats_3048_; lean_object* v_maxHeartbeats_3049_; lean_object* v_quotContext_3050_; lean_object* v_currMacroScope_3051_; uint8_t v_diag_3052_; lean_object* v_cancelTk_x3f_3053_; uint8_t v_suppressElabErrors_3054_; lean_object* v_inheritedTraceOptions_3055_; lean_object* v_ref_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_fileName_3040_ = lean_ctor_get(v___y_3025_, 0);
v_fileMap_3041_ = lean_ctor_get(v___y_3025_, 1);
v_options_3042_ = lean_ctor_get(v___y_3025_, 2);
v_currRecDepth_3043_ = lean_ctor_get(v___y_3025_, 3);
v_maxRecDepth_3044_ = lean_ctor_get(v___y_3025_, 4);
v_ref_3045_ = lean_ctor_get(v___y_3025_, 5);
v_currNamespace_3046_ = lean_ctor_get(v___y_3025_, 6);
v_openDecls_3047_ = lean_ctor_get(v___y_3025_, 7);
v_initHeartbeats_3048_ = lean_ctor_get(v___y_3025_, 8);
v_maxHeartbeats_3049_ = lean_ctor_get(v___y_3025_, 9);
v_quotContext_3050_ = lean_ctor_get(v___y_3025_, 10);
v_currMacroScope_3051_ = lean_ctor_get(v___y_3025_, 11);
v_diag_3052_ = lean_ctor_get_uint8(v___y_3025_, sizeof(void*)*14);
v_cancelTk_x3f_3053_ = lean_ctor_get(v___y_3025_, 12);
v_suppressElabErrors_3054_ = lean_ctor_get_uint8(v___y_3025_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3055_ = lean_ctor_get(v___y_3025_, 13);
v_ref_3056_ = l_Lean_replaceRef(v_cfg_3020_, v_ref_3045_);
lean_inc_ref(v_inheritedTraceOptions_3055_);
lean_inc(v_cancelTk_x3f_3053_);
lean_inc(v_currMacroScope_3051_);
lean_inc(v_quotContext_3050_);
lean_inc(v_maxHeartbeats_3049_);
lean_inc(v_initHeartbeats_3048_);
lean_inc(v_openDecls_3047_);
lean_inc(v_currNamespace_3046_);
lean_inc(v_maxRecDepth_3044_);
lean_inc(v_currRecDepth_3043_);
lean_inc_ref(v_options_3042_);
lean_inc_ref(v_fileMap_3041_);
lean_inc_ref(v_fileName_3040_);
v___x_3057_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3057_, 0, v_fileName_3040_);
lean_ctor_set(v___x_3057_, 1, v_fileMap_3041_);
lean_ctor_set(v___x_3057_, 2, v_options_3042_);
lean_ctor_set(v___x_3057_, 3, v_currRecDepth_3043_);
lean_ctor_set(v___x_3057_, 4, v_maxRecDepth_3044_);
lean_ctor_set(v___x_3057_, 5, v_ref_3056_);
lean_ctor_set(v___x_3057_, 6, v_currNamespace_3046_);
lean_ctor_set(v___x_3057_, 7, v_openDecls_3047_);
lean_ctor_set(v___x_3057_, 8, v_initHeartbeats_3048_);
lean_ctor_set(v___x_3057_, 9, v_maxHeartbeats_3049_);
lean_ctor_set(v___x_3057_, 10, v_quotContext_3050_);
lean_ctor_set(v___x_3057_, 11, v_currMacroScope_3051_);
lean_ctor_set(v___x_3057_, 12, v_cancelTk_x3f_3053_);
lean_ctor_set(v___x_3057_, 13, v_inheritedTraceOptions_3055_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*14, v_diag_3052_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*14 + 1, v_suppressElabErrors_3054_);
lean_inc(v___y_3026_);
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3023_);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3021_);
v___x_3058_ = lean_apply_9(v_onErr_3018_, v_init_3019_, v_cfg_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___x_3057_, v___y_3026_, lean_box(0));
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(lean_object* v_eval_3124_, uint8_t v_logExceptions_3125_, lean_object* v_onErr_3126_, lean_object* v_as_3127_, size_t v_i_3128_, size_t v_stop_3129_, lean_object* v_b_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_eq(v_i_3128_, v_stop_3129_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = lean_array_uget_borrowed(v_as_3127_, v_i_3128_);
lean_inc(v___x_3139_);
lean_inc_ref(v_onErr_3126_);
lean_inc_ref(v_eval_3124_);
v___x_3140_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3124_, v_logExceptions_3125_, v_onErr_3126_, v_b_3130_, v___x_3139_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; size_t v___x_3142_; size_t v___x_3143_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3128_, v___x_3142_);
v_i_3128_ = v___x_3143_;
v_b_3130_ = v_a_3141_;
goto _start;
}
else
{
lean_dec_ref(v_onErr_3126_);
lean_dec_ref(v_eval_3124_);
return v___x_3140_;
}
}
else
{
lean_object* v___x_3145_; 
lean_dec_ref(v_onErr_3126_);
lean_dec_ref(v_eval_3124_);
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_b_3130_);
return v___x_3145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_eval_3146_, lean_object* v_logExceptions_3147_, lean_object* v_onErr_3148_, lean_object* v_as_3149_, lean_object* v_i_3150_, lean_object* v_stop_3151_, lean_object* v_b_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
uint8_t v_logExceptions_boxed_3160_; size_t v_i_boxed_3161_; size_t v_stop_boxed_3162_; lean_object* v_res_3163_; 
v_logExceptions_boxed_3160_ = lean_unbox(v_logExceptions_3147_);
v_i_boxed_3161_ = lean_unbox_usize(v_i_3150_);
lean_dec(v_i_3150_);
v_stop_boxed_3162_ = lean_unbox_usize(v_stop_3151_);
lean_dec(v_stop_3151_);
v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3146_, v_logExceptions_boxed_3160_, v_onErr_3148_, v_as_3149_, v_i_boxed_3161_, v_stop_boxed_3162_, v_b_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v_as_3149_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg___boxed(lean_object* v_eval_3164_, lean_object* v_logExceptions_3165_, lean_object* v_onErr_3166_, lean_object* v_init_3167_, lean_object* v_cfgs_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v_logExceptions_boxed_3176_; lean_object* v_res_3177_; 
v_logExceptions_boxed_3176_ = lean_unbox(v_logExceptions_3165_);
v_res_3177_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3164_, v_logExceptions_boxed_3176_, v_onErr_3166_, v_init_3167_, v_cfgs_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v_cfgs_3168_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg___boxed(lean_object* v_eval_3178_, lean_object* v_logExceptions_3179_, lean_object* v_onErr_3180_, lean_object* v_init_3181_, lean_object* v_cfg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v_logExceptions_boxed_3190_; lean_object* v_res_3191_; 
v_logExceptions_boxed_3190_ = lean_unbox(v_logExceptions_3179_);
v_res_3191_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3178_, v_logExceptions_boxed_3190_, v_onErr_3180_, v_init_3181_, v_cfg_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(lean_object* v_eval_3192_, lean_object* v_init_3193_, lean_object* v_cfg_3194_, lean_object* v_onErr_3195_, uint8_t v_logExceptions_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3192_, v_logExceptions_3196_, v_onErr_3195_, v_init_3193_, v_cfg_3194_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg___boxed(lean_object* v_eval_3205_, lean_object* v_init_3206_, lean_object* v_cfg_3207_, lean_object* v_onErr_3208_, lean_object* v_logExceptions_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
uint8_t v_logExceptions_boxed_3217_; lean_object* v_res_3218_; 
v_logExceptions_boxed_3217_ = lean_unbox(v_logExceptions_3209_);
v_res_3218_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___redArg(v_eval_3205_, v_init_3206_, v_cfg_3207_, v_onErr_3208_, v_logExceptions_boxed_3217_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(lean_object* v_00_u03b1_3219_, lean_object* v_eval_3220_, lean_object* v_init_3221_, lean_object* v_cfg_3222_, lean_object* v_onErr_3223_, uint8_t v_logExceptions_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3220_, v_logExceptions_3224_, v_onErr_3223_, v_init_3221_, v_cfg_3222_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig___boxed(lean_object* v_00_u03b1_3233_, lean_object* v_eval_3234_, lean_object* v_init_3235_, lean_object* v_cfg_3236_, lean_object* v_onErr_3237_, lean_object* v_logExceptions_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
uint8_t v_logExceptions_boxed_3246_; lean_object* v_res_3247_; 
v_logExceptions_boxed_3246_ = lean_unbox(v_logExceptions_3238_);
v_res_3247_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig(v_00_u03b1_3233_, v_eval_3234_, v_init_3235_, v_cfg_3236_, v_onErr_3237_, v_logExceptions_boxed_3246_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3243_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(lean_object* v_00_u03b1_3248_, lean_object* v_eval_3249_, uint8_t v_logExceptions_3250_, lean_object* v_onErr_3251_, lean_object* v_init_3252_, lean_object* v_cfg_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_3249_, v_logExceptions_3250_, v_onErr_3251_, v_init_3252_, v_cfg_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___boxed(lean_object* v_00_u03b1_3262_, lean_object* v_eval_3263_, lean_object* v_logExceptions_3264_, lean_object* v_onErr_3265_, lean_object* v_init_3266_, lean_object* v_cfg_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v_logExceptions_boxed_3275_; lean_object* v_res_3276_; 
v_logExceptions_boxed_3275_ = lean_unbox(v_logExceptions_3264_);
v_res_3276_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0(v_00_u03b1_3262_, v_eval_3263_, v_logExceptions_boxed_3275_, v_onErr_3265_, v_init_3266_, v_cfg_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(lean_object* v_00_u03b1_3277_, lean_object* v_eval_3278_, uint8_t v_logExceptions_3279_, lean_object* v_onErr_3280_, lean_object* v_init_3281_, lean_object* v_cfgs_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3278_, v_logExceptions_3279_, v_onErr_3280_, v_init_3281_, v_cfgs_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3291_, lean_object* v_eval_3292_, lean_object* v_logExceptions_3293_, lean_object* v_onErr_3294_, lean_object* v_init_3295_, lean_object* v_cfgs_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v_logExceptions_boxed_3304_; lean_object* v_res_3305_; 
v_logExceptions_boxed_3304_ = lean_unbox(v_logExceptions_3293_);
v_res_3305_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1(v_00_u03b1_3291_, v_eval_3292_, v_logExceptions_boxed_3304_, v_onErr_3294_, v_init_3295_, v_cfgs_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_cfgs_3296_);
return v_res_3305_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(lean_object* v_s_3306_, lean_object* v_inst_3307_, lean_object* v_R_3308_, lean_object* v_a_3309_, uint8_t v_b_3310_, lean_object* v_c_3311_){
_start:
{
uint8_t v___x_3312_; 
v___x_3312_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___redArg(v_s_3306_, v_a_3309_, v_b_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_s_3313_, lean_object* v_inst_3314_, lean_object* v_R_3315_, lean_object* v_a_3316_, lean_object* v_b_3317_, lean_object* v_c_3318_){
_start:
{
uint8_t v_b_boxed_3319_; uint8_t v_res_3320_; lean_object* v_r_3321_; 
v_b_boxed_3319_ = lean_unbox(v_b_3317_);
v_res_3320_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__0_spec__1(v_s_3313_, v_inst_3314_, v_R_3315_, v_a_3316_, v_b_boxed_3319_, v_c_3318_);
lean_dec_ref(v_s_3313_);
v_r_3321_ = lean_box(v_res_3320_);
return v_r_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3322_, lean_object* v_eval_3323_, uint8_t v_logExceptions_3324_, lean_object* v_onErr_3325_, lean_object* v_as_3326_, size_t v_i_3327_, size_t v_stop_3328_, lean_object* v_b_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___redArg(v_eval_3323_, v_logExceptions_3324_, v_onErr_3325_, v_as_3326_, v_i_3327_, v_stop_3328_, v_b_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3338_, lean_object* v_eval_3339_, lean_object* v_logExceptions_3340_, lean_object* v_onErr_3341_, lean_object* v_as_3342_, lean_object* v_i_3343_, lean_object* v_stop_3344_, lean_object* v_b_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v_logExceptions_boxed_3353_; size_t v_i_boxed_3354_; size_t v_stop_boxed_3355_; lean_object* v_res_3356_; 
v_logExceptions_boxed_3353_ = lean_unbox(v_logExceptions_3340_);
v_i_boxed_3354_ = lean_unbox_usize(v_i_3343_);
lean_dec(v_i_3343_);
v_stop_boxed_3355_ = lean_unbox_usize(v_stop_3344_);
lean_dec(v_stop_3344_);
v_res_3356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1_spec__3(v_00_u03b1_3338_, v_eval_3339_, v_logExceptions_boxed_3353_, v_onErr_3341_, v_as_3342_, v_i_boxed_3354_, v_stop_boxed_3355_, v_b_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec_ref(v_as_3342_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(lean_object* v_eval_3357_, lean_object* v_init_3358_, lean_object* v_cfgs_3359_, lean_object* v_onErr_3360_, uint8_t v_logExceptions_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3357_, v_logExceptions_3361_, v_onErr_3360_, v_init_3358_, v_cfgs_3359_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg___boxed(lean_object* v_eval_3370_, lean_object* v_init_3371_, lean_object* v_cfgs_3372_, lean_object* v_onErr_3373_, lean_object* v_logExceptions_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
uint8_t v_logExceptions_boxed_3382_; lean_object* v_res_3383_; 
v_logExceptions_boxed_3382_ = lean_unbox(v_logExceptions_3374_);
v_res_3383_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___redArg(v_eval_3370_, v_init_3371_, v_cfgs_3372_, v_onErr_3373_, v_logExceptions_boxed_3382_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec_ref(v_cfgs_3372_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(lean_object* v_00_u03b1_3384_, lean_object* v_eval_3385_, lean_object* v_init_3386_, lean_object* v_cfgs_3387_, lean_object* v_onErr_3388_, uint8_t v_logExceptions_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_3385_, v_logExceptions_3389_, v_onErr_3388_, v_init_3386_, v_cfgs_3387_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs___boxed(lean_object* v_00_u03b1_3398_, lean_object* v_eval_3399_, lean_object* v_init_3400_, lean_object* v_cfgs_3401_, lean_object* v_onErr_3402_, lean_object* v_logExceptions_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
uint8_t v_logExceptions_boxed_3411_; lean_object* v_res_3412_; 
v_logExceptions_boxed_3411_ = lean_unbox(v_logExceptions_3403_);
v_res_3412_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs(v_00_u03b1_3398_, v_eval_3399_, v_init_3400_, v_cfgs_3401_, v_onErr_3402_, v_logExceptions_boxed_3411_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec_ref(v_cfgs_3401_);
return v_res_3412_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(lean_object* v_x_3413_){
_start:
{
uint8_t v___x_3414_; 
v___x_3414_ = 0;
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0___boxed(lean_object* v_x_3415_){
_start:
{
uint8_t v_res_3416_; lean_object* v_r_3417_; 
v_res_3416_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg___lam__0(v_x_3415_);
lean_dec(v_x_3415_);
v_r_3417_ = lean_box(v_res_3416_);
return v_r_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(lean_object* v___x_3418_, lean_object* v_ctx_x3f_3419_, size_t v_sz_3420_, size_t v_i_3421_, lean_object* v_bs_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
uint8_t v___x_3430_; 
v___x_3430_ = lean_usize_dec_lt(v_i_3421_, v_sz_3420_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; 
lean_dec_ref(v_ctx_x3f_3419_);
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v_bs_3422_);
return v___x_3431_;
}
else
{
lean_object* v_assignment_3432_; lean_object* v___x_3433_; 
v_assignment_3432_ = lean_ctor_get(v___x_3418_, 0);
lean_inc_ref(v_ctx_x3f_3419_);
lean_inc(v___y_3428_);
lean_inc_ref(v___y_3427_);
lean_inc(v___y_3426_);
lean_inc_ref(v___y_3425_);
lean_inc(v___y_3424_);
lean_inc_ref(v___y_3423_);
v___x_3433_ = lean_apply_7(v_ctx_x3f_3419_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, lean_box(0));
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v_v_3435_; lean_object* v___x_3436_; lean_object* v_bs_x27_3437_; lean_object* v_a_3439_; lean_object* v_tree_3444_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v_v_3435_ = lean_array_uget(v_bs_3422_, v_i_3421_);
v___x_3436_ = lean_unsigned_to_nat(0u);
v_bs_x27_3437_ = lean_array_uset(v_bs_3422_, v_i_3421_, v___x_3436_);
v_tree_3444_ = l_Lean_Elab_InfoTree_substitute(v_v_3435_, v_assignment_3432_);
if (lean_obj_tag(v_a_3434_) == 0)
{
v_a_3439_ = v_tree_3444_;
goto v___jp_3438_;
}
else
{
lean_object* v_val_3445_; lean_object* v___x_3446_; 
v_val_3445_ = lean_ctor_get(v_a_3434_, 0);
lean_inc(v_val_3445_);
lean_dec_ref_known(v_a_3434_, 1);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_val_3445_);
lean_ctor_set(v___x_3446_, 1, v_tree_3444_);
v_a_3439_ = v___x_3446_;
goto v___jp_3438_;
}
v___jp_3438_:
{
size_t v___x_3440_; size_t v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = ((size_t)1ULL);
v___x_3441_ = lean_usize_add(v_i_3421_, v___x_3440_);
v___x_3442_ = lean_array_uset(v_bs_x27_3437_, v_i_3421_, v_a_3439_);
v_i_3421_ = v___x_3441_;
v_bs_3422_ = v___x_3442_;
goto _start;
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v_bs_3422_);
lean_dec_ref(v_ctx_x3f_3419_);
v_a_3447_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3433_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3433_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v___x_3455_, lean_object* v_ctx_x3f_3456_, lean_object* v_sz_3457_, lean_object* v_i_3458_, lean_object* v_bs_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
size_t v_sz_boxed_3467_; size_t v_i_boxed_3468_; lean_object* v_res_3469_; 
v_sz_boxed_3467_ = lean_unbox_usize(v_sz_3457_);
lean_dec(v_sz_3457_);
v_i_boxed_3468_ = lean_unbox_usize(v_i_3458_);
lean_dec(v_i_3458_);
v_res_3469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3455_, v_ctx_x3f_3456_, v_sz_boxed_3467_, v_i_boxed_3468_, v_bs_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___x_3455_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(lean_object* v___x_3470_, lean_object* v_ctx_x3f_3471_, lean_object* v_x_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
if (lean_obj_tag(v_x_3472_) == 0)
{
lean_object* v_cs_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3506_; 
v_cs_3480_ = lean_ctor_get(v_x_3472_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_x_3472_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3482_ = v_x_3472_;
v_isShared_3483_ = v_isSharedCheck_3506_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_cs_3480_);
lean_dec(v_x_3472_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3506_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
size_t v_sz_3484_; size_t v___x_3485_; lean_object* v___x_3486_; 
v_sz_3484_ = lean_array_size(v_cs_3480_);
v___x_3485_ = ((size_t)0ULL);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3470_, v_ctx_x3f_3471_, v_sz_3484_, v___x_3485_, v_cs_3480_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3497_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v_a_3487_);
v___x_3492_ = v___x_3482_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_del_object(v___x_3482_);
v_a_3498_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3486_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3486_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
else
{
lean_object* v_vs_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3533_; 
v_vs_3507_ = lean_ctor_get(v_x_3472_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_x_3472_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3509_ = v_x_3472_;
v_isShared_3510_ = v_isSharedCheck_3533_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_vs_3507_);
lean_dec(v_x_3472_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3533_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
size_t v_sz_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v_sz_3511_ = lean_array_size(v_vs_3507_);
v___x_3512_ = ((size_t)0ULL);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3470_, v_ctx_x3f_3471_, v_sz_3511_, v___x_3512_, v_vs_3507_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
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
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v_a_3514_);
v___x_3519_ = v___x_3509_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3514_);
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
lean_del_object(v___x_3509_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v___x_3534_, lean_object* v_ctx_x3f_3535_, size_t v_sz_3536_, size_t v_i_3537_, lean_object* v_bs_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
uint8_t v___x_3546_; 
v___x_3546_ = lean_usize_dec_lt(v_i_3537_, v_sz_3536_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec_ref(v_ctx_x3f_3535_);
v___x_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3547_, 0, v_bs_3538_);
return v___x_3547_;
}
else
{
lean_object* v_v_3548_; lean_object* v___x_3549_; 
v_v_3548_ = lean_array_uget_borrowed(v_bs_3538_, v_i_3537_);
lean_inc(v_v_3548_);
lean_inc_ref(v_ctx_x3f_3535_);
v___x_3549_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3534_, v_ctx_x3f_3535_, v_v_3548_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; lean_object* v_bs_x27_3552_; size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3551_ = lean_unsigned_to_nat(0u);
v_bs_x27_3552_ = lean_array_uset(v_bs_3538_, v_i_3537_, v___x_3551_);
v___x_3553_ = ((size_t)1ULL);
v___x_3554_ = lean_usize_add(v_i_3537_, v___x_3553_);
v___x_3555_ = lean_array_uset(v_bs_x27_3552_, v_i_3537_, v_a_3550_);
v_i_3537_ = v___x_3554_;
v_bs_3538_ = v___x_3555_;
goto _start;
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref(v_bs_3538_);
lean_dec_ref(v_ctx_x3f_3535_);
v_a_3557_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3549_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3549_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v___x_3565_, lean_object* v_ctx_x3f_3566_, lean_object* v_sz_3567_, lean_object* v_i_3568_, lean_object* v_bs_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
size_t v_sz_boxed_3577_; size_t v_i_boxed_3578_; lean_object* v_res_3579_; 
v_sz_boxed_3577_ = lean_unbox_usize(v_sz_3567_);
lean_dec(v_sz_3567_);
v_i_boxed_3578_ = lean_unbox_usize(v_i_3568_);
lean_dec(v_i_3568_);
v_res_3579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5_spec__6(v___x_3565_, v_ctx_x3f_3566_, v_sz_boxed_3577_, v_i_boxed_3578_, v_bs_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___x_3565_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v___x_3580_, lean_object* v_ctx_x3f_3581_, lean_object* v_x_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3580_, v_ctx_x3f_3581_, v_x_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v___x_3580_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(lean_object* v___x_3591_, lean_object* v_ctx_x3f_3592_, lean_object* v_t_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_root_3601_; lean_object* v_tail_3602_; lean_object* v_size_3603_; size_t v_shift_3604_; lean_object* v_tailOff_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3641_; 
v_root_3601_ = lean_ctor_get(v_t_3593_, 0);
v_tail_3602_ = lean_ctor_get(v_t_3593_, 1);
v_size_3603_ = lean_ctor_get(v_t_3593_, 2);
v_shift_3604_ = lean_ctor_get_usize(v_t_3593_, 4);
v_tailOff_3605_ = lean_ctor_get(v_t_3593_, 3);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_t_3593_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3607_ = v_t_3593_;
v_isShared_3608_ = v_isSharedCheck_3641_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_tailOff_3605_);
lean_inc(v_size_3603_);
lean_inc(v_tail_3602_);
lean_inc(v_root_3601_);
lean_dec(v_t_3593_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3641_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; 
lean_inc_ref(v_ctx_x3f_3592_);
v___x_3609_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__5(v___x_3591_, v_ctx_x3f_3592_, v_root_3601_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; size_t v_sz_3611_; size_t v___x_3612_; lean_object* v___x_3613_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v_sz_3611_ = lean_array_size(v_tail_3602_);
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4_spec__6(v___x_3591_, v_ctx_x3f_3592_, v_sz_3611_, v___x_3612_, v_tail_3602_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3624_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 1, v_a_3614_);
lean_ctor_set(v___x_3607_, 0, v_a_3610_);
v___x_3619_ = v___x_3607_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3610_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_a_3614_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v_size_3603_);
lean_ctor_set(v_reuseFailAlloc_3623_, 3, v_tailOff_3605_);
lean_ctor_set_usize(v_reuseFailAlloc_3623_, 4, v_shift_3604_);
v___x_3619_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3621_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3619_);
v___x_3621_ = v___x_3616_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v_a_3610_);
lean_del_object(v___x_3607_);
lean_dec(v_tailOff_3605_);
lean_dec(v_size_3603_);
v_a_3625_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3613_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3613_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_del_object(v___x_3607_);
lean_dec(v_tailOff_3605_);
lean_dec(v_size_3603_);
lean_dec_ref(v_tail_3602_);
lean_dec_ref(v_ctx_x3f_3592_);
v_a_3633_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3609_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3609_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4___boxed(lean_object* v___x_3642_, lean_object* v_ctx_x3f_3643_, lean_object* v_t_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v___x_3642_, v_ctx_x3f_3643_, v_t_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v___x_3642_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(lean_object* v___y_3653_, lean_object* v_ctx_x3f_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v_a_3660_, lean_object* v_a_x3f_3661_){
_start:
{
lean_object* v___x_3663_; lean_object* v_infoState_3664_; lean_object* v_trees_3665_; lean_object* v___x_3666_; 
v___x_3663_ = lean_st_ref_get(v___y_3653_);
v_infoState_3664_ = lean_ctor_get(v___x_3663_, 7);
lean_inc_ref(v_infoState_3664_);
lean_dec(v___x_3663_);
v_trees_3665_ = lean_ctor_get(v_infoState_3664_, 2);
lean_inc_ref(v_trees_3665_);
v___x_3666_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__4(v_infoState_3664_, v_ctx_x3f_3654_, v_trees_3665_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3653_);
lean_dec_ref(v_infoState_3664_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3705_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3705_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3705_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v_infoState_3672_; lean_object* v_env_3673_; lean_object* v_nextMacroScope_3674_; lean_object* v_ngen_3675_; lean_object* v_auxDeclNGen_3676_; lean_object* v_traceState_3677_; lean_object* v_cache_3678_; lean_object* v_messages_3679_; lean_object* v_snapshotTasks_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3704_; 
v___x_3671_ = lean_st_ref_take(v___y_3653_);
v_infoState_3672_ = lean_ctor_get(v___x_3671_, 7);
v_env_3673_ = lean_ctor_get(v___x_3671_, 0);
v_nextMacroScope_3674_ = lean_ctor_get(v___x_3671_, 1);
v_ngen_3675_ = lean_ctor_get(v___x_3671_, 2);
v_auxDeclNGen_3676_ = lean_ctor_get(v___x_3671_, 3);
v_traceState_3677_ = lean_ctor_get(v___x_3671_, 4);
v_cache_3678_ = lean_ctor_get(v___x_3671_, 5);
v_messages_3679_ = lean_ctor_get(v___x_3671_, 6);
v_snapshotTasks_3680_ = lean_ctor_get(v___x_3671_, 8);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3682_ = v___x_3671_;
v_isShared_3683_ = v_isSharedCheck_3704_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_snapshotTasks_3680_);
lean_inc(v_infoState_3672_);
lean_inc(v_messages_3679_);
lean_inc(v_cache_3678_);
lean_inc(v_traceState_3677_);
lean_inc(v_auxDeclNGen_3676_);
lean_inc(v_ngen_3675_);
lean_inc(v_nextMacroScope_3674_);
lean_inc(v_env_3673_);
lean_dec(v___x_3671_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3704_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
uint8_t v_enabled_3684_; lean_object* v_assignment_3685_; lean_object* v_lazyAssignment_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3702_; 
v_enabled_3684_ = lean_ctor_get_uint8(v_infoState_3672_, sizeof(void*)*3);
v_assignment_3685_ = lean_ctor_get(v_infoState_3672_, 0);
v_lazyAssignment_3686_ = lean_ctor_get(v_infoState_3672_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_infoState_3672_);
if (v_isSharedCheck_3702_ == 0)
{
lean_object* v_unused_3703_; 
v_unused_3703_ = lean_ctor_get(v_infoState_3672_, 2);
lean_dec(v_unused_3703_);
v___x_3688_ = v_infoState_3672_;
v_isShared_3689_ = v_isSharedCheck_3702_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_lazyAssignment_3686_);
lean_inc(v_assignment_3685_);
lean_dec(v_infoState_3672_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3702_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3690_ = l_Lean_PersistentArray_append___redArg(v_a_3660_, v_a_3667_);
lean_dec(v_a_3667_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 2, v___x_3690_);
v___x_3692_ = v___x_3688_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_assignment_3685_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_lazyAssignment_3686_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v___x_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3701_, sizeof(void*)*3, v_enabled_3684_);
v___x_3692_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 7, v___x_3692_);
v___x_3694_ = v___x_3682_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_env_3673_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_nextMacroScope_3674_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_ngen_3675_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v_auxDeclNGen_3676_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v_traceState_3677_);
lean_ctor_set(v_reuseFailAlloc_3700_, 5, v_cache_3678_);
lean_ctor_set(v_reuseFailAlloc_3700_, 6, v_messages_3679_);
lean_ctor_set(v_reuseFailAlloc_3700_, 7, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3700_, 8, v_snapshotTasks_3680_);
v___x_3694_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3695_ = lean_st_ref_set(v___y_3653_, v___x_3694_);
v___x_3696_ = lean_box(0);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3696_);
v___x_3698_ = v___x_3669_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_a_3660_);
v_a_3706_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3666_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3666_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___y_3714_, lean_object* v_ctx_x3f_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v_a_3721_, lean_object* v_a_x3f_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3714_, v_ctx_x3f_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v_a_3721_, v_a_x3f_3722_);
lean_dec(v_a_x3f_3722_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3714_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(lean_object* v___y_3725_){
_start:
{
lean_object* v___x_3727_; lean_object* v_infoState_3728_; lean_object* v_trees_3729_; lean_object* v___x_3730_; lean_object* v_infoState_3731_; lean_object* v_env_3732_; lean_object* v_nextMacroScope_3733_; lean_object* v_ngen_3734_; lean_object* v_auxDeclNGen_3735_; lean_object* v_traceState_3736_; lean_object* v_cache_3737_; lean_object* v_messages_3738_; lean_object* v_snapshotTasks_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3762_; 
v___x_3727_ = lean_st_ref_get(v___y_3725_);
v_infoState_3728_ = lean_ctor_get(v___x_3727_, 7);
lean_inc_ref(v_infoState_3728_);
lean_dec(v___x_3727_);
v_trees_3729_ = lean_ctor_get(v_infoState_3728_, 2);
lean_inc_ref(v_trees_3729_);
lean_dec_ref(v_infoState_3728_);
v___x_3730_ = lean_st_ref_take(v___y_3725_);
v_infoState_3731_ = lean_ctor_get(v___x_3730_, 7);
v_env_3732_ = lean_ctor_get(v___x_3730_, 0);
v_nextMacroScope_3733_ = lean_ctor_get(v___x_3730_, 1);
v_ngen_3734_ = lean_ctor_get(v___x_3730_, 2);
v_auxDeclNGen_3735_ = lean_ctor_get(v___x_3730_, 3);
v_traceState_3736_ = lean_ctor_get(v___x_3730_, 4);
v_cache_3737_ = lean_ctor_get(v___x_3730_, 5);
v_messages_3738_ = lean_ctor_get(v___x_3730_, 6);
v_snapshotTasks_3739_ = lean_ctor_get(v___x_3730_, 8);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3741_ = v___x_3730_;
v_isShared_3742_ = v_isSharedCheck_3762_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_snapshotTasks_3739_);
lean_inc(v_infoState_3731_);
lean_inc(v_messages_3738_);
lean_inc(v_cache_3737_);
lean_inc(v_traceState_3736_);
lean_inc(v_auxDeclNGen_3735_);
lean_inc(v_ngen_3734_);
lean_inc(v_nextMacroScope_3733_);
lean_inc(v_env_3732_);
lean_dec(v___x_3730_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3762_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
uint8_t v_enabled_3743_; lean_object* v_assignment_3744_; lean_object* v_lazyAssignment_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3760_; 
v_enabled_3743_ = lean_ctor_get_uint8(v_infoState_3731_, sizeof(void*)*3);
v_assignment_3744_ = lean_ctor_get(v_infoState_3731_, 0);
v_lazyAssignment_3745_ = lean_ctor_get(v_infoState_3731_, 1);
v_isSharedCheck_3760_ = !lean_is_exclusive(v_infoState_3731_);
if (v_isSharedCheck_3760_ == 0)
{
lean_object* v_unused_3761_; 
v_unused_3761_ = lean_ctor_get(v_infoState_3731_, 2);
lean_dec(v_unused_3761_);
v___x_3747_ = v_infoState_3731_;
v_isShared_3748_ = v_isSharedCheck_3760_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_lazyAssignment_3745_);
lean_inc(v_assignment_3744_);
lean_dec(v_infoState_3731_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3760_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3749_ = lean_unsigned_to_nat(32u);
v___x_3750_ = lean_mk_empty_array_with_capacity(v___x_3749_);
lean_dec_ref(v___x_3750_);
v___x_3751_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__1___closed__1);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 2, v___x_3751_);
v___x_3753_ = v___x_3747_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_assignment_3744_);
lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_lazyAssignment_3745_);
lean_ctor_set(v_reuseFailAlloc_3759_, 2, v___x_3751_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, sizeof(void*)*3, v_enabled_3743_);
v___x_3753_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3755_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 7, v___x_3753_);
v___x_3755_ = v___x_3741_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_env_3732_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_nextMacroScope_3733_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_ngen_3734_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_auxDeclNGen_3735_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_traceState_3736_);
lean_ctor_set(v_reuseFailAlloc_3758_, 5, v_cache_3737_);
lean_ctor_set(v_reuseFailAlloc_3758_, 6, v_messages_3738_);
lean_ctor_set(v_reuseFailAlloc_3758_, 7, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3758_, 8, v_snapshotTasks_3739_);
v___x_3755_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = lean_st_ref_set(v___y_3725_, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3757_, 0, v_trees_3729_);
return v___x_3757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3763_);
lean_dec(v___y_3763_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(lean_object* v_x_3766_, lean_object* v_ctx_x3f_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v_infoState_3776_; uint8_t v_enabled_3777_; 
v___x_3775_ = lean_st_ref_get(v___y_3773_);
v_infoState_3776_ = lean_ctor_get(v___x_3775_, 7);
lean_inc_ref(v_infoState_3776_);
lean_dec(v___x_3775_);
v_enabled_3777_ = lean_ctor_get_uint8(v_infoState_3776_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3776_);
if (v_enabled_3777_ == 0)
{
lean_object* v___x_3778_; 
lean_dec_ref(v_ctx_x3f_3767_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
lean_inc(v___y_3771_);
lean_inc_ref(v___y_3770_);
lean_inc(v___y_3769_);
lean_inc_ref(v___y_3768_);
v___x_3778_ = lean_apply_7(v_x_3766_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, lean_box(0));
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v_a_3780_; lean_object* v_r_3781_; 
v___x_3779_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_3773_);
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref(v___x_3779_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
lean_inc(v___y_3771_);
lean_inc_ref(v___y_3770_);
lean_inc(v___y_3769_);
lean_inc_ref(v___y_3768_);
v_r_3781_ = lean_apply_7(v_x_3766_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, lean_box(0));
if (lean_obj_tag(v_r_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3806_; 
v_a_3782_ = lean_ctor_get(v_r_3781_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_r_3781_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3784_ = v_r_3781_;
v_isShared_3785_ = v_isSharedCheck_3806_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v_r_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3806_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
lean_inc(v_a_3782_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set_tag(v___x_3784_, 1);
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3788_; 
v___x_3788_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3773_, v_ctx_x3f_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v_a_3780_, v___x_3787_);
lean_dec_ref(v___x_3787_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; 
v_unused_3796_ = lean_ctor_get(v___x_3788_, 0);
lean_dec(v_unused_3796_);
v___x_3790_ = v___x_3788_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v___x_3788_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_a_3782_);
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3782_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3782_);
v_a_3797_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3788_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3788_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
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
else
{
lean_object* v_a_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_a_3807_ = lean_ctor_get(v_r_3781_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v_r_3781_, 1);
v___x_3808_ = lean_box(0);
v___x_3809_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___lam__0(v___y_3773_, v_ctx_x3f_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v_a_3780_, v___x_3808_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v___x_3809_, 0);
lean_dec(v_unused_3817_);
v___x_3811_ = v___x_3809_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_dec(v___x_3809_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set_tag(v___x_3811_, 1);
lean_ctor_set(v___x_3811_, 0, v_a_3807_);
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3807_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_a_3807_);
v_a_3818_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3809_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3809_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_3826_, lean_object* v_ctx_x3f_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3826_, v_ctx_x3f_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; lean_object* v_env_3841_; lean_object* v___x_3842_; lean_object* v_mctx_3843_; lean_object* v_options_3844_; lean_object* v_currNamespace_3845_; lean_object* v_openDecls_3846_; lean_object* v___x_3847_; lean_object* v_ngen_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3840_ = lean_st_ref_get(v___y_3838_);
v_env_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc_ref(v_env_3841_);
lean_dec(v___x_3840_);
v___x_3842_ = lean_st_ref_get(v___y_3836_);
v_mctx_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc_ref(v_mctx_3843_);
lean_dec(v___x_3842_);
v_options_3844_ = lean_ctor_get(v___y_3837_, 2);
v_currNamespace_3845_ = lean_ctor_get(v___y_3837_, 6);
v_openDecls_3846_ = lean_ctor_get(v___y_3837_, 7);
v___x_3847_ = lean_st_ref_get(v___y_3838_);
v_ngen_3848_ = lean_ctor_get(v___x_3847_, 2);
lean_inc_ref(v_ngen_3848_);
lean_dec(v___x_3847_);
v___x_3849_ = lean_box(0);
v___x_3850_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_3846_);
lean_inc(v_currNamespace_3845_);
lean_inc_ref(v_options_3844_);
v___x_3851_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3851_, 0, v_env_3841_);
lean_ctor_set(v___x_3851_, 1, v___x_3849_);
lean_ctor_set(v___x_3851_, 2, v___x_3850_);
lean_ctor_set(v___x_3851_, 3, v_mctx_3843_);
lean_ctor_set(v___x_3851_, 4, v_options_3844_);
lean_ctor_set(v___x_3851_, 5, v_currNamespace_3845_);
lean_ctor_set(v___x_3851_, 6, v_openDecls_3846_);
lean_ctor_set(v___x_3851_, 7, v_ngen_3848_);
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v___x_3865_; lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3890_; 
v___x_3865_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_3861_, v___y_3862_, v___y_3863_);
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3890_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3890_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_fileMap_3870_; lean_object* v_env_3871_; lean_object* v_mctx_3872_; lean_object* v_options_3873_; lean_object* v_currNamespace_3874_; lean_object* v_openDecls_3875_; lean_object* v_ngen_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3887_; 
v_fileMap_3870_ = lean_ctor_get(v___y_3862_, 1);
v_env_3871_ = lean_ctor_get(v_a_3866_, 0);
v_mctx_3872_ = lean_ctor_get(v_a_3866_, 3);
v_options_3873_ = lean_ctor_get(v_a_3866_, 4);
v_currNamespace_3874_ = lean_ctor_get(v_a_3866_, 5);
v_openDecls_3875_ = lean_ctor_get(v_a_3866_, 6);
v_ngen_3876_ = lean_ctor_get(v_a_3866_, 7);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_a_3866_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; 
v_unused_3888_ = lean_ctor_get(v_a_3866_, 2);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_a_3866_, 1);
lean_dec(v_unused_3889_);
v___x_3878_ = v_a_3866_;
v_isShared_3879_ = v_isSharedCheck_3887_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_ngen_3876_);
lean_inc(v_openDecls_3875_);
lean_inc(v_currNamespace_3874_);
lean_inc(v_options_3873_);
lean_inc(v_mctx_3872_);
lean_inc(v_env_3871_);
lean_dec(v_a_3866_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3887_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; lean_object* v___x_3882_; 
v___x_3880_ = lean_box(0);
lean_inc_ref(v_fileMap_3870_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 2, v_fileMap_3870_);
lean_ctor_set(v___x_3878_, 1, v___x_3880_);
v___x_3882_ = v___x_3878_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_env_3871_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v_fileMap_3870_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v_mctx_3872_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v_options_3873_);
lean_ctor_set(v_reuseFailAlloc_3886_, 5, v_currNamespace_3874_);
lean_ctor_set(v_reuseFailAlloc_3886_, 6, v_openDecls_3875_);
lean_ctor_set(v_reuseFailAlloc_3886_, 7, v_ngen_3876_);
v___x_3882_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3882_);
v___x_3884_ = v___x_3868_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0___boxed(lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___x_3906_; lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3916_; 
v___x_3906_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0(v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3916_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3916_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v_a_3907_);
v___x_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3912_);
v___x_3914_ = v___x_3909_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0___boxed(lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___lam__0(v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(lean_object* v_x_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v___f_3934_; lean_object* v___x_3935_; 
v___f_3934_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___closed__0));
v___x_3935_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_3926_, v___f_3934_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg___boxed(lean_object* v_x_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(lean_object* v_00_u03b1_3945_, lean_object* v_x_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___redArg(v_x_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed(lean_object* v_00_u03b1_3955_, lean_object* v_x_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0(v_00_u03b1_3955_, v_x_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
return v_res_3964_;
}
}
static uint64_t _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4(void){
_start:
{
lean_object* v___x_3982_; uint64_t v___x_3983_; 
v___x_3982_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3983_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3982_);
return v___x_3983_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5(void){
_start:
{
uint64_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = lean_uint64_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__4);
v___x_3985_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__3));
v___x_3986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
lean_ctor_set_uint64(v___x_3986_, sizeof(void*)*1, v___x_3984_);
return v___x_3986_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6(void){
_start:
{
uint8_t v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3987_ = 1;
v___x_3988_ = lean_unsigned_to_nat(0u);
v___x_3989_ = lean_box(0);
v___x_3990_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__1));
v___x_3991_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__2);
v___x_3992_ = lean_box(1);
v___x_3993_ = 0;
v___x_3994_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__5);
v___x_3995_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
lean_ctor_set(v___x_3995_, 1, v___x_3992_);
lean_ctor_set(v___x_3995_, 2, v___x_3991_);
lean_ctor_set(v___x_3995_, 3, v___x_3990_);
lean_ctor_set(v___x_3995_, 4, v___x_3989_);
lean_ctor_set(v___x_3995_, 5, v___x_3988_);
lean_ctor_set(v___x_3995_, 6, v___x_3989_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*7, v___x_3993_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*7 + 1, v___x_3993_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*7 + 2, v___x_3993_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*7 + 3, v___x_3987_);
return v___x_3995_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_3997_ = lean_unsigned_to_nat(0u);
v___x_3998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
lean_ctor_set(v___x_3998_, 2, v___x_3997_);
lean_ctor_set(v___x_3998_, 3, v___x_3997_);
lean_ctor_set(v___x_3998_, 4, v___x_3996_);
lean_ctor_set(v___x_3998_, 5, v___x_3996_);
lean_ctor_set(v___x_3998_, 6, v___x_3996_);
lean_ctor_set(v___x_3998_, 7, v___x_3996_);
lean_ctor_set(v___x_3998_, 8, v___x_3996_);
lean_ctor_set(v___x_3998_, 9, v___x_3996_);
return v___x_3998_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_4000_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
lean_ctor_set(v___x_4000_, 2, v___x_3999_);
lean_ctor_set(v___x_4000_, 3, v___x_3999_);
lean_ctor_set(v___x_4000_, 4, v___x_3999_);
lean_ctor_set(v___x_4000_, 5, v___x_3999_);
return v___x_4000_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_obj_once(&l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1, &l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1_once, _init_l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo___closed__1);
v___x_4002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
lean_ctor_set(v___x_4002_, 2, v___x_4001_);
lean_ctor_set(v___x_4002_, 3, v___x_4001_);
lean_ctor_set(v___x_4002_, 4, v___x_4001_);
return v___x_4002_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4003_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__9);
v___x_4004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_ConfigEval_ConfigItem_addConstInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_4005_ = lean_box(1);
v___x_4006_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__8);
v___x_4007_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__7);
v___x_4008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
lean_ctor_set(v___x_4008_, 1, v___x_4006_);
lean_ctor_set(v___x_4008_, 2, v___x_4005_);
lean_ctor_set(v___x_4008_, 3, v___x_4004_);
lean_ctor_set(v___x_4008_, 4, v___x_4003_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg(lean_object* v_mx_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4016_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__2));
v___x_4017_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__6);
v___x_4018_ = lean_obj_once(&l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10, &l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10_once, _init_l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__10);
v___x_4019_ = lean_st_mk_ref(v___x_4018_);
v___x_4020_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4020_, 0, lean_box(0));
lean_closure_set(v___x_4020_, 1, v_mx_4012_);
v___x_4021_ = ((lean_object*)(l_Lean_Elab_ConfigEval_runConfigElab___redArg___closed__11));
v___x_4022_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_4020_, v___x_4016_, v___x_4021_, v___x_4017_, v___x_4019_, v_a_4013_, v_a_4014_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4032_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v_fst_4028_; lean_object* v___x_4030_; 
v___x_4027_ = lean_st_ref_get(v___x_4019_);
lean_dec(v___x_4019_);
lean_dec(v___x_4027_);
v_fst_4028_ = lean_ctor_get(v_a_4023_, 0);
lean_inc(v_fst_4028_);
lean_dec(v_a_4023_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v_fst_4028_);
v___x_4030_ = v___x_4025_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_fst_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v___x_4019_);
v_a_4033_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4022_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4022_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___redArg___boxed(lean_object* v_mx_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_4041_, v_a_4042_, v_a_4043_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab(lean_object* v_00_u03b1_4046_, lean_object* v_mx_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v_mx_4047_, v_a_4048_, v_a_4049_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_runConfigElab___boxed(lean_object* v_00_u03b1_4052_, lean_object* v_mx_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Lean_Elab_ConfigEval_runConfigElab(v_00_u03b1_4052_, v_mx_4053_, v_a_4054_, v_a_4055_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___redArg(v___y_4061_, v___y_4062_, v___y_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1___boxed(lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__0_spec__1(v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___redArg(v___y_4079_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3___boxed(lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1_spec__3(v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(lean_object* v_00_u03b1_4090_, lean_object* v_x_4091_, lean_object* v_ctx_x3f_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___redArg(v_x_4091_, v_ctx_x3f_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4101_, lean_object* v_x_4102_, lean_object* v_ctx_x3f_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_ConfigEval_runConfigElab_spec__0_spec__1(v_00_u03b1_4101_, v_x_4102_, v_ctx_x3f_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(lean_object* v_eval_4112_, uint8_t v_logExceptions_4113_, lean_object* v_onErr_4114_, lean_object* v_init_4115_, lean_object* v_cfg_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0___redArg(v_eval_4112_, v_logExceptions_4113_, v_onErr_4114_, v_init_4115_, v_cfg_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed(lean_object* v_eval_4125_, lean_object* v_logExceptions_4126_, lean_object* v_onErr_4127_, lean_object* v_init_4128_, lean_object* v_cfg_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
uint8_t v_logExceptions_boxed_4137_; lean_object* v_res_4138_; 
v_logExceptions_boxed_4137_ = lean_unbox(v_logExceptions_4126_);
v_res_4138_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0(v_eval_4125_, v_logExceptions_boxed_4137_, v_onErr_4127_, v_init_4128_, v_cfg_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object* v_eval_4139_, lean_object* v_init_4140_, lean_object* v_cfg_4141_, lean_object* v_onErr_4142_, uint8_t v_logExceptions_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4147_; lean_object* v___f_4148_; uint8_t v___y_4150_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
v___x_4147_ = lean_box(v_logExceptions_4143_);
lean_inc_n(v_cfg_4141_, 2);
lean_inc(v_init_4140_);
v___f_4148_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4148_, 0, v_eval_4139_);
lean_closure_set(v___f_4148_, 1, v___x_4147_);
lean_closure_set(v___f_4148_, 2, v_onErr_4142_);
lean_closure_set(v___f_4148_, 3, v_init_4140_);
lean_closure_set(v___f_4148_, 4, v_cfg_4141_);
v___x_4153_ = lean_unsigned_to_nat(0u);
v___x_4154_ = l_Lean_Syntax_matchesNull(v_cfg_4141_, v___x_4153_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v___x_4155_ = l_Lean_Syntax_getNumArgs(v_cfg_4141_);
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = lean_nat_dec_eq(v___x_4155_, v___x_4156_);
lean_dec(v___x_4155_);
if (v___x_4157_ == 0)
{
lean_dec(v_cfg_4141_);
v___y_4150_ = v___x_4157_;
goto v___jp_4149_;
}
else
{
lean_object* v___x_4158_; uint8_t v___x_4159_; 
v___x_4158_ = l_Lean_Syntax_getArg(v_cfg_4141_, v___x_4153_);
lean_dec(v_cfg_4141_);
v___x_4159_ = l_Lean_Syntax_matchesNull(v___x_4158_, v___x_4153_);
v___y_4150_ = v___x_4159_;
goto v___jp_4149_;
}
}
else
{
lean_dec(v_cfg_4141_);
v___y_4150_ = v___x_4154_;
goto v___jp_4149_;
}
v___jp_4149_:
{
if (v___y_4150_ == 0)
{
lean_object* v___x_4151_; 
lean_dec(v_init_4140_);
v___x_4151_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4148_, v_a_4144_, v_a_4145_);
return v___x_4151_;
}
else
{
lean_object* v___x_4152_; 
lean_dec_ref(v___f_4148_);
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v_init_4140_);
return v___x_4152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg___boxed(lean_object* v_eval_4160_, lean_object* v_init_4161_, lean_object* v_cfg_4162_, lean_object* v_onErr_4163_, lean_object* v_logExceptions_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
uint8_t v_logExceptions_boxed_4168_; lean_object* v_res_4169_; 
v_logExceptions_boxed_4168_ = lean_unbox(v_logExceptions_4164_);
v_res_4169_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4160_, v_init_4161_, v_cfg_4162_, v_onErr_4163_, v_logExceptions_boxed_4168_, v_a_4165_, v_a_4166_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(lean_object* v_00_u03b1_4170_, lean_object* v_eval_4171_, lean_object* v_init_4172_, lean_object* v_cfg_4173_, lean_object* v_onErr_4174_, uint8_t v_logExceptions_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_4171_, v_init_4172_, v_cfg_4173_, v_onErr_4174_, v_logExceptions_4175_, v_a_4176_, v_a_4177_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___boxed(lean_object* v_00_u03b1_4180_, lean_object* v_eval_4181_, lean_object* v_init_4182_, lean_object* v_cfg_4183_, lean_object* v_onErr_4184_, lean_object* v_logExceptions_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
uint8_t v_logExceptions_boxed_4189_; lean_object* v_res_4190_; 
v_logExceptions_boxed_4189_ = lean_unbox(v_logExceptions_4185_);
v_res_4190_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27(v_00_u03b1_4180_, v_eval_4181_, v_init_4182_, v_cfg_4183_, v_onErr_4184_, v_logExceptions_boxed_4189_, v_a_4186_, v_a_4187_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(lean_object* v_eval_4191_, uint8_t v_logExceptions_4192_, lean_object* v_onErr_4193_, lean_object* v_init_4194_, lean_object* v_cfgs_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l_Lean_Elab_ConfigEval_foldConfigsM___at___00Lean_Elab_ConfigEval_foldConfigM___at___00Lean_Elab_ConfigEval_EvalConfigItem_setConfig_spec__0_spec__1___redArg(v_eval_4191_, v_logExceptions_4192_, v_onErr_4193_, v_init_4194_, v_cfgs_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed(lean_object* v_eval_4204_, lean_object* v_logExceptions_4205_, lean_object* v_onErr_4206_, lean_object* v_init_4207_, lean_object* v_cfgs_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
uint8_t v_logExceptions_boxed_4216_; lean_object* v_res_4217_; 
v_logExceptions_boxed_4216_ = lean_unbox(v_logExceptions_4205_);
v_res_4217_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0(v_eval_4204_, v_logExceptions_boxed_4216_, v_onErr_4206_, v_init_4207_, v_cfgs_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec_ref(v_cfgs_4208_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(lean_object* v_eval_4218_, lean_object* v_init_4219_, lean_object* v_cfgs_4220_, lean_object* v_onErr_4221_, uint8_t v_logExceptions_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
v___x_4226_ = lean_array_get_size(v_cfgs_4220_);
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = lean_nat_dec_eq(v___x_4226_, v___x_4227_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; lean_object* v___f_4230_; lean_object* v___x_4231_; 
v___x_4229_ = lean_box(v_logExceptions_4222_);
v___f_4230_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4230_, 0, v_eval_4218_);
lean_closure_set(v___f_4230_, 1, v___x_4229_);
lean_closure_set(v___f_4230_, 2, v_onErr_4221_);
lean_closure_set(v___f_4230_, 3, v_init_4219_);
lean_closure_set(v___f_4230_, 4, v_cfgs_4220_);
v___x_4231_ = l_Lean_Elab_ConfigEval_runConfigElab___redArg(v___f_4230_, v_a_4223_, v_a_4224_);
return v___x_4231_;
}
else
{
lean_object* v___x_4232_; 
lean_dec_ref(v_onErr_4221_);
lean_dec_ref(v_cfgs_4220_);
lean_dec_ref(v_eval_4218_);
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v_init_4219_);
return v___x_4232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg___boxed(lean_object* v_eval_4233_, lean_object* v_init_4234_, lean_object* v_cfgs_4235_, lean_object* v_onErr_4236_, lean_object* v_logExceptions_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
uint8_t v_logExceptions_boxed_4241_; lean_object* v_res_4242_; 
v_logExceptions_boxed_4241_ = lean_unbox(v_logExceptions_4237_);
v_res_4242_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4233_, v_init_4234_, v_cfgs_4235_, v_onErr_4236_, v_logExceptions_boxed_4241_, v_a_4238_, v_a_4239_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(lean_object* v_00_u03b1_4243_, lean_object* v_eval_4244_, lean_object* v_init_4245_, lean_object* v_cfgs_4246_, lean_object* v_onErr_4247_, uint8_t v_logExceptions_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___redArg(v_eval_4244_, v_init_4245_, v_cfgs_4246_, v_onErr_4247_, v_logExceptions_4248_, v_a_4249_, v_a_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27___boxed(lean_object* v_00_u03b1_4253_, lean_object* v_eval_4254_, lean_object* v_init_4255_, lean_object* v_cfgs_4256_, lean_object* v_onErr_4257_, lean_object* v_logExceptions_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_){
_start:
{
uint8_t v_logExceptions_boxed_4262_; lean_object* v_res_4263_; 
v_logExceptions_boxed_4262_ = lean_unbox(v_logExceptions_4258_);
v_res_4263_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfigs_x27(v_00_u03b1_4253_, v_eval_4254_, v_init_4255_, v_cfgs_4256_, v_onErr_4257_, v_logExceptions_boxed_4262_, v_a_4259_, v_a_4260_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
return v_res_4263_;
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

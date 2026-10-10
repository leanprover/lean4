// Lean compiler output
// Module: Lean.Meta.Native
// Imports: public import Lean.Meta.Basic import Lean.Util.CollectLevelParams import Lean.Elab.DeclarationRange import Lean.Compiler.Options
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
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
extern lean_object* l_Lean_Elab_async;
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
extern lean_object* l_Lean_declRangeExt;
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadEnvMetaM;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadOptionsCoreM;
lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_evalConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__14_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__15 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "` failed: Could not evaluate decidable instance. Error: "};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` failed. Error: "};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__8;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__9;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__10;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__11;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__0;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__1;
static const lean_array_object l_Lean_Meta_nativeEqTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__2 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__2_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__3;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_native"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__4 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__4_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 17, 188, 127, 248, 12, 59, 169)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__5 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__5_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "decl"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__6 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__6_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__6_value),LEAN_SCALAR_PTR_LITERAL(122, 197, 108, 116, 168, 105, 88, 191)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__7 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__7_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ax"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__8 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__8_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__8_value),LEAN_SCALAR_PTR_LITERAL(79, 222, 122, 135, 172, 245, 68, 224)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__9 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__9_value;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__10 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__10_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__11 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__11_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__12;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__13;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__14;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__15;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__16 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__16_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_nativeEqTrue___closed__16_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__17 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__17_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__18;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` failed: Cannot native decide proposition with metavariables:"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__19 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__19_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__20;
static const lean_string_object l_Lean_Meta_nativeEqTrue___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` failed: Cannot native decide proposition with free variables:"};
static const lean_object* l_Lean_Meta_nativeEqTrue___closed__21 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___closed__21_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_NativeEqTrueResult_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_prf_7_; lean_object* v___x_8_; 
v_prf_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_prf_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_prf_7_);
return v___x_8_;
}
else
{
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Meta_NativeEqTrueResult_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(lean_object* v_t_21_, lean_object* v_success_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_21_, v_success_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_success_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_25_, v_success_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(lean_object* v_t_29_, lean_object* v_notTrue_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_29_, v_notTrue_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_notTrue_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_33_, v_notTrue_35_);
return v___x_36_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_instMonadEIO___redArg();
return v___x_37_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0);
v___x_39_ = l_StateRefT_x27_instMonad___redArg(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6(void){
_start:
{
lean_object* v___x_44_; lean_object* v___f_45_; 
v___x_44_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_45_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_45_, 0, v___x_44_);
return v___f_45_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7(void){
_start:
{
lean_object* v___x_46_; lean_object* v___f_47_; 
v___x_46_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_47_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_47_, 0, v___x_46_);
return v___f_47_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8(void){
_start:
{
lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
v___f_48_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7);
v___f_49_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___f_49_);
lean_ctor_set(v___x_50_, 1, v___f_48_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9(void){
_start:
{
lean_object* v___x_51_; lean_object* v___f_52_; 
v___x_51_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8);
v___f_52_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_52_, 0, v___x_51_);
return v___f_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10(void){
_start:
{
lean_object* v___x_53_; lean_object* v___f_54_; 
v___x_53_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8);
v___f_54_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_54_, 0, v___x_53_);
return v___f_54_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11(void){
_start:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_57_; 
v___f_55_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10);
v___f_56_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___f_56_);
lean_ctor_set(v___x_57_, 1, v___f_55_);
return v___x_57_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__15));
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__14));
v___x_65_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_64_, v___x_63_, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17(void){
_start:
{
lean_object* v___x_66_; lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16);
v___f_67_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13));
v___f_68_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12));
v___x_69_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_68_, v___f_67_, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = l_Lean_Core_instMonadOptionsCoreM;
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__15));
v___x_72_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19(void){
_start:
{
lean_object* v___x_73_; lean_object* v___f_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18);
v___f_74_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13));
v___x_75_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___f_74_, v___x_73_);
return v___x_75_;
}
}
lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object* v_auxDeclName_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_toApplicative_83_; lean_object* v_toFunctor_84_; lean_object* v_toSeq_85_; lean_object* v_toSeqLeft_86_; lean_object* v_toSeqRight_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_toApplicative_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_137_; 
v___x_82_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1);
v_toApplicative_83_ = lean_ctor_get(v___x_82_, 0);
v_toFunctor_84_ = lean_ctor_get(v_toApplicative_83_, 0);
v_toSeq_85_ = lean_ctor_get(v_toApplicative_83_, 2);
v_toSeqLeft_86_ = lean_ctor_get(v_toApplicative_83_, 3);
v_toSeqRight_87_ = lean_ctor_get(v_toApplicative_83_, 4);
v___f_88_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__2));
v___f_89_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__3));
lean_inc_ref_n(v_toFunctor_84_, 2);
v___f_90_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_90_, 0, v_toFunctor_84_);
v___f_91_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_91_, 0, v_toFunctor_84_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___f_90_);
lean_ctor_set(v___x_92_, 1, v___f_91_);
lean_inc(v_toSeqRight_87_);
v___f_93_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_93_, 0, v_toSeqRight_87_);
lean_inc(v_toSeqLeft_86_);
v___f_94_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_94_, 0, v_toSeqLeft_86_);
lean_inc(v_toSeq_85_);
v___f_95_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_95_, 0, v_toSeq_85_);
v___x_96_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_96_, 0, v___x_92_);
lean_ctor_set(v___x_96_, 1, v___f_88_);
lean_ctor_set(v___x_96_, 2, v___f_95_);
lean_ctor_set(v___x_96_, 3, v___f_94_);
lean_ctor_set(v___x_96_, 4, v___f_93_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___f_89_);
v___x_98_ = l_StateRefT_x27_instMonad___redArg(v___x_97_);
v_toApplicative_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v___x_98_, 1);
lean_dec(v_unused_138_);
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_137_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_toApplicative_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_137_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_toFunctor_103_; lean_object* v_toSeq_104_; lean_object* v_toSeqLeft_105_; lean_object* v_toSeqRight_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_135_; 
v_toFunctor_103_ = lean_ctor_get(v_toApplicative_99_, 0);
v_toSeq_104_ = lean_ctor_get(v_toApplicative_99_, 2);
v_toSeqLeft_105_ = lean_ctor_get(v_toApplicative_99_, 3);
v_toSeqRight_106_ = lean_ctor_get(v_toApplicative_99_, 4);
v_isSharedCheck_135_ = !lean_is_exclusive(v_toApplicative_99_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v_toApplicative_99_, 1);
lean_dec(v_unused_136_);
v___x_108_ = v_toApplicative_99_;
v_isShared_109_ = v_isSharedCheck_135_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_toSeqRight_106_);
lean_inc(v_toSeqLeft_105_);
lean_inc(v_toSeq_104_);
lean_inc(v_toFunctor_103_);
lean_dec(v_toApplicative_99_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_135_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___x_119_; 
v___f_110_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__4));
v___f_111_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__5));
lean_inc_ref(v_toFunctor_103_);
v___f_112_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_112_, 0, v_toFunctor_103_);
v___f_113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_113_, 0, v_toFunctor_103_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___f_112_);
lean_ctor_set(v___x_114_, 1, v___f_113_);
v___f_115_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_115_, 0, v_toSeqRight_106_);
v___f_116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_116_, 0, v_toSeqLeft_105_);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_117_, 0, v_toSeq_104_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 4, v___f_115_);
lean_ctor_set(v___x_108_, 3, v___f_116_);
lean_ctor_set(v___x_108_, 2, v___f_117_);
lean_ctor_set(v___x_108_, 1, v___f_110_);
lean_ctor_set(v___x_108_, 0, v___x_114_);
v___x_119_ = v___x_108_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___f_110_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v___f_117_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v___f_116_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v___f_115_);
v___x_119_ = v_reuseFailAlloc_134_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___f_111_);
lean_ctor_set(v___x_101_, 0, v___x_119_);
v___x_121_ = v___x_101_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___f_111_);
v___x_121_ = v_reuseFailAlloc_133_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_toMonadRef_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_63__overap_131_; lean_object* v___x_132_; 
v___x_122_ = l_Lean_Meta_instMonadEnvMetaM;
v___x_123_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11);
v___x_124_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17);
v_toMonadRef_125_ = lean_ctor_get(v___x_124_, 0);
v___x_126_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_121_);
v___x_127_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_126_, v___x_121_);
lean_inc_ref(v_toMonadRef_125_);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_123_);
lean_ctor_set(v___x_128_, 1, v_toMonadRef_125_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19);
v___x_130_ = 1;
v___x_63__overap_131_ = l_Lean_evalConst___redArg(v___x_121_, v___x_122_, v___x_128_, v___x_129_, v_auxDeclName_76_, v___x_130_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
v___x_132_ = lean_apply_5(v___x_63__overap_131_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, lean_box(0));
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclName_76_ = stack[0].m_obj;
lean_object* v_a_77_ = stack[1].m_obj;
lean_object* v_a_78_ = stack[2].m_obj;
lean_object* v_a_79_ = stack[3].m_obj;
lean_object* v_a_80_ = stack[4].m_obj;
lean_object* v_res_139_;
v_res_139_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_auxDeclName_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(lean_object* v_auxDeclName_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_auxDeclName_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_146_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object* v_e_147_, lean_object* v___y_148_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = l_Lean_Expr_hasMVar(v_e_147_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v_e_147_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v_mctx_153_; lean_object* v___x_154_; lean_object* v_fst_155_; lean_object* v_snd_156_; lean_object* v___x_157_; lean_object* v_cache_158_; lean_object* v_zetaDeltaFVarIds_159_; lean_object* v_postponed_160_; lean_object* v_diag_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_170_; 
v___x_152_ = lean_st_ref_get(v___y_148_);
v_mctx_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc_ref(v_mctx_153_);
lean_dec(v___x_152_);
v___x_154_ = l_Lean_instantiateMVarsCore(v_mctx_153_, v_e_147_);
v_fst_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_fst_155_);
v_snd_156_ = lean_ctor_get(v___x_154_, 1);
lean_inc(v_snd_156_);
lean_dec_ref(v___x_154_);
v___x_157_ = lean_st_ref_take(v___y_148_);
v_cache_158_ = lean_ctor_get(v___x_157_, 1);
v_zetaDeltaFVarIds_159_ = lean_ctor_get(v___x_157_, 2);
v_postponed_160_ = lean_ctor_get(v___x_157_, 3);
v_diag_161_ = lean_ctor_get(v___x_157_, 4);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; 
v_unused_171_ = lean_ctor_get(v___x_157_, 0);
lean_dec(v_unused_171_);
v___x_163_ = v___x_157_;
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_diag_161_);
lean_inc(v_postponed_160_);
lean_inc(v_zetaDeltaFVarIds_159_);
lean_inc(v_cache_158_);
lean_dec(v___x_157_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v_snd_156_);
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_snd_156_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_cache_158_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_zetaDeltaFVarIds_159_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_postponed_160_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_diag_161_);
v___x_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_st_ref_put(v___y_148_, v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v_fst_155_);
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_147_ = stack[0].m_obj;
lean_object* v___y_148_ = stack[1].m_obj;
lean_object* v_res_172_;
v_res_172_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_147_, v___y_148_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object* v_e_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_173_, v___y_174_);
lean_dec(v___y_174_);
return v_res_176_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object* v_e_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_177_, v___y_179_);
return v___x_183_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_177_ = stack[0].m_obj;
lean_object* v___y_178_ = stack[1].m_obj;
lean_object* v___y_179_ = stack[2].m_obj;
lean_object* v___y_180_ = stack[3].m_obj;
lean_object* v___y_181_ = stack[4].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(v_e_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object* v_e_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(v_e_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_191_;
}
}
lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object* v_kind_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; lean_object* v_auxDeclNGen_196_; lean_object* v___x_197_; lean_object* v_env_198_; lean_object* v___x_199_; lean_object* v_fst_200_; lean_object* v_snd_201_; lean_object* v___x_202_; lean_object* v_env_203_; lean_object* v_nextMacroScope_204_; lean_object* v_ngen_205_; lean_object* v_traceState_206_; lean_object* v_cache_207_; lean_object* v_recordedDeps_208_; lean_object* v_messages_209_; lean_object* v_infoState_210_; lean_object* v_snapshotTasks_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_220_; 
v___x_195_ = lean_st_ref_get(v___y_193_);
v_auxDeclNGen_196_ = lean_ctor_get(v___x_195_, 3);
lean_inc_ref(v_auxDeclNGen_196_);
lean_dec(v___x_195_);
v___x_197_ = lean_st_ref_get(v___y_193_);
v_env_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_env_198_);
lean_dec(v___x_197_);
v___x_199_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_198_, v_auxDeclNGen_196_, v_kind_192_);
v_fst_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_fst_200_);
v_snd_201_ = lean_ctor_get(v___x_199_, 1);
lean_inc(v_snd_201_);
lean_dec_ref(v___x_199_);
v___x_202_ = lean_st_ref_take(v___y_193_);
v_env_203_ = lean_ctor_get(v___x_202_, 0);
v_nextMacroScope_204_ = lean_ctor_get(v___x_202_, 1);
v_ngen_205_ = lean_ctor_get(v___x_202_, 2);
v_traceState_206_ = lean_ctor_get(v___x_202_, 4);
v_cache_207_ = lean_ctor_get(v___x_202_, 5);
v_recordedDeps_208_ = lean_ctor_get(v___x_202_, 6);
v_messages_209_ = lean_ctor_get(v___x_202_, 7);
v_infoState_210_ = lean_ctor_get(v___x_202_, 8);
v_snapshotTasks_211_ = lean_ctor_get(v___x_202_, 9);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v___x_202_, 3);
lean_dec(v_unused_221_);
v___x_213_ = v___x_202_;
v_isShared_214_ = v_isSharedCheck_220_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_snapshotTasks_211_);
lean_inc(v_infoState_210_);
lean_inc(v_messages_209_);
lean_inc(v_recordedDeps_208_);
lean_inc(v_cache_207_);
lean_inc(v_traceState_206_);
lean_inc(v_ngen_205_);
lean_inc(v_nextMacroScope_204_);
lean_inc(v_env_203_);
lean_dec(v___x_202_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_220_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 3, v_snd_201_);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_env_203_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_nextMacroScope_204_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_ngen_205_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_snd_201_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_traceState_206_);
lean_ctor_set(v_reuseFailAlloc_219_, 5, v_cache_207_);
lean_ctor_set(v_reuseFailAlloc_219_, 6, v_recordedDeps_208_);
lean_ctor_set(v_reuseFailAlloc_219_, 7, v_messages_209_);
lean_ctor_set(v_reuseFailAlloc_219_, 8, v_infoState_210_);
lean_ctor_set(v_reuseFailAlloc_219_, 9, v_snapshotTasks_211_);
v___x_216_ = v_reuseFailAlloc_219_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_st_ref_put(v___y_193_, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v_fst_200_);
return v___x_218_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_192_ = stack[0].m_obj;
lean_object* v___y_193_ = stack[1].m_obj;
lean_object* v_res_222_;
v_res_222_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_192_, v___y_193_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object* v_kind_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_223_, v___y_224_);
lean_dec(v___y_224_);
return v_res_226_;
}
}
lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object* v_kind_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_227_, v___y_231_);
return v___x_233_;
}
}
LEAN_EXPORT void l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_227_ = stack[0].m_obj;
lean_object* v___y_228_ = stack[1].m_obj;
lean_object* v___y_229_ = stack[2].m_obj;
lean_object* v___y_230_ = stack[3].m_obj;
lean_object* v___y_231_ = stack[4].m_obj;
lean_object* v_res_234_;
v_res_234_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object* v_kind_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_242_, lean_object* v_opt_243_){
_start:
{
lean_object* v_name_244_; lean_object* v_defValue_245_; lean_object* v_map_246_; lean_object* v___x_247_; 
v_name_244_ = lean_ctor_get(v_opt_243_, 0);
v_defValue_245_ = lean_ctor_get(v_opt_243_, 1);
v_map_246_ = lean_ctor_get(v_opts_242_, 0);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_246_, v_name_244_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_inc(v_defValue_245_);
return v_defValue_245_;
}
else
{
lean_object* v_val_248_; 
v_val_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v___x_247_, 1);
if (lean_obj_tag(v_val_248_) == 3)
{
lean_object* v_v_249_; 
v_v_249_ = lean_ctor_get(v_val_248_, 0);
lean_inc(v_v_249_);
lean_dec_ref_known(v_val_248_, 1);
return v_v_249_;
}
else
{
lean_dec(v_val_248_);
lean_inc(v_defValue_245_);
return v_defValue_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_250_, lean_object* v_opt_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_250_, v_opt_251_);
lean_dec_ref(v_opt_251_);
lean_dec_ref(v_opts_250_);
return v_res_252_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v_env_260_; uint8_t v___x_261_; lean_object* v_env_262_; lean_object* v___x_263_; lean_object* v_toCold_264_; lean_object* v_mctx_265_; lean_object* v_lctx_266_; lean_object* v_options_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_259_ = lean_st_ref_get(v___y_257_);
v_env_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_259_);
v___x_261_ = 0;
v_env_262_ = l_Lean_Environment_setRecordingDeps(v_env_260_, v___x_261_);
v___x_263_ = lean_st_ref_get(v___y_255_);
v_toCold_264_ = lean_ctor_get(v___y_256_, 0);
v_mctx_265_ = lean_ctor_get(v___x_263_, 0);
lean_inc_ref(v_mctx_265_);
lean_dec(v___x_263_);
v_lctx_266_ = lean_ctor_get(v___y_254_, 2);
v_options_267_ = lean_ctor_get(v_toCold_264_, 2);
lean_inc_ref(v_options_267_);
lean_inc_ref(v_lctx_266_);
v___x_268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_268_, 0, v_env_262_);
lean_ctor_set(v___x_268_, 1, v_mctx_265_);
lean_ctor_set(v___x_268_, 2, v_lctx_266_);
lean_ctor_set(v___x_268_, 3, v_options_267_);
v___x_269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_msgData_253_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_253_ = stack[0].m_obj;
lean_object* v___y_254_ = stack[1].m_obj;
lean_object* v___y_255_ = stack[2].m_obj;
lean_object* v___y_256_ = stack[3].m_obj;
lean_object* v___y_257_ = stack[4].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msgData_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msgData_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_278_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_ref_285_; lean_object* v___x_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
v_ref_285_ = lean_ctor_get(v___y_282_, 2);
v___x_286_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msg_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_295_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
lean_inc(v_ref_285_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_ref_285_);
lean_ctor_set(v___x_291_, 1, v_a_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 1);
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_279_ = stack[0].m_obj;
lean_object* v___y_280_ = stack[1].m_obj;
lean_object* v___y_281_ = stack[2].m_obj;
lean_object* v___y_282_ = stack[3].m_obj;
lean_object* v___y_283_ = stack[4].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(lean_object* v_o_307_, lean_object* v_k_308_, uint8_t v_v_309_){
_start:
{
lean_object* v_map_310_; uint8_t v_hasTrace_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_325_; 
v_map_310_ = lean_ctor_get(v_o_307_, 0);
v_hasTrace_311_ = lean_ctor_get_uint8(v_o_307_, sizeof(void*)*1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_o_307_);
if (v_isSharedCheck_325_ == 0)
{
v___x_313_ = v_o_307_;
v_isShared_314_ = v_isSharedCheck_325_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_map_310_);
lean_dec(v_o_307_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_325_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_315_, 0, v_v_309_);
lean_inc(v_k_308_);
v___x_316_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_308_, v___x_315_, v_map_310_);
if (v_hasTrace_311_ == 0)
{
lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_320_; 
v___x_317_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__1));
v___x_318_ = l_Lean_Name_isPrefixOf(v___x_317_, v_k_308_);
lean_dec(v_k_308_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_316_);
v___x_320_ = v___x_313_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_316_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*1, v___x_318_);
return v___x_320_;
}
}
else
{
lean_object* v___x_323_; 
lean_dec(v_k_308_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_316_);
v___x_323_ = v___x_313_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_324_, sizeof(void*)*1, v_hasTrace_311_);
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
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_307_ = stack[0].m_obj;
lean_object* v_k_308_ = stack[1].m_obj;
uint8_t v_v_309_ = stack[2].m_num;
lean_object* v_res_326_;
v_res_326_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(v_o_307_, v_k_308_, v_v_309_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___boxed(lean_object* v_o_327_, lean_object* v_k_328_, lean_object* v_v_329_){
_start:
{
uint8_t v_v_boxed_330_; lean_object* v_res_331_; 
v_v_boxed_330_ = lean_unbox(v_v_329_);
v_res_331_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(v_o_327_, v_k_328_, v_v_boxed_330_);
return v_res_331_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_opts_332_, lean_object* v_opt_333_, uint8_t v_val_334_){
_start:
{
lean_object* v_name_335_; lean_object* v___x_336_; 
v_name_335_ = lean_ctor_get(v_opt_333_, 0);
lean_inc(v_name_335_);
lean_dec_ref(v_opt_333_);
v___x_336_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(v_opts_332_, v_name_335_, v_val_334_);
return v___x_336_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_332_ = stack[0].m_obj;
lean_object* v_opt_333_ = stack[1].m_obj;
uint8_t v_val_334_ = stack[2].m_num;
lean_object* v_res_337_;
v_res_337_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v_opts_332_, v_opt_333_, v_val_334_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_opts_338_, lean_object* v_opt_339_, lean_object* v_val_340_){
_start:
{
uint8_t v_val_boxed_341_; lean_object* v_res_342_; 
v_val_boxed_341_ = lean_unbox(v_val_340_);
v_res_342_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v_opts_338_, v_opt_339_, v_val_boxed_341_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_box(0);
v___x_344_ = l_Lean_Elab_abortCommandExceptionId;
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_349_;
v_res_349_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___boxed(lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v_res_351_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
if (lean_obj_tag(v_x_352_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_a_358_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v_x_352_, 1);
v___x_359_ = l_Lean_stringToMessageData(v_a_358_);
v___x_360_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_359_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v___x_360_;
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_361_ = lean_ctor_get(v_x_352_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_x_352_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v_x_352_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v_x_352_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 0);
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_352_ = stack[0].m_obj;
lean_object* v___y_353_ = stack[1].m_obj;
lean_object* v___y_354_ = stack[2].m_obj;
lean_object* v___y_355_ = stack[3].m_obj;
lean_object* v___y_356_ = stack[4].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg___boxed(lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(lean_object* v_constName_377_, uint8_t v_checkMeta_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; lean_object* v_env_385_; uint8_t v___x_386_; 
v___x_384_ = lean_st_ref_get(v___y_382_);
v_env_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_env_385_);
lean_dec(v___x_384_);
lean_inc(v_constName_377_);
v___x_386_ = lean_has_compile_error(v_env_385_, v_constName_377_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_387_ = lean_st_ref_get(v___y_382_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_388_);
lean_dec(v___x_387_);
v___x_389_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_381_);
v___x_390_ = l_Lean_Environment_evalConst___redArg(v_env_388_, v___x_389_, v_constName_377_, v_checkMeta_378_);
lean_dec(v_constName_377_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v_env_388_);
v___x_391_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_390_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_393_; lean_object* v_env_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref_known(v___x_392_, 1);
v___x_393_ = lean_st_ref_get(v___y_382_);
v_env_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc_ref(v_env_394_);
lean_dec(v___x_393_);
v___x_395_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_381_);
v___x_396_ = l_Lean_Environment_evalConst___redArg(v_env_394_, v___x_395_, v_constName_377_, v_checkMeta_378_);
lean_dec(v_constName_377_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_env_394_);
v___x_397_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_396_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_constName_377_);
v_a_398_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_392_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_392_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_377_ = stack[0].m_obj;
uint8_t v_checkMeta_378_ = stack[1].m_num;
lean_object* v___y_379_ = stack[2].m_obj;
lean_object* v___y_380_ = stack[3].m_obj;
lean_object* v___y_381_ = stack[4].m_obj;
lean_object* v___y_382_ = stack[5].m_obj;
lean_object* v_res_406_;
v_res_406_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_377_, v_checkMeta_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg___boxed(lean_object* v_constName_407_, lean_object* v_checkMeta_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
uint8_t v_checkMeta_boxed_414_; lean_object* v_res_415_; 
v_checkMeta_boxed_414_ = lean_unbox(v_checkMeta_408_);
v_res_415_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_407_, v_checkMeta_boxed_414_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_415_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__4));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_box(0);
v___x_429_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_430_ = l_Lean_mkConst(v___x_429_, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_437_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
lean_ctor_set(v___x_437_, 3, v___x_436_);
lean_ctor_set(v___x_437_, 4, v___x_436_);
lean_ctor_set(v___x_437_, 5, v___x_436_);
return v___x_437_;
}
}
lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v_tacticName_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v_a_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___y_449_; lean_object* v___y_450_; uint8_t v___y_451_; lean_object* v___x_460_; lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_787_; 
v___x_460_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_439_, v___y_446_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_787_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_787_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_787_;
goto v_resetjp_462_;
}
v___jp_448_:
{
if (v___y_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec_ref(v___y_449_);
v___x_452_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_453_ = l_Lean_MessageData_ofName(v_tacticName_438_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_Exception_toMessageData(v___y_450_);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_458_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v___y_445_);
return v___x_459_;
}
else
{
lean_dec_ref(v___y_450_);
lean_dec_ref(v___y_445_);
lean_dec(v_tacticName_438_);
return v___y_449_;
}
}
v_resetjp_462_:
{
lean_object* v___y_466_; lean_object* v___y_481_; lean_object* v___y_482_; uint8_t v___y_483_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_492_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_461_, 2);
v___x_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_493_, 0, v_a_461_);
lean_ctor_set(v___x_493_, 1, v___x_440_);
lean_ctor_set(v___x_493_, 2, v___x_492_);
v___x_494_ = lean_box(1);
v___x_495_ = 1;
v___x_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_496_, 0, v_a_461_);
lean_ctor_set(v___x_496_, 1, v___x_441_);
v___x_497_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_497_, 0, v___x_493_);
lean_ctor_set(v___x_497_, 1, v_a_442_);
lean_ctor_set(v___x_497_, 2, v___x_494_);
lean_ctor_set(v___x_497_, 3, v___x_496_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*4, v___x_495_);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 1);
lean_ctor_set(v___x_463_, 0, v___x_497_);
v___x_499_ = v___x_463_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_786_;
goto v_reusejp_498_;
}
v___jp_465_:
{
if (lean_obj_tag(v___y_466_) == 0)
{
uint8_t v___x_467_; lean_object* v___x_468_; 
lean_dec_ref_known(v___y_466_, 1);
v___x_467_ = 1;
v___x_468_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_a_461_, v___x_467_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec_ref(v___y_445_);
lean_dec(v_tacticName_438_);
return v___x_468_;
}
else
{
lean_object* v_a_469_; uint8_t v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
v___x_470_ = l_Lean_Exception_isInterrupt(v_a_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
lean_inc(v_a_469_);
v___x_471_ = l_Lean_Exception_isRuntime(v_a_469_);
v___y_449_ = v___x_468_;
v___y_450_ = v_a_469_;
v___y_451_ = v___x_471_;
goto v___jp_448_;
}
else
{
v___y_449_ = v___x_468_;
v___y_450_ = v_a_469_;
v___y_451_ = v___x_470_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_a_461_);
lean_dec_ref(v___y_445_);
lean_dec(v_tacticName_438_);
v_a_472_ = lean_ctor_get(v___y_466_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___y_466_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___y_466_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___y_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
v___jp_480_:
{
if (v___y_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v___y_482_);
v___x_484_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_438_);
v___x_485_ = l_Lean_MessageData_ofName(v_tacticName_438_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_Exception_toMessageData(v___y_481_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_490_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
v___y_466_ = v___x_491_;
goto v___jp_465_;
}
else
{
lean_dec_ref(v___y_481_);
v___y_466_ = v___y_482_;
goto v___jp_465_;
}
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v_env_501_; lean_object* v_nextMacroScope_502_; lean_object* v_ngen_503_; lean_object* v_auxDeclNGen_504_; lean_object* v_traceState_505_; lean_object* v_recordedDeps_506_; lean_object* v_messages_507_; lean_object* v_infoState_508_; lean_object* v_snapshotTasks_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_784_; 
v___x_500_ = lean_st_ref_take(v___y_446_);
v_env_501_ = lean_ctor_get(v___x_500_, 0);
v_nextMacroScope_502_ = lean_ctor_get(v___x_500_, 1);
v_ngen_503_ = lean_ctor_get(v___x_500_, 2);
v_auxDeclNGen_504_ = lean_ctor_get(v___x_500_, 3);
v_traceState_505_ = lean_ctor_get(v___x_500_, 4);
v_recordedDeps_506_ = lean_ctor_get(v___x_500_, 6);
v_messages_507_ = lean_ctor_get(v___x_500_, 7);
v_infoState_508_ = lean_ctor_get(v___x_500_, 8);
v_snapshotTasks_509_ = lean_ctor_get(v___x_500_, 9);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v___x_500_, 5);
lean_dec(v_unused_785_);
v___x_511_ = v___x_500_;
v_isShared_512_ = v_isSharedCheck_784_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snapshotTasks_509_);
lean_inc(v_infoState_508_);
lean_inc(v_messages_507_);
lean_inc(v_recordedDeps_506_);
lean_inc(v_traceState_505_);
lean_inc(v_auxDeclNGen_504_);
lean_inc(v_ngen_503_);
lean_inc(v_nextMacroScope_502_);
lean_inc(v_env_501_);
lean_dec(v___x_500_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_784_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_inc(v_a_461_);
v___x_513_ = l_Lean_markMeta(v_env_501_, v_a_461_);
v___x_514_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 5, v___x_514_);
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_nextMacroScope_502_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_ngen_503_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_auxDeclNGen_504_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_traceState_505_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_783_, 6, v_recordedDeps_506_);
lean_ctor_set(v_reuseFailAlloc_783_, 7, v_messages_507_);
lean_ctor_set(v_reuseFailAlloc_783_, 8, v_infoState_508_);
lean_ctor_set(v_reuseFailAlloc_783_, 9, v_snapshotTasks_509_);
v___x_516_ = v_reuseFailAlloc_783_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_mctx_519_; lean_object* v_zetaDeltaFVarIds_520_; lean_object* v_postponed_521_; lean_object* v_diag_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_781_; 
v___x_517_ = lean_st_ref_put(v___y_446_, v___x_516_);
v___x_518_ = lean_st_ref_take(v___y_444_);
v_mctx_519_ = lean_ctor_get(v___x_518_, 0);
v_zetaDeltaFVarIds_520_ = lean_ctor_get(v___x_518_, 2);
v_postponed_521_ = lean_ctor_get(v___x_518_, 3);
v_diag_522_ = lean_ctor_get(v___x_518_, 4);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_518_, 1);
lean_dec(v_unused_782_);
v___x_524_ = v___x_518_;
v_isShared_525_ = v_isSharedCheck_781_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_diag_522_);
lean_inc(v_postponed_521_);
lean_inc(v_zetaDeltaFVarIds_520_);
lean_inc(v_mctx_519_);
lean_dec(v___x_518_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_781_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_mctx_519_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_zetaDeltaFVarIds_520_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_postponed_521_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_diag_522_);
v___x_528_ = v_reuseFailAlloc_780_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v_toCold_530_; lean_object* v_currRecDepth_531_; lean_object* v_ref_532_; uint8_t v_suppressElabErrors_533_; uint8_t v_isRecordingDeps_534_; lean_object* v_fileName_535_; lean_object* v_fileMap_536_; lean_object* v_options_537_; lean_object* v_currNamespace_538_; lean_object* v_openDecls_539_; lean_object* v_initHeartbeats_540_; lean_object* v_maxHeartbeats_541_; lean_object* v_quotContext_542_; lean_object* v_currMacroScope_543_; lean_object* v_cancelTk_x3f_544_; lean_object* v_inheritedTraceOptions_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_778_; 
v___x_529_ = lean_st_ref_put(v___y_444_, v___x_528_);
v_toCold_530_ = lean_ctor_get(v___y_445_, 0);
lean_inc_ref(v_toCold_530_);
v_currRecDepth_531_ = lean_ctor_get(v___y_445_, 1);
v_ref_532_ = lean_ctor_get(v___y_445_, 2);
v_suppressElabErrors_533_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*3 + 2);
v_isRecordingDeps_534_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*3 + 3);
v_fileName_535_ = lean_ctor_get(v_toCold_530_, 0);
v_fileMap_536_ = lean_ctor_get(v_toCold_530_, 1);
v_options_537_ = lean_ctor_get(v_toCold_530_, 2);
v_currNamespace_538_ = lean_ctor_get(v_toCold_530_, 4);
v_openDecls_539_ = lean_ctor_get(v_toCold_530_, 5);
v_initHeartbeats_540_ = lean_ctor_get(v_toCold_530_, 6);
v_maxHeartbeats_541_ = lean_ctor_get(v_toCold_530_, 7);
v_quotContext_542_ = lean_ctor_get(v_toCold_530_, 8);
v_currMacroScope_543_ = lean_ctor_get(v_toCold_530_, 9);
v_cancelTk_x3f_544_ = lean_ctor_get(v_toCold_530_, 10);
v_inheritedTraceOptions_545_ = lean_ctor_get(v_toCold_530_, 11);
v_isSharedCheck_778_ = !lean_is_exclusive(v_toCold_530_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_toCold_530_, 3);
lean_dec(v_unused_779_);
v___x_547_ = v_toCold_530_;
v_isShared_548_ = v_isSharedCheck_778_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_inheritedTraceOptions_545_);
lean_inc(v_cancelTk_x3f_544_);
lean_inc(v_currMacroScope_543_);
lean_inc(v_quotContext_542_);
lean_inc(v_maxHeartbeats_541_);
lean_inc(v_initHeartbeats_540_);
lean_inc(v_openDecls_539_);
lean_inc(v_currNamespace_538_);
lean_inc(v_options_537_);
lean_inc(v_fileMap_536_);
lean_inc(v_fileName_535_);
lean_dec(v_toCold_530_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_778_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint8_t v___x_549_; uint8_t v___x_550_; lean_object* v___y_552_; uint16_t v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; uint8_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; uint16_t v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; uint16_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; uint16_t v___y_675_; uint8_t v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint16_t v___y_715_; lean_object* v___y_716_; lean_object* v_fileName_717_; lean_object* v_fileMap_718_; lean_object* v_currNamespace_719_; lean_object* v_openDecls_720_; lean_object* v_initHeartbeats_721_; lean_object* v_maxHeartbeats_722_; lean_object* v_quotContext_723_; lean_object* v_currMacroScope_724_; lean_object* v_cancelTk_x3f_725_; lean_object* v_inheritedTraceOptions_726_; lean_object* v_currRecDepth_727_; lean_object* v_ref_728_; uint8_t v_suppressElabErrors_729_; uint8_t v_isRecordingDeps_730_; lean_object* v___y_731_; uint16_t v___y_742_; lean_object* v___y_743_; uint8_t v___y_744_; lean_object* v___y_766_; 
v___x_549_ = 1;
v___x_550_ = 0;
if (v_isRecordingDeps_534_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = l_Lean_Elab_async;
v___x_776_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v_options_537_, v___x_775_, v_isRecordingDeps_534_);
v___y_766_ = v___x_776_;
goto v___jp_765_;
}
else
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_537_);
v___y_766_ = v___x_777_;
goto v___jp_765_;
}
v___jp_551_:
{
lean_object* v_toCold_557_; lean_object* v_currRecDepth_558_; lean_object* v_ref_559_; uint8_t v_suppressElabErrors_560_; uint8_t v_isRecordingDeps_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_592_; 
v_toCold_557_ = lean_ctor_get(v___y_555_, 0);
v_currRecDepth_558_ = lean_ctor_get(v___y_555_, 1);
v_ref_559_ = lean_ctor_get(v___y_555_, 2);
v_suppressElabErrors_560_ = lean_ctor_get_uint8(v___y_555_, sizeof(void*)*3 + 2);
v_isRecordingDeps_561_ = lean_ctor_get_uint8(v___y_555_, sizeof(void*)*3 + 3);
v_isSharedCheck_592_ = !lean_is_exclusive(v___y_555_);
if (v_isSharedCheck_592_ == 0)
{
v___x_563_ = v___y_555_;
v_isShared_564_ = v_isSharedCheck_592_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_ref_559_);
lean_inc(v_currRecDepth_558_);
lean_inc(v_toCold_557_);
lean_dec(v___y_555_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_592_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_fileName_565_; lean_object* v_fileMap_566_; lean_object* v_currNamespace_567_; lean_object* v_openDecls_568_; lean_object* v_initHeartbeats_569_; lean_object* v_maxHeartbeats_570_; lean_object* v_quotContext_571_; lean_object* v_currMacroScope_572_; lean_object* v_cancelTk_x3f_573_; lean_object* v_inheritedTraceOptions_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_589_; 
v_fileName_565_ = lean_ctor_get(v_toCold_557_, 0);
v_fileMap_566_ = lean_ctor_get(v_toCold_557_, 1);
v_currNamespace_567_ = lean_ctor_get(v_toCold_557_, 4);
v_openDecls_568_ = lean_ctor_get(v_toCold_557_, 5);
v_initHeartbeats_569_ = lean_ctor_get(v_toCold_557_, 6);
v_maxHeartbeats_570_ = lean_ctor_get(v_toCold_557_, 7);
v_quotContext_571_ = lean_ctor_get(v_toCold_557_, 8);
v_currMacroScope_572_ = lean_ctor_get(v_toCold_557_, 9);
v_cancelTk_x3f_573_ = lean_ctor_get(v_toCold_557_, 10);
v_inheritedTraceOptions_574_ = lean_ctor_get(v_toCold_557_, 11);
v_isSharedCheck_589_ = !lean_is_exclusive(v_toCold_557_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_590_ = lean_ctor_get(v_toCold_557_, 3);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_toCold_557_, 2);
lean_dec(v_unused_591_);
v___x_576_ = v_toCold_557_;
v_isShared_577_ = v_isSharedCheck_589_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_inheritedTraceOptions_574_);
lean_inc(v_cancelTk_x3f_573_);
lean_inc(v_currMacroScope_572_);
lean_inc(v_quotContext_571_);
lean_inc(v_maxHeartbeats_570_);
lean_inc(v_initHeartbeats_569_);
lean_inc(v_openDecls_568_);
lean_inc(v_currNamespace_567_);
lean_inc(v_fileMap_566_);
lean_inc(v_fileName_565_);
lean_dec(v_toCold_557_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_589_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_554_, v___y_552_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v___x_578_);
lean_ctor_set(v___x_576_, 2, v___y_554_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fileName_565_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_fileMap_566_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v___y_554_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_currNamespace_567_);
lean_ctor_set(v_reuseFailAlloc_588_, 5, v_openDecls_568_);
lean_ctor_set(v_reuseFailAlloc_588_, 6, v_initHeartbeats_569_);
lean_ctor_set(v_reuseFailAlloc_588_, 7, v_maxHeartbeats_570_);
lean_ctor_set(v_reuseFailAlloc_588_, 8, v_quotContext_571_);
lean_ctor_set(v_reuseFailAlloc_588_, 9, v_currMacroScope_572_);
lean_ctor_set(v_reuseFailAlloc_588_, 10, v_cancelTk_x3f_573_);
lean_ctor_set(v_reuseFailAlloc_588_, 11, v_inheritedTraceOptions_574_);
v___x_580_ = v_reuseFailAlloc_588_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_580_);
v___x_582_ = v___x_563_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_currRecDepth_558_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_ref_559_);
lean_ctor_set_uint8(v_reuseFailAlloc_587_, sizeof(void*)*3 + 2, v_suppressElabErrors_560_);
lean_ctor_set_uint8(v_reuseFailAlloc_587_, sizeof(void*)*3 + 3, v_isRecordingDeps_561_);
v___x_582_ = v_reuseFailAlloc_587_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; 
lean_ctor_set_uint16(v___x_582_, sizeof(void*)*3, v___y_553_);
v___x_583_ = l_Lean_addAndCompile(v___x_499_, v___x_549_, v___x_550_, v___x_582_, v___y_556_);
lean_dec_ref(v___x_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
v___y_466_ = v___x_583_;
goto v___jp_465_;
}
else
{
lean_object* v_a_584_; uint8_t v___x_585_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
v___x_585_ = l_Lean_Exception_isInterrupt(v_a_584_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
lean_inc(v_a_584_);
v___x_586_ = l_Lean_Exception_isRuntime(v_a_584_);
v___y_481_ = v_a_584_;
v___y_482_ = v___x_583_;
v___y_483_ = v___x_586_;
goto v___jp_480_;
}
else
{
v___y_481_ = v_a_584_;
v___y_482_ = v___x_583_;
v___y_483_ = v___x_585_;
goto v___jp_480_;
}
}
}
}
}
}
}
v___jp_593_:
{
lean_object* v___x_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_traceState_605_; lean_object* v_recordedDeps_606_; lean_object* v_messages_607_; lean_object* v_infoState_608_; lean_object* v_snapshotTasks_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_618_; 
v___x_600_ = lean_st_ref_take(v___y_595_);
v_env_601_ = lean_ctor_get(v___x_600_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_600_, 1);
v_ngen_603_ = lean_ctor_get(v___x_600_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_600_, 3);
v_traceState_605_ = lean_ctor_get(v___x_600_, 4);
v_recordedDeps_606_ = lean_ctor_get(v___x_600_, 6);
v_messages_607_ = lean_ctor_get(v___x_600_, 7);
v_infoState_608_ = lean_ctor_get(v___x_600_, 8);
v_snapshotTasks_609_ = lean_ctor_get(v___x_600_, 9);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v___x_600_, 5);
lean_dec(v_unused_619_);
v___x_611_ = v___x_600_;
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snapshotTasks_609_);
lean_inc(v_infoState_608_);
lean_inc(v_messages_607_);
lean_inc(v_recordedDeps_606_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_600_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = l_Lean_Kernel_enableDiag(v_env_601_, v___y_594_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 5, v___x_514_);
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_traceState_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_recordedDeps_606_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_messages_607_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v_infoState_608_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_snapshotTasks_609_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = lean_st_ref_put(v___y_595_, v___x_615_);
v___y_552_ = v___y_596_;
v___y_553_ = v___y_597_;
v___y_554_ = v___y_599_;
v___y_555_ = v___y_598_;
v___y_556_ = v___y_595_;
goto v___jp_551_;
}
}
}
v___jp_620_:
{
uint16_t v___x_625_; lean_object* v___x_626_; lean_object* v_env_627_; uint8_t v___x_628_; uint16_t v___x_629_; uint16_t v___x_630_; uint16_t v___x_631_; uint8_t v___x_632_; 
v___x_625_ = l_Lean_OptionFlags_ofOptions(v___y_624_);
v___x_626_ = lean_st_ref_get(v___y_621_);
v_env_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc_ref(v_env_627_);
lean_dec(v___x_626_);
v___x_628_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_627_);
lean_dec_ref(v_env_627_);
v___x_629_ = 512;
v___x_630_ = lean_uint16_land(v___x_625_, v___x_629_);
v___x_631_ = 0;
v___x_632_ = lean_uint16_dec_eq(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
if (v___x_628_ == 0)
{
v___y_594_ = v___x_549_;
v___y_595_ = v___y_621_;
v___y_596_ = v___y_622_;
v___y_597_ = v___x_625_;
v___y_598_ = v___y_623_;
v___y_599_ = v___y_624_;
goto v___jp_593_;
}
else
{
v___y_552_ = v___y_622_;
v___y_553_ = v___x_625_;
v___y_554_ = v___y_624_;
v___y_555_ = v___y_623_;
v___y_556_ = v___y_621_;
goto v___jp_551_;
}
}
else
{
if (v___x_628_ == 0)
{
v___y_552_ = v___y_622_;
v___y_553_ = v___x_625_;
v___y_554_ = v___y_624_;
v___y_555_ = v___y_623_;
v___y_556_ = v___y_621_;
goto v___jp_551_;
}
else
{
v___y_594_ = v___x_550_;
v___y_595_ = v___y_621_;
v___y_596_ = v___y_622_;
v___y_597_ = v___x_625_;
v___y_598_ = v___y_623_;
v___y_599_ = v___y_624_;
goto v___jp_593_;
}
}
}
v___jp_633_:
{
lean_object* v_toCold_639_; lean_object* v_currRecDepth_640_; lean_object* v_ref_641_; uint8_t v_suppressElabErrors_642_; uint8_t v_isRecordingDeps_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_673_; 
v_toCold_639_ = lean_ctor_get(v___y_637_, 0);
v_currRecDepth_640_ = lean_ctor_get(v___y_637_, 1);
v_ref_641_ = lean_ctor_get(v___y_637_, 2);
v_suppressElabErrors_642_ = lean_ctor_get_uint8(v___y_637_, sizeof(void*)*3 + 2);
v_isRecordingDeps_643_ = lean_ctor_get_uint8(v___y_637_, sizeof(void*)*3 + 3);
v_isSharedCheck_673_ = !lean_is_exclusive(v___y_637_);
if (v_isSharedCheck_673_ == 0)
{
v___x_645_ = v___y_637_;
v_isShared_646_ = v_isSharedCheck_673_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_ref_641_);
lean_inc(v_currRecDepth_640_);
lean_inc(v_toCold_639_);
lean_dec(v___y_637_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_673_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_fileName_647_; lean_object* v_fileMap_648_; lean_object* v_currNamespace_649_; lean_object* v_openDecls_650_; lean_object* v_initHeartbeats_651_; lean_object* v_maxHeartbeats_652_; lean_object* v_quotContext_653_; lean_object* v_currMacroScope_654_; lean_object* v_cancelTk_x3f_655_; lean_object* v_inheritedTraceOptions_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_670_; 
v_fileName_647_ = lean_ctor_get(v_toCold_639_, 0);
v_fileMap_648_ = lean_ctor_get(v_toCold_639_, 1);
v_currNamespace_649_ = lean_ctor_get(v_toCold_639_, 4);
v_openDecls_650_ = lean_ctor_get(v_toCold_639_, 5);
v_initHeartbeats_651_ = lean_ctor_get(v_toCold_639_, 6);
v_maxHeartbeats_652_ = lean_ctor_get(v_toCold_639_, 7);
v_quotContext_653_ = lean_ctor_get(v_toCold_639_, 8);
v_currMacroScope_654_ = lean_ctor_get(v_toCold_639_, 9);
v_cancelTk_x3f_655_ = lean_ctor_get(v_toCold_639_, 10);
v_inheritedTraceOptions_656_ = lean_ctor_get(v_toCold_639_, 11);
v_isSharedCheck_670_ = !lean_is_exclusive(v_toCold_639_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_671_ = lean_ctor_get(v_toCold_639_, 3);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_toCold_639_, 2);
lean_dec(v_unused_672_);
v___x_658_ = v_toCold_639_;
v_isShared_659_ = v_isSharedCheck_670_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_inheritedTraceOptions_656_);
lean_inc(v_cancelTk_x3f_655_);
lean_inc(v_currMacroScope_654_);
lean_inc(v_quotContext_653_);
lean_inc(v_maxHeartbeats_652_);
lean_inc(v_initHeartbeats_651_);
lean_inc(v_openDecls_650_);
lean_inc(v_currNamespace_649_);
lean_inc(v_fileMap_648_);
lean_inc(v_fileName_647_);
lean_dec(v_toCold_639_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_670_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_636_, v___y_635_);
lean_inc_ref(v___y_636_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v___x_660_);
lean_ctor_set(v___x_658_, 2, v___y_636_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fileName_647_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_fileMap_648_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v___y_636_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v_currNamespace_649_);
lean_ctor_set(v_reuseFailAlloc_669_, 5, v_openDecls_650_);
lean_ctor_set(v_reuseFailAlloc_669_, 6, v_initHeartbeats_651_);
lean_ctor_set(v_reuseFailAlloc_669_, 7, v_maxHeartbeats_652_);
lean_ctor_set(v_reuseFailAlloc_669_, 8, v_quotContext_653_);
lean_ctor_set(v_reuseFailAlloc_669_, 9, v_currMacroScope_654_);
lean_ctor_set(v_reuseFailAlloc_669_, 10, v_cancelTk_x3f_655_);
lean_ctor_set(v_reuseFailAlloc_669_, 11, v_inheritedTraceOptions_656_);
v___x_662_ = v_reuseFailAlloc_669_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_662_);
v___x_664_ = v___x_645_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_currRecDepth_640_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_ref_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 2, v_suppressElabErrors_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 3, v_isRecordingDeps_643_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_ctor_set_uint16(v___x_664_, sizeof(void*)*3, v___y_634_);
if (v_isRecordingDeps_643_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_666_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_636_, v___x_665_, v___x_549_);
v___y_621_ = v___y_638_;
v___y_622_ = v___y_635_;
v___y_623_ = v___x_664_;
v___y_624_ = v___x_666_;
goto v___jp_620_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_636_);
v___y_621_ = v___y_638_;
v___y_622_ = v___y_635_;
v___y_623_ = v___x_664_;
v___y_624_ = v___x_667_;
goto v___jp_620_;
}
}
}
}
}
}
v___jp_674_:
{
lean_object* v___x_681_; lean_object* v_env_682_; lean_object* v_nextMacroScope_683_; lean_object* v_ngen_684_; lean_object* v_auxDeclNGen_685_; lean_object* v_traceState_686_; lean_object* v_recordedDeps_687_; lean_object* v_messages_688_; lean_object* v_infoState_689_; lean_object* v_snapshotTasks_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_699_; 
v___x_681_ = lean_st_ref_take(v___y_677_);
v_env_682_ = lean_ctor_get(v___x_681_, 0);
v_nextMacroScope_683_ = lean_ctor_get(v___x_681_, 1);
v_ngen_684_ = lean_ctor_get(v___x_681_, 2);
v_auxDeclNGen_685_ = lean_ctor_get(v___x_681_, 3);
v_traceState_686_ = lean_ctor_get(v___x_681_, 4);
v_recordedDeps_687_ = lean_ctor_get(v___x_681_, 6);
v_messages_688_ = lean_ctor_get(v___x_681_, 7);
v_infoState_689_ = lean_ctor_get(v___x_681_, 8);
v_snapshotTasks_690_ = lean_ctor_get(v___x_681_, 9);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_681_, 5);
lean_dec(v_unused_700_);
v___x_692_ = v___x_681_;
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snapshotTasks_690_);
lean_inc(v_infoState_689_);
lean_inc(v_messages_688_);
lean_inc(v_recordedDeps_687_);
lean_inc(v_traceState_686_);
lean_inc(v_auxDeclNGen_685_);
lean_inc(v_ngen_684_);
lean_inc(v_nextMacroScope_683_);
lean_inc(v_env_682_);
lean_dec(v___x_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_Kernel_enableDiag(v_env_682_, v___y_676_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 5, v___x_514_);
lean_ctor_set(v___x_692_, 0, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_nextMacroScope_683_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_ngen_684_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_auxDeclNGen_685_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_traceState_686_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_recordedDeps_687_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_messages_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_infoState_689_);
lean_ctor_set(v_reuseFailAlloc_698_, 9, v_snapshotTasks_690_);
v___x_696_ = v_reuseFailAlloc_698_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; 
v___x_697_ = lean_st_ref_put(v___y_677_, v___x_696_);
v___y_634_ = v___y_675_;
v___y_635_ = v___y_678_;
v___y_636_ = v___y_680_;
v___y_637_ = v___y_679_;
v___y_638_ = v___y_677_;
goto v___jp_633_;
}
}
}
v___jp_701_:
{
uint16_t v___x_706_; lean_object* v___x_707_; lean_object* v_env_708_; uint8_t v___x_709_; uint16_t v___x_710_; uint16_t v___x_711_; uint16_t v___x_712_; uint8_t v___x_713_; 
v___x_706_ = l_Lean_OptionFlags_ofOptions(v___y_705_);
v___x_707_ = lean_st_ref_get(v___y_702_);
v_env_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_708_);
lean_dec(v___x_707_);
v___x_709_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_708_);
lean_dec_ref(v_env_708_);
v___x_710_ = 512;
v___x_711_ = lean_uint16_land(v___x_706_, v___x_710_);
v___x_712_ = 0;
v___x_713_ = lean_uint16_dec_eq(v___x_711_, v___x_712_);
if (v___x_713_ == 0)
{
if (v___x_709_ == 0)
{
v___y_675_ = v___x_706_;
v___y_676_ = v___x_549_;
v___y_677_ = v___y_702_;
v___y_678_ = v___y_703_;
v___y_679_ = v___y_704_;
v___y_680_ = v___y_705_;
goto v___jp_674_;
}
else
{
v___y_634_ = v___x_706_;
v___y_635_ = v___y_703_;
v___y_636_ = v___y_705_;
v___y_637_ = v___y_704_;
v___y_638_ = v___y_702_;
goto v___jp_633_;
}
}
else
{
if (v___x_709_ == 0)
{
v___y_634_ = v___x_706_;
v___y_635_ = v___y_703_;
v___y_636_ = v___y_705_;
v___y_637_ = v___y_704_;
v___y_638_ = v___y_702_;
goto v___jp_633_;
}
else
{
v___y_675_ = v___x_706_;
v___y_676_ = v___x_550_;
v___y_677_ = v___y_702_;
v___y_678_ = v___y_703_;
v___y_679_ = v___y_704_;
v___y_680_ = v___y_705_;
goto v___jp_674_;
}
}
}
v___jp_714_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_732_ = l_Lean_maxRecDepth;
v___x_733_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_716_, v___x_732_);
lean_inc_ref(v___y_716_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 11, v_inheritedTraceOptions_726_);
lean_ctor_set(v___x_547_, 10, v_cancelTk_x3f_725_);
lean_ctor_set(v___x_547_, 9, v_currMacroScope_724_);
lean_ctor_set(v___x_547_, 8, v_quotContext_723_);
lean_ctor_set(v___x_547_, 7, v_maxHeartbeats_722_);
lean_ctor_set(v___x_547_, 6, v_initHeartbeats_721_);
lean_ctor_set(v___x_547_, 5, v_openDecls_720_);
lean_ctor_set(v___x_547_, 4, v_currNamespace_719_);
lean_ctor_set(v___x_547_, 3, v___x_733_);
lean_ctor_set(v___x_547_, 2, v___y_716_);
lean_ctor_set(v___x_547_, 1, v_fileMap_718_);
lean_ctor_set(v___x_547_, 0, v_fileName_717_);
v___x_735_ = v___x_547_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_fileName_717_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_fileMap_718_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v___y_716_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_currNamespace_719_);
lean_ctor_set(v_reuseFailAlloc_740_, 5, v_openDecls_720_);
lean_ctor_set(v_reuseFailAlloc_740_, 6, v_initHeartbeats_721_);
lean_ctor_set(v_reuseFailAlloc_740_, 7, v_maxHeartbeats_722_);
lean_ctor_set(v_reuseFailAlloc_740_, 8, v_quotContext_723_);
lean_ctor_set(v_reuseFailAlloc_740_, 9, v_currMacroScope_724_);
lean_ctor_set(v_reuseFailAlloc_740_, 10, v_cancelTk_x3f_725_);
lean_ctor_set(v_reuseFailAlloc_740_, 11, v_inheritedTraceOptions_726_);
v___x_735_ = v_reuseFailAlloc_740_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_currRecDepth_727_);
lean_ctor_set(v___x_736_, 2, v_ref_728_);
lean_ctor_set_uint16(v___x_736_, sizeof(void*)*3, v___y_715_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*3 + 2, v_suppressElabErrors_729_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*3 + 3, v_isRecordingDeps_730_);
if (v_isRecordingDeps_730_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_738_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_716_, v___x_737_, v_isRecordingDeps_730_);
v___y_702_ = v___y_731_;
v___y_703_ = v___x_732_;
v___y_704_ = v___x_736_;
v___y_705_ = v___x_738_;
goto v___jp_701_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_716_);
v___y_702_ = v___y_731_;
v___y_703_ = v___x_732_;
v___y_704_ = v___x_736_;
v___y_705_ = v___x_739_;
goto v___jp_701_;
}
}
}
v___jp_741_:
{
lean_object* v___x_745_; lean_object* v_env_746_; lean_object* v_nextMacroScope_747_; lean_object* v_ngen_748_; lean_object* v_auxDeclNGen_749_; lean_object* v_traceState_750_; lean_object* v_recordedDeps_751_; lean_object* v_messages_752_; lean_object* v_infoState_753_; lean_object* v_snapshotTasks_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_763_; 
v___x_745_ = lean_st_ref_take(v___y_446_);
v_env_746_ = lean_ctor_get(v___x_745_, 0);
v_nextMacroScope_747_ = lean_ctor_get(v___x_745_, 1);
v_ngen_748_ = lean_ctor_get(v___x_745_, 2);
v_auxDeclNGen_749_ = lean_ctor_get(v___x_745_, 3);
v_traceState_750_ = lean_ctor_get(v___x_745_, 4);
v_recordedDeps_751_ = lean_ctor_get(v___x_745_, 6);
v_messages_752_ = lean_ctor_get(v___x_745_, 7);
v_infoState_753_ = lean_ctor_get(v___x_745_, 8);
v_snapshotTasks_754_ = lean_ctor_get(v___x_745_, 9);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_745_, 5);
lean_dec(v_unused_764_);
v___x_756_ = v___x_745_;
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_snapshotTasks_754_);
lean_inc(v_infoState_753_);
lean_inc(v_messages_752_);
lean_inc(v_recordedDeps_751_);
lean_inc(v_traceState_750_);
lean_inc(v_auxDeclNGen_749_);
lean_inc(v_ngen_748_);
lean_inc(v_nextMacroScope_747_);
lean_inc(v_env_746_);
lean_dec(v___x_745_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l_Lean_Kernel_enableDiag(v_env_746_, v___y_744_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 5, v___x_514_);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_nextMacroScope_747_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_ngen_748_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_auxDeclNGen_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_traceState_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_762_, 6, v_recordedDeps_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 7, v_messages_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 8, v_infoState_753_);
lean_ctor_set(v_reuseFailAlloc_762_, 9, v_snapshotTasks_754_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_st_ref_put(v___y_446_, v___x_760_);
lean_inc(v_ref_532_);
lean_inc(v_currRecDepth_531_);
v___y_715_ = v___y_742_;
v___y_716_ = v___y_743_;
v_fileName_717_ = v_fileName_535_;
v_fileMap_718_ = v_fileMap_536_;
v_currNamespace_719_ = v_currNamespace_538_;
v_openDecls_720_ = v_openDecls_539_;
v_initHeartbeats_721_ = v_initHeartbeats_540_;
v_maxHeartbeats_722_ = v_maxHeartbeats_541_;
v_quotContext_723_ = v_quotContext_542_;
v_currMacroScope_724_ = v_currMacroScope_543_;
v_cancelTk_x3f_725_ = v_cancelTk_x3f_544_;
v_inheritedTraceOptions_726_ = v_inheritedTraceOptions_545_;
v_currRecDepth_727_ = v_currRecDepth_531_;
v_ref_728_ = v_ref_532_;
v_suppressElabErrors_729_ = v_suppressElabErrors_533_;
v_isRecordingDeps_730_ = v_isRecordingDeps_534_;
v___y_731_ = v___y_446_;
goto v___jp_714_;
}
}
}
v___jp_765_:
{
uint16_t v___x_767_; lean_object* v___x_768_; lean_object* v_env_769_; uint8_t v___x_770_; uint16_t v___x_771_; uint16_t v___x_772_; uint16_t v___x_773_; uint8_t v___x_774_; 
v___x_767_ = l_Lean_OptionFlags_ofOptions(v___y_766_);
v___x_768_ = lean_st_ref_get(v___y_446_);
v_env_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc_ref(v_env_769_);
lean_dec(v___x_768_);
v___x_770_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_769_);
lean_dec_ref(v_env_769_);
v___x_771_ = 512;
v___x_772_ = lean_uint16_land(v___x_767_, v___x_771_);
v___x_773_ = 0;
v___x_774_ = lean_uint16_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
if (v___x_770_ == 0)
{
v___y_742_ = v___x_767_;
v___y_743_ = v___y_766_;
v___y_744_ = v___x_549_;
goto v___jp_741_;
}
else
{
lean_inc(v_ref_532_);
lean_inc(v_currRecDepth_531_);
v___y_715_ = v___x_767_;
v___y_716_ = v___y_766_;
v_fileName_717_ = v_fileName_535_;
v_fileMap_718_ = v_fileMap_536_;
v_currNamespace_719_ = v_currNamespace_538_;
v_openDecls_720_ = v_openDecls_539_;
v_initHeartbeats_721_ = v_initHeartbeats_540_;
v_maxHeartbeats_722_ = v_maxHeartbeats_541_;
v_quotContext_723_ = v_quotContext_542_;
v_currMacroScope_724_ = v_currMacroScope_543_;
v_cancelTk_x3f_725_ = v_cancelTk_x3f_544_;
v_inheritedTraceOptions_726_ = v_inheritedTraceOptions_545_;
v_currRecDepth_727_ = v_currRecDepth_531_;
v_ref_728_ = v_ref_532_;
v_suppressElabErrors_729_ = v_suppressElabErrors_533_;
v_isRecordingDeps_730_ = v_isRecordingDeps_534_;
v___y_731_ = v___y_446_;
goto v___jp_714_;
}
}
else
{
if (v___x_770_ == 0)
{
lean_inc(v_ref_532_);
lean_inc(v_currRecDepth_531_);
v___y_715_ = v___x_767_;
v___y_716_ = v___y_766_;
v_fileName_717_ = v_fileName_535_;
v_fileMap_718_ = v_fileMap_536_;
v_currNamespace_719_ = v_currNamespace_538_;
v_openDecls_720_ = v_openDecls_539_;
v_initHeartbeats_721_ = v_initHeartbeats_540_;
v_maxHeartbeats_722_ = v_maxHeartbeats_541_;
v_quotContext_723_ = v_quotContext_542_;
v_currMacroScope_724_ = v_currMacroScope_543_;
v_cancelTk_x3f_725_ = v_cancelTk_x3f_544_;
v_inheritedTraceOptions_726_ = v_inheritedTraceOptions_545_;
v_currRecDepth_727_ = v_currRecDepth_531_;
v_ref_728_ = v_ref_532_;
v_suppressElabErrors_729_ = v_suppressElabErrors_533_;
v_isRecordingDeps_730_ = v_isRecordingDeps_534_;
v___y_731_ = v___y_446_;
goto v___jp_714_;
}
else
{
v___y_742_ = v___x_767_;
v___y_743_ = v___y_766_;
v___y_744_ = v___x_550_;
goto v___jp_741_;
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
LEAN_EXPORT void l_Lean_Meta_nativeEqTrue___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_438_ = stack[0].m_obj;
lean_object* v___x_439_ = stack[1].m_obj;
lean_object* v___x_440_ = stack[2].m_obj;
lean_object* v___x_441_ = stack[3].m_obj;
lean_object* v_a_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v___y_444_ = stack[6].m_obj;
lean_object* v___y_445_ = stack[7].m_obj;
lean_object* v___y_446_ = stack[8].m_obj;
lean_object* v_res_788_;
v_res_788_ = l_Lean_Meta_nativeEqTrue___lam__0(v_tacticName_438_, v___x_439_, v___x_440_, v___x_441_, v_a_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v_tacticName_789_, lean_object* v___x_790_, lean_object* v___x_791_, lean_object* v___x_792_, lean_object* v_a_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_nativeEqTrue___lam__0(v_tacticName_789_, v___x_790_, v___x_791_, v___x_792_, v_a_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(lean_object* v_env_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v_nextMacroScope_805_; lean_object* v_ngen_806_; lean_object* v_auxDeclNGen_807_; lean_object* v_traceState_808_; lean_object* v_recordedDeps_809_; lean_object* v_messages_810_; lean_object* v_infoState_811_; lean_object* v_snapshotTasks_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_838_; 
v___x_804_ = lean_st_ref_take(v___y_802_);
v_nextMacroScope_805_ = lean_ctor_get(v___x_804_, 1);
v_ngen_806_ = lean_ctor_get(v___x_804_, 2);
v_auxDeclNGen_807_ = lean_ctor_get(v___x_804_, 3);
v_traceState_808_ = lean_ctor_get(v___x_804_, 4);
v_recordedDeps_809_ = lean_ctor_get(v___x_804_, 6);
v_messages_810_ = lean_ctor_get(v___x_804_, 7);
v_infoState_811_ = lean_ctor_get(v___x_804_, 8);
v_snapshotTasks_812_ = lean_ctor_get(v___x_804_, 9);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_839_ = lean_ctor_get(v___x_804_, 5);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v___x_804_, 0);
lean_dec(v_unused_840_);
v___x_814_ = v___x_804_;
v_isShared_815_ = v_isSharedCheck_838_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_snapshotTasks_812_);
lean_inc(v_infoState_811_);
lean_inc(v_messages_810_);
lean_inc(v_recordedDeps_809_);
lean_inc(v_traceState_808_);
lean_inc(v_auxDeclNGen_807_);
lean_inc(v_ngen_806_);
lean_inc(v_nextMacroScope_805_);
lean_dec(v___x_804_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_838_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 5, v___x_816_);
lean_ctor_set(v___x_814_, 0, v_env_800_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_env_800_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_nextMacroScope_805_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_ngen_806_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_auxDeclNGen_807_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v_traceState_808_);
lean_ctor_set(v_reuseFailAlloc_837_, 5, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_837_, 6, v_recordedDeps_809_);
lean_ctor_set(v_reuseFailAlloc_837_, 7, v_messages_810_);
lean_ctor_set(v_reuseFailAlloc_837_, 8, v_infoState_811_);
lean_ctor_set(v_reuseFailAlloc_837_, 9, v_snapshotTasks_812_);
v___x_818_ = v_reuseFailAlloc_837_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_mctx_821_; lean_object* v_zetaDeltaFVarIds_822_; lean_object* v_postponed_823_; lean_object* v_diag_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_835_; 
v___x_819_ = lean_st_ref_put(v___y_802_, v___x_818_);
v___x_820_ = lean_st_ref_take(v___y_801_);
v_mctx_821_ = lean_ctor_get(v___x_820_, 0);
v_zetaDeltaFVarIds_822_ = lean_ctor_get(v___x_820_, 2);
v_postponed_823_ = lean_ctor_get(v___x_820_, 3);
v_diag_824_ = lean_ctor_get(v___x_820_, 4);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_820_, 1);
lean_dec(v_unused_836_);
v___x_826_ = v___x_820_;
v_isShared_827_ = v_isSharedCheck_835_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_diag_824_);
lean_inc(v_postponed_823_);
lean_inc(v_zetaDeltaFVarIds_822_);
lean_inc(v_mctx_821_);
lean_dec(v___x_820_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_835_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_828_ = lean_box(0);
v___x_829_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v___x_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_mctx_821_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_zetaDeltaFVarIds_822_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_postponed_823_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v_diag_824_);
v___x_831_ = v_reuseFailAlloc_834_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_st_ref_put(v___y_801_, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_828_);
return v___x_833_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_800_ = stack[0].m_obj;
lean_object* v___y_801_ = stack[1].m_obj;
lean_object* v___y_802_ = stack[2].m_obj;
lean_object* v_res_841_;
v_res_841_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_800_, v___y_801_, v___y_802_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg___boxed(lean_object* v_env_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
return v_res_846_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(lean_object* v_env_847_, lean_object* v_x_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; lean_object* v_env_855_; lean_object* v_a_857_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_854_ = lean_st_ref_get(v___y_852_);
v_env_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc_ref(v_env_855_);
lean_dec(v___x_854_);
v___x_867_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_847_, v___y_850_, v___y_852_);
lean_dec_ref(v___x_867_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
v___x_868_ = lean_apply_5(v_x_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, lean_box(0));
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_855_, v___y_850_, v___y_852_);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v___x_870_, 0);
lean_dec(v_unused_878_);
v___x_872_ = v___x_870_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_dec(v___x_870_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_a_869_);
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_869_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_868_, 1);
v_a_857_ = v_a_879_;
goto v___jp_856_;
}
v___jp_856_:
{
lean_object* v___x_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v___x_858_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_855_, v___y_850_, v___y_852_);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v___x_858_, 0);
lean_dec(v_unused_866_);
v___x_860_ = v___x_858_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_dec(v___x_858_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 1);
lean_ctor_set(v___x_860_, 0, v_a_857_);
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_857_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_847_ = stack[0].m_obj;
lean_object* v_x_848_ = stack[1].m_obj;
lean_object* v___y_849_ = stack[2].m_obj;
lean_object* v___y_850_ = stack[3].m_obj;
lean_object* v___y_851_ = stack[4].m_obj;
lean_object* v___y_852_ = stack[5].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_847_, v_x_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg___boxed(lean_object* v_env_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_881_, v_x_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_888_;
}
}
lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(lean_object* v_stx_889_, lean_object* v___y_890_){
_start:
{
uint8_t v___x_892_; lean_object* v___x_893_; 
v___x_892_ = 0;
v___x_893_ = l_Lean_Syntax_getRange_x3f(v_stx_889_, v___x_892_);
if (lean_obj_tag(v___x_893_) == 1)
{
lean_object* v_toCold_894_; lean_object* v_val_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_907_; 
v_toCold_894_ = lean_ctor_get(v___y_890_, 0);
v_val_895_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_907_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_907_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_val_895_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_907_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_fileMap_899_; lean_object* v_start_900_; lean_object* v_stop_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v_fileMap_899_ = lean_ctor_get(v_toCold_894_, 1);
v_start_900_ = lean_ctor_get(v_val_895_, 0);
lean_inc(v_start_900_);
v_stop_901_ = lean_ctor_get(v_val_895_, 1);
lean_inc(v_stop_901_);
lean_dec(v_val_895_);
lean_inc_ref(v_fileMap_899_);
v___x_902_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_899_, v_start_900_, v_stop_901_);
lean_dec(v_stop_901_);
lean_dec(v_start_900_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_902_);
v___x_904_ = v___x_897_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_906_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec(v___x_893_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_889_ = stack[0].m_obj;
lean_object* v___y_890_ = stack[1].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_889_, v___y_890_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg___boxed(lean_object* v_stx_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_911_, v___y_912_);
lean_dec_ref(v___y_912_);
lean_dec(v_stx_911_);
return v_res_914_;
}
}
lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(lean_object* v_declName_915_, lean_object* v_declRanges_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
uint8_t v___x_920_; 
v___x_920_ = l_Lean_Name_isAnonymous(v_declName_915_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_env_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_921_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_922_ = lean_st_ref_get(v___y_918_);
v_env_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc_ref(v_env_923_);
lean_dec(v___x_922_);
v___x_924_ = l_Lean_declRangeExt;
v___x_925_ = lean_box(1);
lean_inc(v_declName_915_);
v___x_926_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_921_, v___x_924_, v_env_923_, v_declName_915_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v_env_928_; lean_object* v_nextMacroScope_929_; lean_object* v_ngen_930_; lean_object* v_auxDeclNGen_931_; lean_object* v_traceState_932_; lean_object* v_recordedDeps_933_; lean_object* v_messages_934_; lean_object* v_infoState_935_; lean_object* v_snapshotTasks_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_963_; 
v___x_927_ = lean_st_ref_take(v___y_918_);
v_env_928_ = lean_ctor_get(v___x_927_, 0);
v_nextMacroScope_929_ = lean_ctor_get(v___x_927_, 1);
v_ngen_930_ = lean_ctor_get(v___x_927_, 2);
v_auxDeclNGen_931_ = lean_ctor_get(v___x_927_, 3);
v_traceState_932_ = lean_ctor_get(v___x_927_, 4);
v_recordedDeps_933_ = lean_ctor_get(v___x_927_, 6);
v_messages_934_ = lean_ctor_get(v___x_927_, 7);
v_infoState_935_ = lean_ctor_get(v___x_927_, 8);
v_snapshotTasks_936_ = lean_ctor_get(v___x_927_, 9);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v___x_927_, 5);
lean_dec(v_unused_964_);
v___x_938_ = v___x_927_;
v_isShared_939_ = v_isSharedCheck_963_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snapshotTasks_936_);
lean_inc(v_infoState_935_);
lean_inc(v_messages_934_);
lean_inc(v_recordedDeps_933_);
lean_inc(v_traceState_932_);
lean_inc(v_auxDeclNGen_931_);
lean_inc(v_ngen_930_);
lean_inc(v_nextMacroScope_929_);
lean_inc(v_env_928_);
lean_dec(v___x_927_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_963_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_924_, v_env_928_, v_declName_915_, v_declRanges_916_, v___x_926_);
v___x_941_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 5, v___x_941_);
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_nextMacroScope_929_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_ngen_930_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_auxDeclNGen_931_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v_traceState_932_);
lean_ctor_set(v_reuseFailAlloc_962_, 5, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_962_, 6, v_recordedDeps_933_);
lean_ctor_set(v_reuseFailAlloc_962_, 7, v_messages_934_);
lean_ctor_set(v_reuseFailAlloc_962_, 8, v_infoState_935_);
lean_ctor_set(v_reuseFailAlloc_962_, 9, v_snapshotTasks_936_);
v___x_943_ = v_reuseFailAlloc_962_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_mctx_946_; lean_object* v_zetaDeltaFVarIds_947_; lean_object* v_postponed_948_; lean_object* v_diag_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_960_; 
v___x_944_ = lean_st_ref_put(v___y_918_, v___x_943_);
v___x_945_ = lean_st_ref_take(v___y_917_);
v_mctx_946_ = lean_ctor_get(v___x_945_, 0);
v_zetaDeltaFVarIds_947_ = lean_ctor_get(v___x_945_, 2);
v_postponed_948_ = lean_ctor_get(v___x_945_, 3);
v_diag_949_ = lean_ctor_get(v___x_945_, 4);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_945_, 1);
lean_dec(v_unused_961_);
v___x_951_ = v___x_945_;
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_diag_949_);
lean_inc(v_postponed_948_);
lean_inc(v_zetaDeltaFVarIds_947_);
lean_inc(v_mctx_946_);
lean_dec(v___x_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_953_ = lean_box(0);
v___x_954_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_mctx_946_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_zetaDeltaFVarIds_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_postponed_948_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_diag_949_);
v___x_956_ = v_reuseFailAlloc_959_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_st_ref_put(v___y_917_, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_953_);
return v___x_958_;
}
}
}
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_declRanges_916_);
lean_dec(v_declName_915_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec_ref(v_declRanges_916_);
lean_dec(v_declName_915_);
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT void l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_915_ = stack[0].m_obj;
lean_object* v_declRanges_916_ = stack[1].m_obj;
lean_object* v___y_917_ = stack[2].m_obj;
lean_object* v___y_918_ = stack[3].m_obj;
lean_object* v_res_969_;
v_res_969_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_915_, v_declRanges_916_, v___y_917_, v___y_918_);
stack->m_obj
 = v_res_969_;
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg___boxed(lean_object* v_declName_970_, lean_object* v_declRanges_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_970_, v_declRanges_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec(v___y_972_);
return v_res_975_;
}
}
lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_declName_976_, lean_object* v_rangeStx_977_, lean_object* v_selectionRangeStx_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1001_; 
v___x_984_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_rangeStx_977_, v___y_981_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1001_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1001_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
if (lean_obj_tag(v_a_985_) == 1)
{
lean_object* v_val_989_; lean_object* v_a_991_; lean_object* v___x_994_; lean_object* v_a_995_; 
lean_del_object(v___x_987_);
v_val_989_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v_a_985_, 1);
v___x_994_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_selectionRangeStx_978_, v___y_981_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v___x_994_);
if (lean_obj_tag(v_a_995_) == 0)
{
lean_inc(v_val_989_);
v_a_991_ = v_val_989_;
goto v___jp_990_;
}
else
{
lean_object* v_val_996_; 
v_val_996_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v_a_995_, 1);
v_a_991_ = v_val_996_;
goto v___jp_990_;
}
v___jp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_val_989_);
lean_ctor_set(v___x_992_, 1, v_a_991_);
v___x_993_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_976_, v___x_992_, v___y_980_, v___y_982_);
return v___x_993_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec(v_a_985_);
lean_dec(v_declName_976_);
v___x_997_ = lean_box(0);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_997_);
v___x_999_ = v___x_987_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_976_ = stack[0].m_obj;
lean_object* v_rangeStx_977_ = stack[1].m_obj;
lean_object* v_selectionRangeStx_978_ = stack[2].m_obj;
lean_object* v___y_979_ = stack[3].m_obj;
lean_object* v___y_980_ = stack[4].m_obj;
lean_object* v___y_981_ = stack[5].m_obj;
lean_object* v___y_982_ = stack[6].m_obj;
lean_object* v_res_1002_;
v_res_1002_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_declName_976_, v_rangeStx_977_, v_selectionRangeStx_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
stack->m_obj
 = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8___boxed(lean_object* v_declName_1003_, lean_object* v_rangeStx_1004_, lean_object* v_selectionRangeStx_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_declName_1003_, v_rangeStx_1004_, v_selectionRangeStx_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_selectionRangeStx_1005_);
lean_dec(v_rangeStx_1004_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
if (lean_obj_tag(v_a_1012_) == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = l_List_reverse___redArg(v_a_1013_);
return v___x_1014_;
}
else
{
lean_object* v_head_1015_; lean_object* v_tail_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1025_; 
v_head_1015_ = lean_ctor_get(v_a_1012_, 0);
v_tail_1016_ = lean_ctor_get(v_a_1012_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_a_1012_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1018_ = v_a_1012_;
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_tail_1016_);
lean_inc(v_head_1015_);
lean_dec(v_a_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = l_Lean_mkLevelParam(v_head_1015_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_a_1013_);
lean_ctor_set(v___x_1018_, 0, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_a_1013_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
v_a_1012_ = v_tail_1016_;
v_a_1013_ = v___x_1022_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_unsigned_to_nat(16u);
v___x_1028_ = lean_mk_array(v___x_1027_, v___x_1026_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_1035_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_1036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
lean_ctor_set(v___x_1036_, 2, v___x_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = l_Lean_Level_ofNat(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_1051_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_1055_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_1056_ = l_Lean_mkConst(v___x_1055_, v___x_1054_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_1059_ = l_Lean_mkConst(v___x_1058_, v___x_1057_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_1066_ = l_Lean_mkConst(v___x_1065_, v___x_1064_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_1073_, lean_object* v_e_1074_, lean_object* v_axiomDeclRange_x3f_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___x_1089_; lean_object* v_a_1090_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; uint8_t v___x_1196_; 
v___x_1089_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_1074_, v_a_1077_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v___x_1089_);
v___x_1196_ = l_Lean_Expr_hasFVar(v_a_1090_);
if (v___x_1196_ == 0)
{
v___y_1175_ = v_a_1076_;
v___y_1176_ = v_a_1077_;
v___y_1177_ = v_a_1078_;
v___y_1178_ = v_a_1079_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v___x_1197_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1198_ = l_Lean_MessageData_ofName(v_tacticName_1073_);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_indentExpr(v_a_1090_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1203_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
v___jp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(v___y_1082_, v___x_1084_);
v___x_1086_ = l_Lean_mkConst(v___y_1083_, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
v___jp_1091_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_params_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1171_; 
v___x_1096_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1090_);
v___x_1097_ = l_Lean_collectLevelParams(v___x_1096_, v_a_1090_);
v_params_1098_ = lean_ctor_get(v___x_1097_, 2);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; 
v_unused_1172_ = lean_ctor_get(v___x_1097_, 1);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v___x_1097_, 0);
lean_dec(v_unused_1173_);
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1171_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_params_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1171_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v_env_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_array_to_list(v_params_1098_);
v___x_1104_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_1073_);
v___x_1105_ = l_Lean_Name_append(v___x_1104_, v_tacticName_1073_);
v___x_1106_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1105_);
v___x_1107_ = l_Lean_Name_append(v___x_1105_, v___x_1106_);
lean_inc(v_a_1090_);
lean_inc(v___x_1103_);
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1108_, 0, v_tacticName_1073_);
lean_closure_set(v___f_1108_, 1, v___x_1107_);
lean_closure_set(v___f_1108_, 2, v___x_1103_);
lean_closure_set(v___f_1108_, 3, v___x_1102_);
lean_closure_set(v___f_1108_, 4, v_a_1090_);
v___x_1109_ = lean_st_ref_get(v___y_1095_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = l_Lean_Environment_unlockAsync(v_env_1110_);
v___x_1112_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v___x_1111_, v___f_1108_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1162_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1162_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1162_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_unbox(v_a_1113_);
lean_dec(v_a_1113_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec(v___x_1105_);
lean_dec(v___x_1103_);
lean_del_object(v___x_1100_);
lean_dec(v_a_1090_);
v___x_1118_ = lean_box(1);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1118_);
v___x_1120_ = v___x_1115_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1161_; 
lean_del_object(v___x_1115_);
v___x_1122_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1123_ = l_Lean_Name_append(v___x_1105_, v___x_1122_);
v___x_1124_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1123_, v___y_1095_);
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1161_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1161_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1129_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1130_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1131_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1132_ = l_Lean_mkApp3(v___x_1129_, v___x_1130_, v_a_1090_, v___x_1131_);
lean_inc(v___x_1103_);
lean_inc(v_a_1125_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 2, v___x_1132_);
lean_ctor_set(v___x_1100_, 1, v___x_1103_);
lean_ctor_set(v___x_1100_, 0, v_a_1125_);
v___x_1134_ = v___x_1100_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = 0;
v___x_1136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*1, v___x_1135_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1136_);
v___x_1138_ = v___x_1127_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_addDecl(v___x_1138_, v___x_1135_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_dec_ref_known(v___x_1139_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1075_) == 1)
{
lean_object* v_val_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_val_1140_ = lean_ctor_get(v_axiomDeclRange_x3f_1075_, 0);
v___x_1141_ = lean_box(0);
lean_inc(v_a_1125_);
v___x_1142_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_a_1125_, v_val_1140_, v___x_1141_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref_known(v___x_1142_, 1);
v___y_1082_ = v___x_1103_;
v___y_1083_ = v_a_1125_;
goto v___jp_1081_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_a_1125_);
lean_dec(v___x_1103_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
v___y_1082_ = v___x_1103_;
v___y_1083_ = v_a_1125_;
goto v___jp_1081_;
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_a_1125_);
lean_dec(v___x_1103_);
v_a_1151_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1139_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1139_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
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
}
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v___x_1105_);
lean_dec(v___x_1103_);
lean_del_object(v___x_1100_);
lean_dec(v_a_1090_);
v_a_1163_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1112_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1112_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
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
}
v___jp_1174_:
{
uint8_t v___x_1179_; 
v___x_1179_ = l_Lean_Expr_hasMVar(v_a_1090_);
if (v___x_1179_ == 0)
{
v___y_1092_ = v___y_1175_;
v___y_1093_ = v___y_1176_;
v___y_1094_ = v___y_1177_;
v___y_1095_ = v___y_1178_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
v___x_1180_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1181_ = l_Lean_MessageData_ofName(v_tacticName_1073_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_indentExpr(v_a_1090_);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1186_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_nativeEqTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_1073_ = stack[0].m_obj;
lean_object* v_e_1074_ = stack[1].m_obj;
lean_object* v_axiomDeclRange_x3f_1075_ = stack[2].m_obj;
lean_object* v_a_1076_ = stack[3].m_obj;
lean_object* v_a_1077_ = stack[4].m_obj;
lean_object* v_a_1078_ = stack[5].m_obj;
lean_object* v_a_1079_ = stack[6].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1073_, v_e_1074_, v_axiomDeclRange_x3f_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1214_, lean_object* v_e_1215_, lean_object* v_axiomDeclRange_x3f_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1214_, v_e_1215_, v_axiomDeclRange_x3f_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_axiomDeclRange_x3f_1216_);
return v_res_1222_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1229_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1224_ = stack[1].m_obj;
lean_object* v___y_1225_ = stack[2].m_obj;
lean_object* v___y_1226_ = stack[3].m_obj;
lean_object* v___y_1227_ = stack[4].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_box(0), v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1237_;
}
}
lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1238_, lean_object* v_constName_1239_, uint8_t v_checkMeta_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1239_, v_checkMeta_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT void l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1239_ = stack[1].m_obj;
uint8_t v_checkMeta_1240_ = stack[2].m_num;
lean_object* v___y_1241_ = stack[3].m_obj;
lean_object* v___y_1242_ = stack[4].m_obj;
lean_object* v___y_1243_ = stack[5].m_obj;
lean_object* v___y_1244_ = stack[6].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_box(0), v_constName_1239_, v_checkMeta_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_constName_1249_, lean_object* v_checkMeta_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v_checkMeta_boxed_1256_; lean_object* v_res_1257_; 
v_checkMeta_boxed_1256_ = lean_unbox(v_checkMeta_1250_);
v_res_1257_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1248_, v_constName_1249_, v_checkMeta_boxed_1256_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1257_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1258_, lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1259_ = stack[1].m_obj;
lean_object* v___y_1260_ = stack[2].m_obj;
lean_object* v___y_1261_ = stack[3].m_obj;
lean_object* v___y_1262_ = stack[4].m_obj;
lean_object* v___y_1263_ = stack[5].m_obj;
lean_object* v_res_1266_;
v_res_1266_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_box(0), v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
stack->m_obj
 = v_res_1266_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_msg_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1267_, v_msg_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1274_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(lean_object* v_env_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_1275_, v___y_1277_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1275_ = stack[0].m_obj;
lean_object* v___y_1276_ = stack[1].m_obj;
lean_object* v___y_1277_ = stack[2].m_obj;
lean_object* v___y_1278_ = stack[3].m_obj;
lean_object* v___y_1279_ = stack[4].m_obj;
lean_object* v_res_1282_;
v_res_1282_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(v_env_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
stack->m_obj
 = v_res_1282_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___boxed(lean_object* v_env_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(v_env_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_00_u03b1_1290_, lean_object* v_env_1291_, lean_object* v_x_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_1291_, v_x_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1291_ = stack[1].m_obj;
lean_object* v_x_1292_ = stack[2].m_obj;
lean_object* v___y_1293_ = stack[3].m_obj;
lean_object* v___y_1294_ = stack[4].m_obj;
lean_object* v___y_1295_ = stack[5].m_obj;
lean_object* v___y_1296_ = stack[6].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(lean_box(0), v_env_1291_, v_x_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object* v_00_u03b1_1300_, lean_object* v_env_1301_, lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(v_00_u03b1_1300_, v_env_1301_, v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1308_;
}
}
lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(lean_object* v_stx_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_1309_, v___y_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT void l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1309_ = stack[0].m_obj;
lean_object* v___y_1310_ = stack[1].m_obj;
lean_object* v___y_1311_ = stack[2].m_obj;
lean_object* v___y_1312_ = stack[3].m_obj;
lean_object* v___y_1313_ = stack[4].m_obj;
lean_object* v_res_1316_;
v_res_1316_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(v_stx_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
stack->m_obj
 = v_res_1316_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___boxed(lean_object* v_stx_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(v_stx_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v_stx_1317_);
return v_res_1323_;
}
}
lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(lean_object* v_declName_1324_, lean_object* v_declRanges_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_1324_, v_declRanges_1325_, v___y_1327_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT void l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1324_ = stack[0].m_obj;
lean_object* v_declRanges_1325_ = stack[1].m_obj;
lean_object* v___y_1326_ = stack[2].m_obj;
lean_object* v___y_1327_ = stack[3].m_obj;
lean_object* v___y_1328_ = stack[4].m_obj;
lean_object* v___y_1329_ = stack[5].m_obj;
lean_object* v_res_1332_;
v_res_1332_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(v_declName_1324_, v_declRanges_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
stack->m_obj
 = v_res_1332_;
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___boxed(lean_object* v_declName_1333_, lean_object* v_declRanges_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(v_declName_1333_, v_declRanges_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1340_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1342_ = stack[1].m_obj;
lean_object* v___y_1343_ = stack[2].m_obj;
lean_object* v___y_1344_ = stack[3].m_obj;
lean_object* v___y_1345_ = stack[4].m_obj;
lean_object* v___y_1346_ = stack[5].m_obj;
lean_object* v_res_1349_;
v_res_1349_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_box(0), v_x_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
stack->m_obj
 = v_res_1349_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1350_, v_x_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1357_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Native(builtin);
}
#ifdef __cplusplus
}
#endif

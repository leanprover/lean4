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
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
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
extern lean_object* l_Lean_declRangeExt;
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__7;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__8;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__9;
static lean_once_cell_t l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_nativeEqTrue___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` failed. Error: "};
static const lean_object* l_Lean_Meta_nativeEqTrue___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__11_value;
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
static const lean_ctor_object l_Lean_Meta_nativeEqTrue___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_nativeEqTrue___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object* v_auxDeclName_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___boxed(lean_object* v_auxDeclName_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(v_auxDeclName_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object* v_e_146_, lean_object* v___y_147_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = l_Lean_Expr_hasMVar(v_e_146_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v_e_146_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v_mctx_152_; lean_object* v___x_153_; lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v___x_156_; lean_object* v_cache_157_; lean_object* v_zetaDeltaFVarIds_158_; lean_object* v_postponed_159_; lean_object* v_diag_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_169_; 
v___x_151_ = lean_st_ref_get(v___y_147_);
v_mctx_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_mctx_152_);
lean_dec(v___x_151_);
v___x_153_ = l_Lean_instantiateMVarsCore(v_mctx_152_, v_e_146_);
v_fst_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_fst_154_);
v_snd_155_ = lean_ctor_get(v___x_153_, 1);
lean_inc(v_snd_155_);
lean_dec_ref(v___x_153_);
v___x_156_ = lean_st_ref_take(v___y_147_);
v_cache_157_ = lean_ctor_get(v___x_156_, 1);
v_zetaDeltaFVarIds_158_ = lean_ctor_get(v___x_156_, 2);
v_postponed_159_ = lean_ctor_get(v___x_156_, 3);
v_diag_160_ = lean_ctor_get(v___x_156_, 4);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v___x_156_, 0);
lean_dec(v_unused_170_);
v___x_162_ = v___x_156_;
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_diag_160_);
lean_inc(v_postponed_159_);
lean_inc(v_zetaDeltaFVarIds_158_);
lean_inc(v_cache_157_);
lean_dec(v___x_156_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v_snd_155_);
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_snd_155_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_cache_157_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_zetaDeltaFVarIds_158_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_postponed_159_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_diag_160_);
v___x_165_ = v_reuseFailAlloc_168_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_st_ref_put(v___y_147_, v___x_165_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v_fst_154_);
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object* v_e_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_171_, v___y_172_);
lean_dec(v___y_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object* v_e_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_175_, v___y_177_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object* v_e_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(v_e_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object* v_kind_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v_auxDeclNGen_193_; lean_object* v___x_194_; lean_object* v_env_195_; lean_object* v___x_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_199_; lean_object* v_env_200_; lean_object* v_nextMacroScope_201_; lean_object* v_ngen_202_; lean_object* v_traceState_203_; lean_object* v_cache_204_; lean_object* v_recordedDeps_205_; lean_object* v_messages_206_; lean_object* v_infoState_207_; lean_object* v_snapshotTasks_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_217_; 
v___x_192_ = lean_st_ref_get(v___y_190_);
v_auxDeclNGen_193_ = lean_ctor_get(v___x_192_, 3);
lean_inc_ref(v_auxDeclNGen_193_);
lean_dec(v___x_192_);
v___x_194_ = lean_st_ref_get(v___y_190_);
v_env_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc_ref(v_env_195_);
lean_dec(v___x_194_);
v___x_196_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_195_, v_auxDeclNGen_193_, v_kind_189_);
v_fst_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_fst_197_);
v_snd_198_ = lean_ctor_get(v___x_196_, 1);
lean_inc(v_snd_198_);
lean_dec_ref(v___x_196_);
v___x_199_ = lean_st_ref_take(v___y_190_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
v_nextMacroScope_201_ = lean_ctor_get(v___x_199_, 1);
v_ngen_202_ = lean_ctor_get(v___x_199_, 2);
v_traceState_203_ = lean_ctor_get(v___x_199_, 4);
v_cache_204_ = lean_ctor_get(v___x_199_, 5);
v_recordedDeps_205_ = lean_ctor_get(v___x_199_, 6);
v_messages_206_ = lean_ctor_get(v___x_199_, 7);
v_infoState_207_ = lean_ctor_get(v___x_199_, 8);
v_snapshotTasks_208_ = lean_ctor_get(v___x_199_, 9);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v___x_199_, 3);
lean_dec(v_unused_218_);
v___x_210_ = v___x_199_;
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_snapshotTasks_208_);
lean_inc(v_infoState_207_);
lean_inc(v_messages_206_);
lean_inc(v_recordedDeps_205_);
lean_inc(v_cache_204_);
lean_inc(v_traceState_203_);
lean_inc(v_ngen_202_);
lean_inc(v_nextMacroScope_201_);
lean_inc(v_env_200_);
lean_dec(v___x_199_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 3, v_snd_198_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_env_200_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_nextMacroScope_201_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_ngen_202_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_snd_198_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_traceState_203_);
lean_ctor_set(v_reuseFailAlloc_216_, 5, v_cache_204_);
lean_ctor_set(v_reuseFailAlloc_216_, 6, v_recordedDeps_205_);
lean_ctor_set(v_reuseFailAlloc_216_, 7, v_messages_206_);
lean_ctor_set(v_reuseFailAlloc_216_, 8, v_infoState_207_);
lean_ctor_set(v_reuseFailAlloc_216_, 9, v_snapshotTasks_208_);
v___x_213_ = v_reuseFailAlloc_216_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_st_ref_put(v___y_190_, v___x_213_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v_fst_197_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object* v_kind_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_219_, v___y_220_);
lean_dec(v___y_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object* v_kind_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_223_, v___y_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object* v_kind_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_237_, lean_object* v_opt_238_){
_start:
{
lean_object* v_name_239_; lean_object* v_defValue_240_; lean_object* v_map_241_; lean_object* v___x_242_; 
v_name_239_ = lean_ctor_get(v_opt_238_, 0);
v_defValue_240_ = lean_ctor_get(v_opt_238_, 1);
v_map_241_ = lean_ctor_get(v_opts_237_, 0);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_241_, v_name_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_inc(v_defValue_240_);
return v_defValue_240_;
}
else
{
lean_object* v_val_243_; 
v_val_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v___x_242_, 1);
if (lean_obj_tag(v_val_243_) == 3)
{
lean_object* v_v_244_; 
v_v_244_ = lean_ctor_get(v_val_243_, 0);
lean_inc(v_v_244_);
lean_dec_ref_known(v_val_243_, 1);
return v_v_244_;
}
else
{
lean_dec(v_val_243_);
lean_inc(v_defValue_240_);
return v_defValue_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_245_, lean_object* v_opt_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_245_, v_opt_246_);
lean_dec_ref(v_opt_246_);
lean_dec_ref(v_opts_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object* v_msgData_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; lean_object* v_env_255_; uint8_t v___x_256_; lean_object* v_env_257_; lean_object* v___x_258_; lean_object* v_toCold_259_; lean_object* v_mctx_260_; lean_object* v_lctx_261_; lean_object* v_options_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_254_ = lean_st_ref_get(v___y_252_);
v_env_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_ref(v_env_255_);
lean_dec(v___x_254_);
v___x_256_ = 0;
v_env_257_ = l_Lean_Environment_setRecordingDeps(v_env_255_, v___x_256_);
v___x_258_ = lean_st_ref_get(v___y_250_);
v_toCold_259_ = lean_ctor_get(v___y_251_, 0);
v_mctx_260_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_mctx_260_);
lean_dec(v___x_258_);
v_lctx_261_ = lean_ctor_get(v___y_249_, 2);
v_options_262_ = lean_ctor_get(v_toCold_259_, 2);
lean_inc_ref(v_options_262_);
lean_inc_ref(v_lctx_261_);
v___x_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_263_, 0, v_env_257_);
lean_ctor_set(v___x_263_, 1, v_mctx_260_);
lean_ctor_set(v___x_263_, 2, v_lctx_261_);
lean_ctor_set(v___x_263_, 3, v_options_262_);
v___x_264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_msgData_248_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msgData_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_ref_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_ref_279_ = lean_ctor_get(v___y_276_, 2);
v___x_280_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msg_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
lean_inc(v_ref_279_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_ref_279_);
lean_ctor_set(v___x_285_, 1, v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(lean_object* v_o_300_, lean_object* v_k_301_, uint8_t v_v_302_){
_start:
{
lean_object* v_map_303_; uint8_t v_hasTrace_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_318_; 
v_map_303_ = lean_ctor_get(v_o_300_, 0);
v_hasTrace_304_ = lean_ctor_get_uint8(v_o_300_, sizeof(void*)*1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_o_300_);
if (v_isSharedCheck_318_ == 0)
{
v___x_306_ = v_o_300_;
v_isShared_307_ = v_isSharedCheck_318_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_map_303_);
lean_dec(v_o_300_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_318_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_308_, 0, v_v_302_);
lean_inc(v_k_301_);
v___x_309_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_301_, v___x_308_, v_map_303_);
if (v_hasTrace_304_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; lean_object* v___x_313_; 
v___x_310_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__1));
v___x_311_ = l_Lean_Name_isPrefixOf(v___x_310_, v_k_301_);
lean_dec(v_k_301_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_313_ = v___x_306_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_309_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_311_);
return v___x_313_;
}
}
else
{
lean_object* v___x_316_; 
lean_dec(v_k_301_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_316_ = v___x_306_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_317_, sizeof(void*)*1, v_hasTrace_304_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___boxed(lean_object* v_o_319_, lean_object* v_k_320_, lean_object* v_v_321_){
_start:
{
uint8_t v_v_boxed_322_; lean_object* v_res_323_; 
v_v_boxed_322_ = lean_unbox(v_v_321_);
v_res_323_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(v_o_319_, v_k_320_, v_v_boxed_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_opts_324_, lean_object* v_opt_325_, uint8_t v_val_326_){
_start:
{
lean_object* v_name_327_; lean_object* v___x_328_; 
v_name_327_ = lean_ctor_get(v_opt_325_, 0);
lean_inc(v_name_327_);
lean_dec_ref(v_opt_325_);
v___x_328_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(v_opts_324_, v_name_327_, v_val_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_opts_329_, lean_object* v_opt_330_, lean_object* v_val_331_){
_start:
{
uint8_t v_val_boxed_332_; lean_object* v_res_333_; 
v_val_boxed_332_ = lean_unbox(v_val_331_);
v_res_333_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v_opts_329_, v_opt_330_, v_val_boxed_332_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_box(0);
v___x_335_ = l_Lean_Elab_abortCommandExceptionId;
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___boxed(lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(lean_object* v_x_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_348_ = lean_ctor_get(v_x_342_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v_x_342_, 1);
v___x_349_ = l_Lean_stringToMessageData(v_a_348_);
v___x_350_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_349_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
return v___x_350_;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v_x_342_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v_x_342_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v_x_342_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 0);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg___boxed(lean_object* v_x_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(lean_object* v_constName_366_, uint8_t v_checkMeta_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v_env_374_; uint8_t v___x_375_; 
v___x_373_ = lean_st_ref_get(v___y_371_);
v_env_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc_ref(v_env_374_);
lean_dec(v___x_373_);
lean_inc(v_constName_366_);
v___x_375_ = lean_has_compile_error(v_env_374_, v_constName_366_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v_env_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_376_ = lean_st_ref_get(v___y_371_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_370_);
v___x_379_ = l_Lean_Environment_evalConst___redArg(v_env_377_, v___x_378_, v_constName_366_, v_checkMeta_367_);
lean_dec(v_constName_366_);
lean_dec_ref(v___x_378_);
lean_dec_ref(v_env_377_);
v___x_380_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_379_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; lean_object* v_env_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec_ref_known(v___x_381_, 1);
v___x_382_ = lean_st_ref_get(v___y_371_);
v_env_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc_ref(v_env_383_);
lean_dec(v___x_382_);
v___x_384_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_370_);
v___x_385_ = l_Lean_Environment_evalConst___redArg(v_env_383_, v___x_384_, v_constName_366_, v_checkMeta_367_);
lean_dec(v_constName_366_);
lean_dec_ref(v___x_384_);
lean_dec_ref(v_env_383_);
v___x_386_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_385_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_386_;
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_constName_366_);
v_a_387_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_381_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_381_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg___boxed(lean_object* v_constName_395_, lean_object* v_checkMeta_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v_checkMeta_boxed_402_; lean_object* v_res_403_; 
v_checkMeta_boxed_402_ = lean_unbox(v_checkMeta_396_);
v_res_403_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_395_, v_checkMeta_boxed_402_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_403_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_box(0);
v___x_414_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__5));
v___x_415_ = l_Lean_mkConst(v___x_414_, v___x_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__7, &l_Lean_Meta_nativeEqTrue___lam__0___closed__7_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__7);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
v___x_422_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_ctor_set(v___x_422_, 2, v___x_421_);
lean_ctor_set(v___x_422_, 3, v___x_421_);
lean_ctor_set(v___x_422_, 4, v___x_421_);
lean_ctor_set(v___x_422_, 5, v___x_421_);
lean_ctor_set(v___x_422_, 6, v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__11));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_426_, lean_object* v_tacticName_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_a_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_780_; 
v___x_436_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_426_, v___y_434_);
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_780_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_780_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_780_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_455_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__6, &l_Lean_Meta_nativeEqTrue___lam__0___closed__6_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__6);
lean_inc_n(v_a_437_, 2);
v___x_456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_456_, 0, v_a_437_);
lean_ctor_set(v___x_456_, 1, v___x_428_);
lean_ctor_set(v___x_456_, 2, v___x_455_);
v___x_457_ = lean_box(1);
v___x_458_ = 1;
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v_a_437_);
lean_ctor_set(v___x_459_, 1, v___x_429_);
v___x_460_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_460_, 0, v___x_456_);
lean_ctor_set(v___x_460_, 1, v_a_430_);
lean_ctor_set(v___x_460_, 2, v___x_457_);
lean_ctor_set(v___x_460_, 3, v___x_459_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*4, v___x_458_);
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 1);
lean_ctor_set(v___x_439_, 0, v___x_460_);
v___x_462_ = v___x_439_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_779_;
goto v_reusejp_461_;
}
v___jp_441_:
{
uint8_t v___x_442_; lean_object* v___x_443_; 
v___x_442_ = 1;
v___x_443_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_a_437_, v___x_442_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_dec_ref(v___y_433_);
lean_dec(v_tacticName_427_);
return v___x_443_;
}
else
{
lean_object* v_a_444_; uint8_t v___x_445_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v___x_445_ = l_Lean_Exception_isInterrupt(v_a_444_);
if (v___x_445_ == 0)
{
uint8_t v___x_446_; 
lean_inc(v_a_444_);
v___x_446_ = l_Lean_Exception_isRuntime(v_a_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_447_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_448_ = l_Lean_MessageData_ofName(v_tacticName_427_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = l_Lean_Exception_toMessageData(v_a_444_);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_453_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec_ref(v___y_433_);
return v___x_454_;
}
else
{
lean_dec_ref(v___y_433_);
lean_dec(v_tacticName_427_);
return v___x_443_;
}
}
else
{
lean_dec_ref(v___y_433_);
lean_dec(v_tacticName_427_);
return v___x_443_;
}
}
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v_env_464_; lean_object* v_nextMacroScope_465_; lean_object* v_ngen_466_; lean_object* v_auxDeclNGen_467_; lean_object* v_traceState_468_; lean_object* v_recordedDeps_469_; lean_object* v_messages_470_; lean_object* v_infoState_471_; lean_object* v_snapshotTasks_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_777_; 
v___x_463_ = lean_st_ref_take(v___y_434_);
v_env_464_ = lean_ctor_get(v___x_463_, 0);
v_nextMacroScope_465_ = lean_ctor_get(v___x_463_, 1);
v_ngen_466_ = lean_ctor_get(v___x_463_, 2);
v_auxDeclNGen_467_ = lean_ctor_get(v___x_463_, 3);
v_traceState_468_ = lean_ctor_get(v___x_463_, 4);
v_recordedDeps_469_ = lean_ctor_get(v___x_463_, 6);
v_messages_470_ = lean_ctor_get(v___x_463_, 7);
v_infoState_471_ = lean_ctor_get(v___x_463_, 8);
v_snapshotTasks_472_ = lean_ctor_get(v___x_463_, 9);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_463_, 5);
lean_dec(v_unused_778_);
v___x_474_ = v___x_463_;
v_isShared_475_ = v_isSharedCheck_777_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snapshotTasks_472_);
lean_inc(v_infoState_471_);
lean_inc(v_messages_470_);
lean_inc(v_recordedDeps_469_);
lean_inc(v_traceState_468_);
lean_inc(v_auxDeclNGen_467_);
lean_inc(v_ngen_466_);
lean_inc(v_nextMacroScope_465_);
lean_inc(v_env_464_);
lean_dec(v___x_463_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_777_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
lean_inc(v_a_437_);
v___x_476_ = l_Lean_markMeta(v_env_464_, v_a_437_);
v___x_477_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 5, v___x_477_);
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_nextMacroScope_465_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_ngen_466_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_auxDeclNGen_467_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_traceState_468_);
lean_ctor_set(v_reuseFailAlloc_776_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_776_, 6, v_recordedDeps_469_);
lean_ctor_set(v_reuseFailAlloc_776_, 7, v_messages_470_);
lean_ctor_set(v_reuseFailAlloc_776_, 8, v_infoState_471_);
lean_ctor_set(v_reuseFailAlloc_776_, 9, v_snapshotTasks_472_);
v___x_479_ = v_reuseFailAlloc_776_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_zetaDeltaFVarIds_483_; lean_object* v_postponed_484_; lean_object* v_diag_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_774_; 
v___x_480_ = lean_st_ref_put(v___y_434_, v___x_479_);
v___x_481_ = lean_st_ref_take(v___y_432_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
v_zetaDeltaFVarIds_483_ = lean_ctor_get(v___x_481_, 2);
v_postponed_484_ = lean_ctor_get(v___x_481_, 3);
v_diag_485_ = lean_ctor_get(v___x_481_, 4);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_481_, 1);
lean_dec(v_unused_775_);
v___x_487_ = v___x_481_;
v_isShared_488_ = v_isSharedCheck_774_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_diag_485_);
lean_inc(v_postponed_484_);
lean_inc(v_zetaDeltaFVarIds_483_);
lean_inc(v_mctx_482_);
lean_dec(v___x_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_774_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_mctx_482_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_zetaDeltaFVarIds_483_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_postponed_484_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_diag_485_);
v___x_491_ = v_reuseFailAlloc_773_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v_toCold_493_; lean_object* v_currRecDepth_494_; lean_object* v_ref_495_; uint8_t v_suppressElabErrors_496_; uint8_t v_checkDeprecated_497_; uint8_t v_isRecordingDeps_498_; lean_object* v_fileName_499_; lean_object* v_fileMap_500_; lean_object* v_options_501_; lean_object* v_currNamespace_502_; lean_object* v_openDecls_503_; lean_object* v_initHeartbeats_504_; lean_object* v_maxHeartbeats_505_; lean_object* v_quotContext_506_; lean_object* v_currMacroScope_507_; lean_object* v_cancelTk_x3f_508_; lean_object* v_inheritedTraceOptions_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_771_; 
v___x_492_ = lean_st_ref_put(v___y_432_, v___x_491_);
v_toCold_493_ = lean_ctor_get(v___y_433_, 0);
lean_inc_ref(v_toCold_493_);
v_currRecDepth_494_ = lean_ctor_get(v___y_433_, 1);
v_ref_495_ = lean_ctor_get(v___y_433_, 2);
v_suppressElabErrors_496_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*3 + 2);
v_checkDeprecated_497_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*3 + 3);
v_isRecordingDeps_498_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*3 + 4);
v_fileName_499_ = lean_ctor_get(v_toCold_493_, 0);
v_fileMap_500_ = lean_ctor_get(v_toCold_493_, 1);
v_options_501_ = lean_ctor_get(v_toCold_493_, 2);
v_currNamespace_502_ = lean_ctor_get(v_toCold_493_, 4);
v_openDecls_503_ = lean_ctor_get(v_toCold_493_, 5);
v_initHeartbeats_504_ = lean_ctor_get(v_toCold_493_, 6);
v_maxHeartbeats_505_ = lean_ctor_get(v_toCold_493_, 7);
v_quotContext_506_ = lean_ctor_get(v_toCold_493_, 8);
v_currMacroScope_507_ = lean_ctor_get(v_toCold_493_, 9);
v_cancelTk_x3f_508_ = lean_ctor_get(v_toCold_493_, 10);
v_inheritedTraceOptions_509_ = lean_ctor_get(v_toCold_493_, 11);
v_isSharedCheck_771_ = !lean_is_exclusive(v_toCold_493_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_toCold_493_, 3);
lean_dec(v_unused_772_);
v___x_511_ = v_toCold_493_;
v_isShared_512_ = v_isSharedCheck_771_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_inheritedTraceOptions_509_);
lean_inc(v_cancelTk_x3f_508_);
lean_inc(v_currMacroScope_507_);
lean_inc(v_quotContext_506_);
lean_inc(v_maxHeartbeats_505_);
lean_inc(v_initHeartbeats_504_);
lean_inc(v_openDecls_503_);
lean_inc(v_currNamespace_502_);
lean_inc(v_options_501_);
lean_inc(v_fileMap_500_);
lean_inc(v_fileName_499_);
lean_dec(v_toCold_493_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_771_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint8_t v___x_513_; uint8_t v___x_514_; uint16_t v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_585_; uint16_t v___y_586_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_625_; uint16_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; uint8_t v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint16_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; uint16_t v___y_707_; lean_object* v___y_708_; lean_object* v_fileName_709_; lean_object* v_fileMap_710_; lean_object* v_currNamespace_711_; lean_object* v_openDecls_712_; lean_object* v_initHeartbeats_713_; lean_object* v_maxHeartbeats_714_; lean_object* v_quotContext_715_; lean_object* v_currMacroScope_716_; lean_object* v_cancelTk_x3f_717_; lean_object* v_inheritedTraceOptions_718_; lean_object* v_currRecDepth_719_; lean_object* v_ref_720_; uint8_t v_suppressElabErrors_721_; uint8_t v_checkDeprecated_722_; uint8_t v_isRecordingDeps_723_; lean_object* v___y_724_; uint16_t v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_759_; 
v___x_513_ = 1;
v___x_514_ = 0;
if (v_isRecordingDeps_498_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = l_Lean_Elab_async;
v___x_769_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v_options_501_, v___x_768_, v_isRecordingDeps_498_);
v___y_759_ = v___x_769_;
goto v___jp_758_;
}
else
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_501_);
v___y_759_ = v___x_770_;
goto v___jp_758_;
}
v___jp_515_:
{
lean_object* v_toCold_521_; lean_object* v_currRecDepth_522_; lean_object* v_ref_523_; uint8_t v_suppressElabErrors_524_; uint8_t v_checkDeprecated_525_; uint8_t v_isRecordingDeps_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_583_; 
v_toCold_521_ = lean_ctor_get(v___y_519_, 0);
v_currRecDepth_522_ = lean_ctor_get(v___y_519_, 1);
v_ref_523_ = lean_ctor_get(v___y_519_, 2);
v_suppressElabErrors_524_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*3 + 2);
v_checkDeprecated_525_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*3 + 3);
v_isRecordingDeps_526_ = lean_ctor_get_uint8(v___y_519_, sizeof(void*)*3 + 4);
v_isSharedCheck_583_ = !lean_is_exclusive(v___y_519_);
if (v_isSharedCheck_583_ == 0)
{
v___x_528_ = v___y_519_;
v_isShared_529_ = v_isSharedCheck_583_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_ref_523_);
lean_inc(v_currRecDepth_522_);
lean_inc(v_toCold_521_);
lean_dec(v___y_519_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_583_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_fileName_530_; lean_object* v_fileMap_531_; lean_object* v_currNamespace_532_; lean_object* v_openDecls_533_; lean_object* v_initHeartbeats_534_; lean_object* v_maxHeartbeats_535_; lean_object* v_quotContext_536_; lean_object* v_currMacroScope_537_; lean_object* v_cancelTk_x3f_538_; lean_object* v_inheritedTraceOptions_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_580_; 
v_fileName_530_ = lean_ctor_get(v_toCold_521_, 0);
v_fileMap_531_ = lean_ctor_get(v_toCold_521_, 1);
v_currNamespace_532_ = lean_ctor_get(v_toCold_521_, 4);
v_openDecls_533_ = lean_ctor_get(v_toCold_521_, 5);
v_initHeartbeats_534_ = lean_ctor_get(v_toCold_521_, 6);
v_maxHeartbeats_535_ = lean_ctor_get(v_toCold_521_, 7);
v_quotContext_536_ = lean_ctor_get(v_toCold_521_, 8);
v_currMacroScope_537_ = lean_ctor_get(v_toCold_521_, 9);
v_cancelTk_x3f_538_ = lean_ctor_get(v_toCold_521_, 10);
v_inheritedTraceOptions_539_ = lean_ctor_get(v_toCold_521_, 11);
v_isSharedCheck_580_ = !lean_is_exclusive(v_toCold_521_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_581_ = lean_ctor_get(v_toCold_521_, 3);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_toCold_521_, 2);
lean_dec(v_unused_582_);
v___x_541_ = v_toCold_521_;
v_isShared_542_ = v_isSharedCheck_580_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_inheritedTraceOptions_539_);
lean_inc(v_cancelTk_x3f_538_);
lean_inc(v_currMacroScope_537_);
lean_inc(v_quotContext_536_);
lean_inc(v_maxHeartbeats_535_);
lean_inc(v_initHeartbeats_534_);
lean_inc(v_openDecls_533_);
lean_inc(v_currNamespace_532_);
lean_inc(v_fileMap_531_);
lean_inc(v_fileName_530_);
lean_dec(v_toCold_521_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_580_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_517_, v___y_518_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 3, v___x_543_);
lean_ctor_set(v___x_541_, 2, v___y_517_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_fileName_530_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_fileMap_531_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v___y_517_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_currNamespace_532_);
lean_ctor_set(v_reuseFailAlloc_579_, 5, v_openDecls_533_);
lean_ctor_set(v_reuseFailAlloc_579_, 6, v_initHeartbeats_534_);
lean_ctor_set(v_reuseFailAlloc_579_, 7, v_maxHeartbeats_535_);
lean_ctor_set(v_reuseFailAlloc_579_, 8, v_quotContext_536_);
lean_ctor_set(v_reuseFailAlloc_579_, 9, v_currMacroScope_537_);
lean_ctor_set(v_reuseFailAlloc_579_, 10, v_cancelTk_x3f_538_);
lean_ctor_set(v_reuseFailAlloc_579_, 11, v_inheritedTraceOptions_539_);
v___x_545_ = v_reuseFailAlloc_579_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_545_);
v___x_547_ = v___x_528_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_currRecDepth_522_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_ref_523_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*3 + 2, v_suppressElabErrors_524_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*3 + 3, v_checkDeprecated_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*3 + 4, v_isRecordingDeps_526_);
v___x_547_ = v_reuseFailAlloc_578_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; 
lean_ctor_set_uint16(v___x_547_, sizeof(void*)*3, v___y_516_);
v___x_548_ = l_Lean_addAndCompile(v___x_462_, v___x_513_, v___x_514_, v___x_547_, v___y_520_);
lean_dec_ref(v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_dec_ref_known(v___x_548_, 1);
goto v___jp_441_;
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_437_);
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_577_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_577_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_577_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
uint8_t v___x_553_; 
v___x_553_ = l_Lean_Exception_isInterrupt(v_a_549_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
lean_inc(v_a_549_);
v___x_554_ = l_Lean_Exception_isRuntime(v_a_549_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_551_);
v___x_555_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_556_ = l_Lean_MessageData_ofName(v_tacticName_427_);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Exception_toMessageData(v_a_549_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_561_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec_ref(v___y_433_);
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_object* v___x_572_; 
lean_dec_ref(v___y_433_);
lean_dec(v_tacticName_427_);
if (v_isShared_552_ == 0)
{
v___x_572_ = v___x_551_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_549_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
lean_object* v___x_575_; 
lean_dec_ref(v___y_433_);
lean_dec(v_tacticName_427_);
if (v_isShared_552_ == 0)
{
v___x_575_ = v___x_551_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_549_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
}
}
}
v___jp_584_:
{
lean_object* v___x_591_; lean_object* v_env_592_; lean_object* v_nextMacroScope_593_; lean_object* v_ngen_594_; lean_object* v_auxDeclNGen_595_; lean_object* v_traceState_596_; lean_object* v_recordedDeps_597_; lean_object* v_messages_598_; lean_object* v_infoState_599_; lean_object* v_snapshotTasks_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_609_; 
v___x_591_ = lean_st_ref_take(v___y_587_);
v_env_592_ = lean_ctor_get(v___x_591_, 0);
v_nextMacroScope_593_ = lean_ctor_get(v___x_591_, 1);
v_ngen_594_ = lean_ctor_get(v___x_591_, 2);
v_auxDeclNGen_595_ = lean_ctor_get(v___x_591_, 3);
v_traceState_596_ = lean_ctor_get(v___x_591_, 4);
v_recordedDeps_597_ = lean_ctor_get(v___x_591_, 6);
v_messages_598_ = lean_ctor_get(v___x_591_, 7);
v_infoState_599_ = lean_ctor_get(v___x_591_, 8);
v_snapshotTasks_600_ = lean_ctor_get(v___x_591_, 9);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_591_, 5);
lean_dec(v_unused_610_);
v___x_602_ = v___x_591_;
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snapshotTasks_600_);
lean_inc(v_infoState_599_);
lean_inc(v_messages_598_);
lean_inc(v_recordedDeps_597_);
lean_inc(v_traceState_596_);
lean_inc(v_auxDeclNGen_595_);
lean_inc(v_ngen_594_);
lean_inc(v_nextMacroScope_593_);
lean_inc(v_env_592_);
lean_dec(v___x_591_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = l_Lean_Kernel_enableDiag(v_env_592_, v___y_588_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 5, v___x_477_);
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_593_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_594_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_595_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_traceState_596_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_recordedDeps_597_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_messages_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_infoState_599_);
lean_ctor_set(v_reuseFailAlloc_608_, 9, v_snapshotTasks_600_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_st_ref_put(v___y_587_, v___x_606_);
v___y_516_ = v___y_586_;
v___y_517_ = v___y_585_;
v___y_518_ = v___y_589_;
v___y_519_ = v___y_590_;
v___y_520_ = v___y_587_;
goto v___jp_515_;
}
}
}
v___jp_611_:
{
uint16_t v___x_616_; lean_object* v___x_617_; lean_object* v_env_618_; uint8_t v___x_619_; uint16_t v___x_620_; uint16_t v___x_621_; uint16_t v___x_622_; uint8_t v___x_623_; 
v___x_616_ = l_Lean_OptionFlags_ofOptions(v___y_615_);
v___x_617_ = lean_st_ref_get(v___y_612_);
v_env_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc_ref(v_env_618_);
lean_dec(v___x_617_);
v___x_619_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_618_);
lean_dec_ref(v_env_618_);
v___x_620_ = 512;
v___x_621_ = lean_uint16_land(v___x_616_, v___x_620_);
v___x_622_ = 0;
v___x_623_ = lean_uint16_dec_eq(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
if (v___x_619_ == 0)
{
v___y_585_ = v___y_615_;
v___y_586_ = v___x_616_;
v___y_587_ = v___y_612_;
v___y_588_ = v___x_513_;
v___y_589_ = v___y_613_;
v___y_590_ = v___y_614_;
goto v___jp_584_;
}
else
{
v___y_516_ = v___x_616_;
v___y_517_ = v___y_615_;
v___y_518_ = v___y_613_;
v___y_519_ = v___y_614_;
v___y_520_ = v___y_612_;
goto v___jp_515_;
}
}
else
{
if (v___x_619_ == 0)
{
v___y_516_ = v___x_616_;
v___y_517_ = v___y_615_;
v___y_518_ = v___y_613_;
v___y_519_ = v___y_614_;
v___y_520_ = v___y_612_;
goto v___jp_515_;
}
else
{
v___y_585_ = v___y_615_;
v___y_586_ = v___x_616_;
v___y_587_ = v___y_612_;
v___y_588_ = v___x_514_;
v___y_589_ = v___y_613_;
v___y_590_ = v___y_614_;
goto v___jp_584_;
}
}
}
v___jp_624_:
{
lean_object* v_toCold_630_; lean_object* v_currRecDepth_631_; lean_object* v_ref_632_; uint8_t v_suppressElabErrors_633_; uint8_t v_checkDeprecated_634_; uint8_t v_isRecordingDeps_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_665_; 
v_toCold_630_ = lean_ctor_get(v___y_628_, 0);
v_currRecDepth_631_ = lean_ctor_get(v___y_628_, 1);
v_ref_632_ = lean_ctor_get(v___y_628_, 2);
v_suppressElabErrors_633_ = lean_ctor_get_uint8(v___y_628_, sizeof(void*)*3 + 2);
v_checkDeprecated_634_ = lean_ctor_get_uint8(v___y_628_, sizeof(void*)*3 + 3);
v_isRecordingDeps_635_ = lean_ctor_get_uint8(v___y_628_, sizeof(void*)*3 + 4);
v_isSharedCheck_665_ = !lean_is_exclusive(v___y_628_);
if (v_isSharedCheck_665_ == 0)
{
v___x_637_ = v___y_628_;
v_isShared_638_ = v_isSharedCheck_665_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_ref_632_);
lean_inc(v_currRecDepth_631_);
lean_inc(v_toCold_630_);
lean_dec(v___y_628_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_665_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_fileName_639_; lean_object* v_fileMap_640_; lean_object* v_currNamespace_641_; lean_object* v_openDecls_642_; lean_object* v_initHeartbeats_643_; lean_object* v_maxHeartbeats_644_; lean_object* v_quotContext_645_; lean_object* v_currMacroScope_646_; lean_object* v_cancelTk_x3f_647_; lean_object* v_inheritedTraceOptions_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_662_; 
v_fileName_639_ = lean_ctor_get(v_toCold_630_, 0);
v_fileMap_640_ = lean_ctor_get(v_toCold_630_, 1);
v_currNamespace_641_ = lean_ctor_get(v_toCold_630_, 4);
v_openDecls_642_ = lean_ctor_get(v_toCold_630_, 5);
v_initHeartbeats_643_ = lean_ctor_get(v_toCold_630_, 6);
v_maxHeartbeats_644_ = lean_ctor_get(v_toCold_630_, 7);
v_quotContext_645_ = lean_ctor_get(v_toCold_630_, 8);
v_currMacroScope_646_ = lean_ctor_get(v_toCold_630_, 9);
v_cancelTk_x3f_647_ = lean_ctor_get(v_toCold_630_, 10);
v_inheritedTraceOptions_648_ = lean_ctor_get(v_toCold_630_, 11);
v_isSharedCheck_662_ = !lean_is_exclusive(v_toCold_630_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; lean_object* v_unused_664_; 
v_unused_663_ = lean_ctor_get(v_toCold_630_, 3);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v_toCold_630_, 2);
lean_dec(v_unused_664_);
v___x_650_ = v_toCold_630_;
v_isShared_651_ = v_isSharedCheck_662_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_inheritedTraceOptions_648_);
lean_inc(v_cancelTk_x3f_647_);
lean_inc(v_currMacroScope_646_);
lean_inc(v_quotContext_645_);
lean_inc(v_maxHeartbeats_644_);
lean_inc(v_initHeartbeats_643_);
lean_inc(v_openDecls_642_);
lean_inc(v_currNamespace_641_);
lean_inc(v_fileMap_640_);
lean_inc(v_fileName_639_);
lean_dec(v_toCold_630_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_662_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_625_, v___y_627_);
lean_inc_ref(v___y_625_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 3, v___x_652_);
lean_ctor_set(v___x_650_, 2, v___y_625_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_fileName_639_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_fileMap_640_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v___y_625_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_currNamespace_641_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v_openDecls_642_);
lean_ctor_set(v_reuseFailAlloc_661_, 6, v_initHeartbeats_643_);
lean_ctor_set(v_reuseFailAlloc_661_, 7, v_maxHeartbeats_644_);
lean_ctor_set(v_reuseFailAlloc_661_, 8, v_quotContext_645_);
lean_ctor_set(v_reuseFailAlloc_661_, 9, v_currMacroScope_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 10, v_cancelTk_x3f_647_);
lean_ctor_set(v_reuseFailAlloc_661_, 11, v_inheritedTraceOptions_648_);
v___x_654_ = v_reuseFailAlloc_661_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_654_);
v___x_656_ = v___x_637_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_currRecDepth_631_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_ref_632_);
lean_ctor_set_uint8(v_reuseFailAlloc_660_, sizeof(void*)*3 + 2, v_suppressElabErrors_633_);
lean_ctor_set_uint8(v_reuseFailAlloc_660_, sizeof(void*)*3 + 3, v_checkDeprecated_634_);
lean_ctor_set_uint8(v_reuseFailAlloc_660_, sizeof(void*)*3 + 4, v_isRecordingDeps_635_);
v___x_656_ = v_reuseFailAlloc_660_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_ctor_set_uint16(v___x_656_, sizeof(void*)*3, v___y_626_);
if (v_isRecordingDeps_635_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_658_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_625_, v___x_657_, v___x_513_);
v___y_612_ = v___y_629_;
v___y_613_ = v___y_627_;
v___y_614_ = v___x_656_;
v___y_615_ = v___x_658_;
goto v___jp_611_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_625_);
v___y_612_ = v___y_629_;
v___y_613_ = v___y_627_;
v___y_614_ = v___x_656_;
v___y_615_ = v___x_659_;
goto v___jp_611_;
}
}
}
}
}
}
v___jp_666_:
{
lean_object* v___x_673_; lean_object* v_env_674_; lean_object* v_nextMacroScope_675_; lean_object* v_ngen_676_; lean_object* v_auxDeclNGen_677_; lean_object* v_traceState_678_; lean_object* v_recordedDeps_679_; lean_object* v_messages_680_; lean_object* v_infoState_681_; lean_object* v_snapshotTasks_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_691_; 
v___x_673_ = lean_st_ref_take(v___y_668_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
v_nextMacroScope_675_ = lean_ctor_get(v___x_673_, 1);
v_ngen_676_ = lean_ctor_get(v___x_673_, 2);
v_auxDeclNGen_677_ = lean_ctor_get(v___x_673_, 3);
v_traceState_678_ = lean_ctor_get(v___x_673_, 4);
v_recordedDeps_679_ = lean_ctor_get(v___x_673_, 6);
v_messages_680_ = lean_ctor_get(v___x_673_, 7);
v_infoState_681_ = lean_ctor_get(v___x_673_, 8);
v_snapshotTasks_682_ = lean_ctor_get(v___x_673_, 9);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_673_, 5);
lean_dec(v_unused_692_);
v___x_684_ = v___x_673_;
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snapshotTasks_682_);
lean_inc(v_infoState_681_);
lean_inc(v_messages_680_);
lean_inc(v_recordedDeps_679_);
lean_inc(v_traceState_678_);
lean_inc(v_auxDeclNGen_677_);
lean_inc(v_ngen_676_);
lean_inc(v_nextMacroScope_675_);
lean_inc(v_env_674_);
lean_dec(v___x_673_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = l_Lean_Kernel_enableDiag(v_env_674_, v___y_667_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 5, v___x_477_);
lean_ctor_set(v___x_684_, 0, v___x_686_);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_nextMacroScope_675_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_ngen_676_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_auxDeclNGen_677_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_traceState_678_);
lean_ctor_set(v_reuseFailAlloc_690_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_690_, 6, v_recordedDeps_679_);
lean_ctor_set(v_reuseFailAlloc_690_, 7, v_messages_680_);
lean_ctor_set(v_reuseFailAlloc_690_, 8, v_infoState_681_);
lean_ctor_set(v_reuseFailAlloc_690_, 9, v_snapshotTasks_682_);
v___x_688_ = v_reuseFailAlloc_690_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; 
v___x_689_ = lean_st_ref_put(v___y_668_, v___x_688_);
v___y_625_ = v___y_669_;
v___y_626_ = v___y_671_;
v___y_627_ = v___y_670_;
v___y_628_ = v___y_672_;
v___y_629_ = v___y_668_;
goto v___jp_624_;
}
}
}
v___jp_693_:
{
uint16_t v___x_698_; lean_object* v___x_699_; lean_object* v_env_700_; uint8_t v___x_701_; uint16_t v___x_702_; uint16_t v___x_703_; uint16_t v___x_704_; uint8_t v___x_705_; 
v___x_698_ = l_Lean_OptionFlags_ofOptions(v___y_697_);
v___x_699_ = lean_st_ref_get(v___y_694_);
v_env_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_700_);
lean_dec(v___x_699_);
v___x_701_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_700_);
lean_dec_ref(v_env_700_);
v___x_702_ = 512;
v___x_703_ = lean_uint16_land(v___x_698_, v___x_702_);
v___x_704_ = 0;
v___x_705_ = lean_uint16_dec_eq(v___x_703_, v___x_704_);
if (v___x_705_ == 0)
{
if (v___x_701_ == 0)
{
v___y_667_ = v___x_513_;
v___y_668_ = v___y_694_;
v___y_669_ = v___y_697_;
v___y_670_ = v___y_695_;
v___y_671_ = v___x_698_;
v___y_672_ = v___y_696_;
goto v___jp_666_;
}
else
{
v___y_625_ = v___y_697_;
v___y_626_ = v___x_698_;
v___y_627_ = v___y_695_;
v___y_628_ = v___y_696_;
v___y_629_ = v___y_694_;
goto v___jp_624_;
}
}
else
{
if (v___x_701_ == 0)
{
v___y_625_ = v___y_697_;
v___y_626_ = v___x_698_;
v___y_627_ = v___y_695_;
v___y_628_ = v___y_696_;
v___y_629_ = v___y_694_;
goto v___jp_624_;
}
else
{
v___y_667_ = v___x_514_;
v___y_668_ = v___y_694_;
v___y_669_ = v___y_697_;
v___y_670_ = v___y_695_;
v___y_671_ = v___x_698_;
v___y_672_ = v___y_696_;
goto v___jp_666_;
}
}
}
v___jp_706_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = l_Lean_maxRecDepth;
v___x_726_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_708_, v___x_725_);
lean_inc_ref(v___y_708_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 11, v_inheritedTraceOptions_718_);
lean_ctor_set(v___x_511_, 10, v_cancelTk_x3f_717_);
lean_ctor_set(v___x_511_, 9, v_currMacroScope_716_);
lean_ctor_set(v___x_511_, 8, v_quotContext_715_);
lean_ctor_set(v___x_511_, 7, v_maxHeartbeats_714_);
lean_ctor_set(v___x_511_, 6, v_initHeartbeats_713_);
lean_ctor_set(v___x_511_, 5, v_openDecls_712_);
lean_ctor_set(v___x_511_, 4, v_currNamespace_711_);
lean_ctor_set(v___x_511_, 3, v___x_726_);
lean_ctor_set(v___x_511_, 2, v___y_708_);
lean_ctor_set(v___x_511_, 1, v_fileMap_710_);
lean_ctor_set(v___x_511_, 0, v_fileName_709_);
v___x_728_ = v___x_511_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_fileName_709_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_fileMap_710_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v___y_708_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_currNamespace_711_);
lean_ctor_set(v_reuseFailAlloc_733_, 5, v_openDecls_712_);
lean_ctor_set(v_reuseFailAlloc_733_, 6, v_initHeartbeats_713_);
lean_ctor_set(v_reuseFailAlloc_733_, 7, v_maxHeartbeats_714_);
lean_ctor_set(v_reuseFailAlloc_733_, 8, v_quotContext_715_);
lean_ctor_set(v_reuseFailAlloc_733_, 9, v_currMacroScope_716_);
lean_ctor_set(v_reuseFailAlloc_733_, 10, v_cancelTk_x3f_717_);
lean_ctor_set(v_reuseFailAlloc_733_, 11, v_inheritedTraceOptions_718_);
v___x_728_ = v_reuseFailAlloc_733_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_currRecDepth_719_);
lean_ctor_set(v___x_729_, 2, v_ref_720_);
lean_ctor_set_uint16(v___x_729_, sizeof(void*)*3, v___y_707_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*3 + 2, v_suppressElabErrors_721_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*3 + 3, v_checkDeprecated_722_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*3 + 4, v_isRecordingDeps_723_);
if (v_isRecordingDeps_723_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_731_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_708_, v___x_730_, v_isRecordingDeps_723_);
v___y_694_ = v___y_724_;
v___y_695_ = v___x_725_;
v___y_696_ = v___x_729_;
v___y_697_ = v___x_731_;
goto v___jp_693_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_708_);
v___y_694_ = v___y_724_;
v___y_695_ = v___x_725_;
v___y_696_ = v___x_729_;
v___y_697_ = v___x_732_;
goto v___jp_693_;
}
}
}
v___jp_734_:
{
lean_object* v___x_738_; lean_object* v_env_739_; lean_object* v_nextMacroScope_740_; lean_object* v_ngen_741_; lean_object* v_auxDeclNGen_742_; lean_object* v_traceState_743_; lean_object* v_recordedDeps_744_; lean_object* v_messages_745_; lean_object* v_infoState_746_; lean_object* v_snapshotTasks_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_756_; 
v___x_738_ = lean_st_ref_take(v___y_434_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
v_nextMacroScope_740_ = lean_ctor_get(v___x_738_, 1);
v_ngen_741_ = lean_ctor_get(v___x_738_, 2);
v_auxDeclNGen_742_ = lean_ctor_get(v___x_738_, 3);
v_traceState_743_ = lean_ctor_get(v___x_738_, 4);
v_recordedDeps_744_ = lean_ctor_get(v___x_738_, 6);
v_messages_745_ = lean_ctor_get(v___x_738_, 7);
v_infoState_746_ = lean_ctor_get(v___x_738_, 8);
v_snapshotTasks_747_ = lean_ctor_get(v___x_738_, 9);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v___x_738_, 5);
lean_dec(v_unused_757_);
v___x_749_ = v___x_738_;
v_isShared_750_ = v_isSharedCheck_756_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_snapshotTasks_747_);
lean_inc(v_infoState_746_);
lean_inc(v_messages_745_);
lean_inc(v_recordedDeps_744_);
lean_inc(v_traceState_743_);
lean_inc(v_auxDeclNGen_742_);
lean_inc(v_ngen_741_);
lean_inc(v_nextMacroScope_740_);
lean_inc(v_env_739_);
lean_dec(v___x_738_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_756_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = l_Lean_Kernel_enableDiag(v_env_739_, v___y_737_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 5, v___x_477_);
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_nextMacroScope_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_ngen_741_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_auxDeclNGen_742_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_traceState_743_);
lean_ctor_set(v_reuseFailAlloc_755_, 5, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_755_, 6, v_recordedDeps_744_);
lean_ctor_set(v_reuseFailAlloc_755_, 7, v_messages_745_);
lean_ctor_set(v_reuseFailAlloc_755_, 8, v_infoState_746_);
lean_ctor_set(v_reuseFailAlloc_755_, 9, v_snapshotTasks_747_);
v___x_753_ = v_reuseFailAlloc_755_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; 
v___x_754_ = lean_st_ref_put(v___y_434_, v___x_753_);
lean_inc(v_ref_495_);
lean_inc(v_currRecDepth_494_);
v___y_707_ = v___y_735_;
v___y_708_ = v___y_736_;
v_fileName_709_ = v_fileName_499_;
v_fileMap_710_ = v_fileMap_500_;
v_currNamespace_711_ = v_currNamespace_502_;
v_openDecls_712_ = v_openDecls_503_;
v_initHeartbeats_713_ = v_initHeartbeats_504_;
v_maxHeartbeats_714_ = v_maxHeartbeats_505_;
v_quotContext_715_ = v_quotContext_506_;
v_currMacroScope_716_ = v_currMacroScope_507_;
v_cancelTk_x3f_717_ = v_cancelTk_x3f_508_;
v_inheritedTraceOptions_718_ = v_inheritedTraceOptions_509_;
v_currRecDepth_719_ = v_currRecDepth_494_;
v_ref_720_ = v_ref_495_;
v_suppressElabErrors_721_ = v_suppressElabErrors_496_;
v_checkDeprecated_722_ = v_checkDeprecated_497_;
v_isRecordingDeps_723_ = v_isRecordingDeps_498_;
v___y_724_ = v___y_434_;
goto v___jp_706_;
}
}
}
v___jp_758_:
{
uint16_t v___x_760_; lean_object* v___x_761_; lean_object* v_env_762_; uint8_t v___x_763_; uint16_t v___x_764_; uint16_t v___x_765_; uint16_t v___x_766_; uint8_t v___x_767_; 
v___x_760_ = l_Lean_OptionFlags_ofOptions(v___y_759_);
v___x_761_ = lean_st_ref_get(v___y_434_);
v_env_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_env_762_);
lean_dec(v___x_761_);
v___x_763_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_762_);
lean_dec_ref(v_env_762_);
v___x_764_ = 512;
v___x_765_ = lean_uint16_land(v___x_760_, v___x_764_);
v___x_766_ = 0;
v___x_767_ = lean_uint16_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
if (v___x_763_ == 0)
{
v___y_735_ = v___x_760_;
v___y_736_ = v___y_759_;
v___y_737_ = v___x_513_;
goto v___jp_734_;
}
else
{
lean_inc(v_ref_495_);
lean_inc(v_currRecDepth_494_);
v___y_707_ = v___x_760_;
v___y_708_ = v___y_759_;
v_fileName_709_ = v_fileName_499_;
v_fileMap_710_ = v_fileMap_500_;
v_currNamespace_711_ = v_currNamespace_502_;
v_openDecls_712_ = v_openDecls_503_;
v_initHeartbeats_713_ = v_initHeartbeats_504_;
v_maxHeartbeats_714_ = v_maxHeartbeats_505_;
v_quotContext_715_ = v_quotContext_506_;
v_currMacroScope_716_ = v_currMacroScope_507_;
v_cancelTk_x3f_717_ = v_cancelTk_x3f_508_;
v_inheritedTraceOptions_718_ = v_inheritedTraceOptions_509_;
v_currRecDepth_719_ = v_currRecDepth_494_;
v_ref_720_ = v_ref_495_;
v_suppressElabErrors_721_ = v_suppressElabErrors_496_;
v_checkDeprecated_722_ = v_checkDeprecated_497_;
v_isRecordingDeps_723_ = v_isRecordingDeps_498_;
v___y_724_ = v___y_434_;
goto v___jp_706_;
}
}
else
{
if (v___x_763_ == 0)
{
lean_inc(v_ref_495_);
lean_inc(v_currRecDepth_494_);
v___y_707_ = v___x_760_;
v___y_708_ = v___y_759_;
v_fileName_709_ = v_fileName_499_;
v_fileMap_710_ = v_fileMap_500_;
v_currNamespace_711_ = v_currNamespace_502_;
v_openDecls_712_ = v_openDecls_503_;
v_initHeartbeats_713_ = v_initHeartbeats_504_;
v_maxHeartbeats_714_ = v_maxHeartbeats_505_;
v_quotContext_715_ = v_quotContext_506_;
v_currMacroScope_716_ = v_currMacroScope_507_;
v_cancelTk_x3f_717_ = v_cancelTk_x3f_508_;
v_inheritedTraceOptions_718_ = v_inheritedTraceOptions_509_;
v_currRecDepth_719_ = v_currRecDepth_494_;
v_ref_720_ = v_ref_495_;
v_suppressElabErrors_721_ = v_suppressElabErrors_496_;
v_checkDeprecated_722_ = v_checkDeprecated_497_;
v_isRecordingDeps_723_ = v_isRecordingDeps_498_;
v___y_724_ = v___y_434_;
goto v___jp_706_;
}
else
{
v___y_735_ = v___x_760_;
v___y_736_ = v___y_759_;
v___y_737_ = v___x_514_;
goto v___jp_734_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_781_, lean_object* v_tacticName_782_, lean_object* v___x_783_, lean_object* v___x_784_, lean_object* v_a_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_781_, v_tacticName_782_, v___x_783_, v___x_784_, v_a_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(lean_object* v_env_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v_nextMacroScope_797_; lean_object* v_ngen_798_; lean_object* v_auxDeclNGen_799_; lean_object* v_traceState_800_; lean_object* v_recordedDeps_801_; lean_object* v_messages_802_; lean_object* v_infoState_803_; lean_object* v_snapshotTasks_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_830_; 
v___x_796_ = lean_st_ref_take(v___y_794_);
v_nextMacroScope_797_ = lean_ctor_get(v___x_796_, 1);
v_ngen_798_ = lean_ctor_get(v___x_796_, 2);
v_auxDeclNGen_799_ = lean_ctor_get(v___x_796_, 3);
v_traceState_800_ = lean_ctor_get(v___x_796_, 4);
v_recordedDeps_801_ = lean_ctor_get(v___x_796_, 6);
v_messages_802_ = lean_ctor_get(v___x_796_, 7);
v_infoState_803_ = lean_ctor_get(v___x_796_, 8);
v_snapshotTasks_804_ = lean_ctor_get(v___x_796_, 9);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; 
v_unused_831_ = lean_ctor_get(v___x_796_, 5);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v___x_796_, 0);
lean_dec(v_unused_832_);
v___x_806_ = v___x_796_;
v_isShared_807_ = v_isSharedCheck_830_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snapshotTasks_804_);
lean_inc(v_infoState_803_);
lean_inc(v_messages_802_);
lean_inc(v_recordedDeps_801_);
lean_inc(v_traceState_800_);
lean_inc(v_auxDeclNGen_799_);
lean_inc(v_ngen_798_);
lean_inc(v_nextMacroScope_797_);
lean_dec(v___x_796_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_830_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 5, v___x_808_);
lean_ctor_set(v___x_806_, 0, v_env_792_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_env_792_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_nextMacroScope_797_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_ngen_798_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_auxDeclNGen_799_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v_traceState_800_);
lean_ctor_set(v_reuseFailAlloc_829_, 5, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_829_, 6, v_recordedDeps_801_);
lean_ctor_set(v_reuseFailAlloc_829_, 7, v_messages_802_);
lean_ctor_set(v_reuseFailAlloc_829_, 8, v_infoState_803_);
lean_ctor_set(v_reuseFailAlloc_829_, 9, v_snapshotTasks_804_);
v___x_810_ = v_reuseFailAlloc_829_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_mctx_813_; lean_object* v_zetaDeltaFVarIds_814_; lean_object* v_postponed_815_; lean_object* v_diag_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_827_; 
v___x_811_ = lean_st_ref_put(v___y_794_, v___x_810_);
v___x_812_ = lean_st_ref_take(v___y_793_);
v_mctx_813_ = lean_ctor_get(v___x_812_, 0);
v_zetaDeltaFVarIds_814_ = lean_ctor_get(v___x_812_, 2);
v_postponed_815_ = lean_ctor_get(v___x_812_, 3);
v_diag_816_ = lean_ctor_get(v___x_812_, 4);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_812_, 1);
lean_dec(v_unused_828_);
v___x_818_ = v___x_812_;
v_isShared_819_ = v_isSharedCheck_827_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_diag_816_);
lean_inc(v_postponed_815_);
lean_inc(v_zetaDeltaFVarIds_814_);
lean_inc(v_mctx_813_);
lean_dec(v___x_812_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_827_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_820_ = lean_box(0);
v___x_821_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v___x_821_);
v___x_823_ = v___x_818_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_mctx_813_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_zetaDeltaFVarIds_814_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v_postponed_815_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v_diag_816_);
v___x_823_ = v_reuseFailAlloc_826_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_st_ref_put(v___y_793_, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_820_);
return v___x_825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg___boxed(lean_object* v_env_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec(v___y_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(lean_object* v_env_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_env_846_; lean_object* v_a_848_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_845_ = lean_st_ref_get(v___y_843_);
v_env_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_env_846_);
lean_dec(v___x_845_);
v___x_858_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_838_, v___y_841_, v___y_843_);
lean_dec_ref(v___x_858_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
v___x_859_ = lean_apply_5(v_x_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, lean_box(0));
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_846_, v___y_841_, v___y_843_);
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
lean_ctor_set(v___x_863_, 0, v_a_860_);
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_860_);
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
lean_object* v_a_870_; 
v_a_870_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_859_, 1);
v_a_848_ = v_a_870_;
goto v___jp_847_;
}
v___jp_847_:
{
lean_object* v___x_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v___x_849_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_846_, v___y_841_, v___y_843_);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v___x_849_, 0);
lean_dec(v_unused_857_);
v___x_851_ = v___x_849_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_dec(v___x_849_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 1);
lean_ctor_set(v___x_851_, 0, v_a_848_);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_848_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg___boxed(lean_object* v_env_871_, lean_object* v_x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_871_, v_x_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(lean_object* v_stx_879_, lean_object* v___y_880_){
_start:
{
uint8_t v___x_882_; lean_object* v___x_883_; 
v___x_882_ = 0;
v___x_883_ = l_Lean_Syntax_getRange_x3f(v_stx_879_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 1)
{
lean_object* v_toCold_884_; lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
v_toCold_884_ = lean_ctor_get(v___y_880_, 0);
v_val_885_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v___x_883_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v___x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_fileMap_889_; lean_object* v_start_890_; lean_object* v_stop_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v_fileMap_889_ = lean_ctor_get(v_toCold_884_, 1);
v_start_890_ = lean_ctor_get(v_val_885_, 0);
lean_inc(v_start_890_);
v_stop_891_ = lean_ctor_get(v_val_885_, 1);
lean_inc(v_stop_891_);
lean_dec(v_val_885_);
lean_inc_ref(v_fileMap_889_);
v___x_892_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_889_, v_start_890_, v_stop_891_);
lean_dec(v_stop_891_);
lean_dec(v_start_890_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_892_);
v___x_894_ = v___x_887_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v___x_883_);
v___x_898_ = lean_box(0);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg___boxed(lean_object* v_stx_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_900_, v___y_901_);
lean_dec_ref(v___y_901_);
lean_dec(v_stx_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(lean_object* v_declName_904_, lean_object* v_declRanges_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = l_Lean_Name_isAnonymous(v_declName_904_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v_env_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_910_ = lean_st_ref_get(v___y_907_);
v_env_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc_ref(v_env_911_);
lean_dec(v___x_910_);
v___x_912_ = l_Lean_declRangeExt;
v___x_913_ = lean_box(1);
lean_inc(v_declName_904_);
v___x_914_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_912_, v_env_911_, v_declName_904_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v_env_916_; lean_object* v_nextMacroScope_917_; lean_object* v_ngen_918_; lean_object* v_auxDeclNGen_919_; lean_object* v_traceState_920_; lean_object* v_recordedDeps_921_; lean_object* v_messages_922_; lean_object* v_infoState_923_; lean_object* v_snapshotTasks_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_951_; 
v___x_915_ = lean_st_ref_take(v___y_907_);
v_env_916_ = lean_ctor_get(v___x_915_, 0);
v_nextMacroScope_917_ = lean_ctor_get(v___x_915_, 1);
v_ngen_918_ = lean_ctor_get(v___x_915_, 2);
v_auxDeclNGen_919_ = lean_ctor_get(v___x_915_, 3);
v_traceState_920_ = lean_ctor_get(v___x_915_, 4);
v_recordedDeps_921_ = lean_ctor_get(v___x_915_, 6);
v_messages_922_ = lean_ctor_get(v___x_915_, 7);
v_infoState_923_ = lean_ctor_get(v___x_915_, 8);
v_snapshotTasks_924_ = lean_ctor_get(v___x_915_, 9);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_915_, 5);
lean_dec(v_unused_952_);
v___x_926_ = v___x_915_;
v_isShared_927_ = v_isSharedCheck_951_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snapshotTasks_924_);
lean_inc(v_infoState_923_);
lean_inc(v_messages_922_);
lean_inc(v_recordedDeps_921_);
lean_inc(v_traceState_920_);
lean_inc(v_auxDeclNGen_919_);
lean_inc(v_ngen_918_);
lean_inc(v_nextMacroScope_917_);
lean_inc(v_env_916_);
lean_dec(v___x_915_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_951_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_928_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_912_, v_env_916_, v_declName_904_, v_declRanges_905_, v___x_914_);
v___x_929_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 5, v___x_929_);
lean_ctor_set(v___x_926_, 0, v___x_928_);
v___x_931_ = v___x_926_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_nextMacroScope_917_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_ngen_918_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_auxDeclNGen_919_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_traceState_920_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_recordedDeps_921_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_messages_922_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v_infoState_923_);
lean_ctor_set(v_reuseFailAlloc_950_, 9, v_snapshotTasks_924_);
v___x_931_ = v_reuseFailAlloc_950_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_mctx_934_; lean_object* v_zetaDeltaFVarIds_935_; lean_object* v_postponed_936_; lean_object* v_diag_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
v___x_932_ = lean_st_ref_put(v___y_907_, v___x_931_);
v___x_933_ = lean_st_ref_take(v___y_906_);
v_mctx_934_ = lean_ctor_get(v___x_933_, 0);
v_zetaDeltaFVarIds_935_ = lean_ctor_get(v___x_933_, 2);
v_postponed_936_ = lean_ctor_get(v___x_933_, 3);
v_diag_937_ = lean_ctor_get(v___x_933_, 4);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_933_, 1);
lean_dec(v_unused_949_);
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_diag_937_);
lean_inc(v_postponed_936_);
lean_inc(v_zetaDeltaFVarIds_935_);
lean_inc(v_mctx_934_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_mctx_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_zetaDeltaFVarIds_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_postponed_936_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_diag_937_);
v___x_944_ = v_reuseFailAlloc_947_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_st_ref_put(v___y_906_, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_941_);
return v___x_946_;
}
}
}
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec_ref(v_declRanges_905_);
lean_dec(v_declName_904_);
v___x_953_ = lean_box(0);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec_ref(v_declRanges_905_);
lean_dec(v_declName_904_);
v___x_955_ = lean_box(0);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg___boxed(lean_object* v_declName_957_, lean_object* v_declRanges_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_957_, v_declRanges_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec(v___y_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_declName_963_, lean_object* v_rangeStx_964_, lean_object* v_selectionRangeStx_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_988_; 
v___x_971_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_rangeStx_964_, v___y_968_);
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_988_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
if (lean_obj_tag(v_a_972_) == 1)
{
lean_object* v_val_976_; lean_object* v_a_978_; lean_object* v___x_981_; lean_object* v_a_982_; 
lean_del_object(v___x_974_);
v_val_976_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v_a_972_, 1);
v___x_981_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_selectionRangeStx_965_, v___y_968_);
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
if (lean_obj_tag(v_a_982_) == 0)
{
lean_inc(v_val_976_);
v_a_978_ = v_val_976_;
goto v___jp_977_;
}
else
{
lean_object* v_val_983_; 
v_val_983_ = lean_ctor_get(v_a_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v_a_982_, 1);
v_a_978_ = v_val_983_;
goto v___jp_977_;
}
v___jp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_val_976_);
lean_ctor_set(v___x_979_, 1, v_a_978_);
v___x_980_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_963_, v___x_979_, v___y_967_, v___y_969_);
return v___x_980_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_dec(v_a_972_);
lean_dec(v_declName_963_);
v___x_984_ = lean_box(0);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_984_);
v___x_986_ = v___x_974_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8___boxed(lean_object* v_declName_989_, lean_object* v_rangeStx_990_, lean_object* v_selectionRangeStx_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_declName_989_, v_rangeStx_990_, v_selectionRangeStx_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v_selectionRangeStx_991_);
lean_dec(v_rangeStx_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
if (lean_obj_tag(v_a_998_) == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = l_List_reverse___redArg(v_a_999_);
return v___x_1000_;
}
else
{
lean_object* v_head_1001_; lean_object* v_tail_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1011_; 
v_head_1001_ = lean_ctor_get(v_a_998_, 0);
v_tail_1002_ = lean_ctor_get(v_a_998_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1004_ = v_a_998_;
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_tail_1002_);
lean_inc(v_head_1001_);
lean_dec(v_a_998_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = l_Lean_mkLevelParam(v_head_1001_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v_a_999_);
lean_ctor_set(v___x_1004_, 0, v___x_1006_);
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_a_999_);
v___x_1008_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
v_a_998_ = v_tail_1002_;
v_a_999_ = v___x_1008_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_unsigned_to_nat(16u);
v___x_1014_ = lean_mk_array(v___x_1013_, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1015_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_1021_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_1022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
lean_ctor_set(v___x_1022_, 2, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = l_Lean_Level_ofNat(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_1037_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_1041_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_1042_ = l_Lean_mkConst(v___x_1041_, v___x_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__5));
v___x_1045_ = l_Lean_mkConst(v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_1052_ = l_Lean_mkConst(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_1059_, lean_object* v_e_1060_, lean_object* v_axiomDeclRange_x3f_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___x_1075_; lean_object* v_a_1076_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; uint8_t v___x_1182_; 
v___x_1075_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_1060_, v_a_1063_);
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v___x_1182_ = l_Lean_Expr_hasFVar(v_a_1076_);
if (v___x_1182_ == 0)
{
v___y_1161_ = v_a_1062_;
v___y_1162_ = v_a_1063_;
v___y_1163_ = v_a_1064_;
v___y_1164_ = v_a_1065_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v___x_1183_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1184_ = l_Lean_MessageData_ofName(v_tacticName_1059_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_indentExpr(v_a_1076_);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1189_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
v___jp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(v___y_1069_, v___x_1070_);
v___x_1072_ = l_Lean_mkConst(v___y_1068_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
v___jp_1077_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_params_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1157_; 
v___x_1082_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1076_);
v___x_1083_ = l_Lean_collectLevelParams(v___x_1082_, v_a_1076_);
v_params_1084_ = lean_ctor_get(v___x_1083_, 2);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1158_ = lean_ctor_get(v___x_1083_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v___x_1083_, 0);
lean_dec(v_unused_1159_);
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1157_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_params_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1157_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v_env_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_array_to_list(v_params_1084_);
v___x_1090_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_1059_);
v___x_1091_ = l_Lean_Name_append(v___x_1090_, v_tacticName_1059_);
v___x_1092_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1091_);
v___x_1093_ = l_Lean_Name_append(v___x_1091_, v___x_1092_);
lean_inc(v_a_1076_);
lean_inc(v___x_1089_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1094_, 0, v___x_1093_);
lean_closure_set(v___f_1094_, 1, v_tacticName_1059_);
lean_closure_set(v___f_1094_, 2, v___x_1089_);
lean_closure_set(v___f_1094_, 3, v___x_1088_);
lean_closure_set(v___f_1094_, 4, v_a_1076_);
v___x_1095_ = lean_st_ref_get(v___y_1081_);
v_env_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_env_1096_);
lean_dec(v___x_1095_);
v___x_1097_ = l_Lean_Environment_unlockAsync(v_env_1096_);
v___x_1098_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v___x_1097_, v___f_1094_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1148_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1148_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1148_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_unbox(v_a_1099_);
lean_dec(v_a_1099_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v___x_1091_);
lean_dec(v___x_1089_);
lean_del_object(v___x_1086_);
lean_dec(v_a_1076_);
v___x_1104_ = lean_box(1);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1101_);
v___x_1108_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1109_ = l_Lean_Name_append(v___x_1091_, v___x_1108_);
v___x_1110_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1109_, v___y_1081_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1147_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1147_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1115_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1116_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1117_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1118_ = l_Lean_mkApp3(v___x_1115_, v___x_1116_, v_a_1076_, v___x_1117_);
lean_inc(v___x_1089_);
lean_inc(v_a_1111_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 2, v___x_1118_);
lean_ctor_set(v___x_1086_, 1, v___x_1089_);
lean_ctor_set(v___x_1086_, 0, v_a_1111_);
v___x_1120_ = v___x_1086_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1111_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1121_ = 0;
v___x_1122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*1, v___x_1121_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1122_);
v___x_1124_ = v___x_1113_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_addDecl(v___x_1124_, v___x_1121_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_dec_ref_known(v___x_1125_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1061_) == 1)
{
lean_object* v_val_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_val_1126_ = lean_ctor_get(v_axiomDeclRange_x3f_1061_, 0);
v___x_1127_ = lean_box(0);
lean_inc(v_a_1111_);
v___x_1128_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_a_1111_, v_val_1126_, v___x_1127_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_dec_ref_known(v___x_1128_, 1);
v___y_1068_ = v_a_1111_;
v___y_1069_ = v___x_1089_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_a_1111_);
lean_dec(v___x_1089_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
v___y_1068_ = v_a_1111_;
v___y_1069_ = v___x_1089_;
goto v___jp_1067_;
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_a_1111_);
lean_dec(v___x_1089_);
v_a_1137_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1125_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1125_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
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
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v___x_1091_);
lean_dec(v___x_1089_);
lean_del_object(v___x_1086_);
lean_dec(v_a_1076_);
v_a_1149_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1098_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1098_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
v___jp_1160_:
{
uint8_t v___x_1165_; 
v___x_1165_ = l_Lean_Expr_hasMVar(v_a_1076_);
if (v___x_1165_ == 0)
{
v___y_1078_ = v___y_1161_;
v___y_1079_ = v___y_1162_;
v___y_1080_ = v___y_1163_;
v___y_1081_ = v___y_1164_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v___x_1166_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1167_ = l_Lean_MessageData_ofName(v_tacticName_1059_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_indentExpr(v_a_1076_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1172_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1199_, lean_object* v_e_1200_, lean_object* v_axiomDeclRange_x3f_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1199_, v_e_1200_, v_axiomDeclRange_x3f_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_axiomDeclRange_x3f_1201_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1222_, lean_object* v_constName_1223_, uint8_t v_checkMeta_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1223_, v_checkMeta_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_constName_1232_, lean_object* v_checkMeta_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v_checkMeta_boxed_1239_; lean_object* v_res_1240_; 
v_checkMeta_boxed_1239_ = lean_unbox(v_checkMeta_1233_);
v_res_1240_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1231_, v_constName_1232_, v_checkMeta_boxed_1239_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1241_, lean_object* v_msg_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1249_, v_msg_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(lean_object* v_env_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_1257_, v___y_1259_, v___y_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___boxed(lean_object* v_env_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(v_env_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_00_u03b1_1271_, lean_object* v_env_1272_, lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_1272_, v_x_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_env_1281_, lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(v_00_u03b1_1280_, v_env_1281_, v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(lean_object* v_stx_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_1289_, v___y_1292_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___boxed(lean_object* v_stx_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(v_stx_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v_stx_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(lean_object* v_declName_1303_, lean_object* v_declRanges_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_1303_, v_declRanges_1304_, v___y_1306_, v___y_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___boxed(lean_object* v_declName_1311_, lean_object* v_declRanges_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(v_declName_1311_, v_declRanges_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1327_, v_x_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1334_;
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

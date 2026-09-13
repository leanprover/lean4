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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_async;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18_value)} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19_value)} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__20 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__20_value;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_NativeEqTrueResult_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_prf_8_; lean_object* v___x_9_; 
v_prf_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_prf_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_prf_8_);
return v___x_9_;
}
else
{
return v_k_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_NativeEqTrueResult_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim___redArg(lean_object* v_t_22_, lean_object* v_success_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_22_, v_success_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_success_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_success_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_26_, v_success_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim___redArg(lean_object* v_t_30_, lean_object* v_notTrue_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_30_, v_notTrue_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NativeEqTrueResult_notTrue_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_notTrue_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_NativeEqTrueResult_ctorElim___redArg(v_t_34_, v_notTrue_36_);
return v___x_37_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_instMonadEIO___redArg();
return v___x_38_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__0);
v___x_40_ = l_StateRefT_x27_instMonad___redArg(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6(void){
_start:
{
lean_object* v___x_45_; lean_object* v___f_46_; 
v___x_45_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_46_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_46_, 0, v___x_45_);
return v___f_46_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7(void){
_start:
{
lean_object* v___x_47_; lean_object* v___f_48_; 
v___x_47_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_48_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
return v___f_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8(void){
_start:
{
lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___x_51_; 
v___f_49_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__7);
v___f_50_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__6);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___f_50_);
lean_ctor_set(v___x_51_, 1, v___f_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9(void){
_start:
{
lean_object* v___x_52_; lean_object* v___f_53_; 
v___x_52_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8);
v___f_53_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_53_, 0, v___x_52_);
return v___f_53_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10(void){
_start:
{
lean_object* v___x_54_; lean_object* v___f_55_; 
v___x_54_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__8);
v___f_55_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_55_, 0, v___x_54_);
return v___f_55_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11(void){
_start:
{
lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; 
v___f_56_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__10);
v___f_57_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__9);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___f_57_);
lean_ctor_set(v___x_58_, 1, v___f_56_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__15));
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__14));
v___x_66_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_65_, v___x_64_, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17(void){
_start:
{
lean_object* v___x_67_; lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; 
v___x_67_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__16);
v___f_68_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13));
v___f_69_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12));
v___x_70_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_69_, v___f_68_, v___x_67_);
return v___x_70_;
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
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_toMonadRef_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_64__overap_131_; lean_object* v___x_132_; 
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
v___x_129_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__20));
v___x_130_ = 1;
v___x_64__overap_131_ = l_Lean_evalConst___redArg(v___x_121_, v___x_122_, v___x_128_, v___x_129_, v_auxDeclName_76_, v___x_130_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
v___x_132_ = lean_apply_5(v___x_64__overap_131_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, lean_box(0));
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
lean_object* v___x_192_; lean_object* v_auxDeclNGen_193_; lean_object* v___x_194_; lean_object* v_env_195_; lean_object* v___x_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_199_; lean_object* v_env_200_; lean_object* v_nextMacroScope_201_; lean_object* v_ngen_202_; lean_object* v_traceState_203_; lean_object* v_cache_204_; lean_object* v_messages_205_; lean_object* v_infoState_206_; lean_object* v_snapshotTasks_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
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
v_messages_205_ = lean_ctor_get(v___x_199_, 6);
v_infoState_206_ = lean_ctor_get(v___x_199_, 7);
v_snapshotTasks_207_ = lean_ctor_get(v___x_199_, 8);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v___x_199_, 3);
lean_dec(v_unused_217_);
v___x_209_ = v___x_199_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snapshotTasks_207_);
lean_inc(v_infoState_206_);
lean_inc(v_messages_205_);
lean_inc(v_cache_204_);
lean_inc(v_traceState_203_);
lean_inc(v_ngen_202_);
lean_inc(v_nextMacroScope_201_);
lean_inc(v_env_200_);
lean_dec(v___x_199_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 3, v_snd_198_);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_env_200_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_nextMacroScope_201_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_ngen_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_snd_198_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_traceState_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 5, v_cache_204_);
lean_ctor_set(v_reuseFailAlloc_215_, 6, v_messages_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 7, v_infoState_206_);
lean_ctor_set(v_reuseFailAlloc_215_, 8, v_snapshotTasks_207_);
v___x_212_ = v_reuseFailAlloc_215_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_st_ref_put(v___y_190_, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v_fst_197_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object* v_kind_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_218_, v___y_219_);
lean_dec(v___y_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object* v_kind_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_222_, v___y_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object* v_kind_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_235_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_opts_236_, lean_object* v_opt_237_){
_start:
{
lean_object* v_name_238_; lean_object* v_defValue_239_; lean_object* v_map_240_; lean_object* v___x_241_; 
v_name_238_ = lean_ctor_get(v_opt_237_, 0);
v_defValue_239_ = lean_ctor_get(v_opt_237_, 1);
v_map_240_ = lean_ctor_get(v_opts_236_, 0);
v___x_241_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_240_, v_name_238_);
if (lean_obj_tag(v___x_241_) == 0)
{
uint8_t v___x_242_; 
v___x_242_ = lean_unbox(v_defValue_239_);
return v___x_242_;
}
else
{
lean_object* v_val_243_; 
v_val_243_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v___x_241_, 1);
if (lean_obj_tag(v_val_243_) == 1)
{
uint8_t v_v_244_; 
v_v_244_ = lean_ctor_get_uint8(v_val_243_, 0);
lean_dec_ref_known(v_val_243_, 0);
return v_v_244_;
}
else
{
uint8_t v___x_245_; 
lean_dec(v_val_243_);
v___x_245_ = lean_unbox(v_defValue_239_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v_opts_246_, v_opt_247_);
lean_dec_ref(v_opt_247_);
lean_dec_ref(v_opts_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_opts_250_, lean_object* v_opt_251_){
_start:
{
lean_object* v_name_252_; lean_object* v_defValue_253_; lean_object* v_map_254_; lean_object* v___x_255_; 
v_name_252_ = lean_ctor_get(v_opt_251_, 0);
v_defValue_253_ = lean_ctor_get(v_opt_251_, 1);
v_map_254_ = lean_ctor_get(v_opts_250_, 0);
v___x_255_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_254_, v_name_252_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_inc(v_defValue_253_);
return v_defValue_253_;
}
else
{
lean_object* v_val_256_; 
v_val_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_255_, 1);
if (lean_obj_tag(v_val_256_) == 3)
{
lean_object* v_v_257_; 
v_v_257_ = lean_ctor_get(v_val_256_, 0);
lean_inc(v_v_257_);
lean_dec_ref_known(v_val_256_, 1);
return v_v_257_;
}
else
{
lean_dec(v_val_256_);
lean_inc(v_defValue_253_);
return v_defValue_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object* v_opts_258_, lean_object* v_opt_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v_opts_258_, v_opt_259_);
lean_dec_ref(v_opt_259_);
lean_dec_ref(v_opts_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object* v_msgData_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_env_268_; lean_object* v___x_269_; lean_object* v_toCold_270_; lean_object* v_mctx_271_; lean_object* v_lctx_272_; lean_object* v_options_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_267_ = lean_st_ref_get(v___y_265_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_env_268_);
lean_dec(v___x_267_);
v___x_269_ = lean_st_ref_get(v___y_263_);
v_toCold_270_ = lean_ctor_get(v___y_264_, 0);
v_mctx_271_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_mctx_271_);
lean_dec(v___x_269_);
v_lctx_272_ = lean_ctor_get(v___y_262_, 2);
v_options_273_ = lean_ctor_get(v_toCold_270_, 2);
lean_inc_ref(v_options_273_);
lean_inc_ref(v_lctx_272_);
v___x_274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_274_, 0, v_env_268_);
lean_ctor_set(v___x_274_, 1, v_mctx_271_);
lean_ctor_set(v___x_274_, 2, v_lctx_272_);
lean_ctor_set(v___x_274_, 3, v_options_273_);
v___x_275_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v_msgData_261_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object* v_msgData_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msgData_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_ref_290_; lean_object* v___x_291_; lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
v_ref_290_ = lean_ctor_get(v___y_287_, 2);
v___x_291_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msg_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_300_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
lean_inc(v_ref_290_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_ref_290_);
lean_ctor_set(v___x_296_, 1, v_a_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 1);
lean_ctor_set(v___x_294_, 0, v___x_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(lean_object* v_o_311_, lean_object* v_k_312_, uint8_t v_v_313_){
_start:
{
lean_object* v_map_314_; uint8_t v_hasTrace_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_329_; 
v_map_314_ = lean_ctor_get(v_o_311_, 0);
v_hasTrace_315_ = lean_ctor_get_uint8(v_o_311_, sizeof(void*)*1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_o_311_);
if (v_isSharedCheck_329_ == 0)
{
v___x_317_ = v_o_311_;
v_isShared_318_ = v_isSharedCheck_329_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_map_314_);
lean_dec(v_o_311_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_329_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_319_, 0, v_v_313_);
lean_inc(v_k_312_);
v___x_320_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_312_, v___x_319_, v_map_314_);
if (v_hasTrace_315_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_324_; 
v___x_321_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__1));
v___x_322_ = l_Lean_Name_isPrefixOf(v___x_321_, v_k_312_);
lean_dec(v_k_312_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_320_);
v___x_324_ = v___x_317_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_320_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_322_);
return v___x_324_;
}
}
else
{
lean_object* v___x_327_; 
lean_dec(v_k_312_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_320_);
v___x_327_ = v___x_317_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_328_, sizeof(void*)*1, v_hasTrace_315_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___boxed(lean_object* v_o_330_, lean_object* v_k_331_, lean_object* v_v_332_){
_start:
{
uint8_t v_v_boxed_333_; lean_object* v_res_334_; 
v_v_boxed_333_ = lean_unbox(v_v_332_);
v_res_334_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(v_o_330_, v_k_331_, v_v_boxed_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_335_, lean_object* v_opt_336_, uint8_t v_val_337_){
_start:
{
lean_object* v_name_338_; lean_object* v___x_339_; 
v_name_338_ = lean_ctor_get(v_opt_336_, 0);
lean_inc(v_name_338_);
lean_dec_ref(v_opt_336_);
v___x_339_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(v_opts_335_, v_name_338_, v_val_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_340_, lean_object* v_opt_341_, lean_object* v_val_342_){
_start:
{
uint8_t v_val_boxed_343_; lean_object* v_res_344_; 
v_val_boxed_343_ = lean_unbox(v_val_342_);
v_res_344_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_340_, v_opt_341_, v_val_boxed_343_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_box(0);
v___x_346_ = l_Lean_Elab_abortCommandExceptionId;
v___x_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___boxed(lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
if (lean_obj_tag(v_x_353_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_359_ = lean_ctor_get(v_x_353_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v_x_353_, 1);
v___x_360_ = l_Lean_stringToMessageData(v_a_359_);
v___x_361_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_360_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v_x_353_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_x_353_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v_x_353_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v_x_353_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 0);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(lean_object* v_constName_377_, uint8_t v_checkMeta_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
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
lean_object* v___x_387_; lean_object* v_toCold_388_; lean_object* v_env_389_; lean_object* v_options_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_387_ = lean_st_ref_get(v___y_382_);
v_toCold_388_ = lean_ctor_get(v___y_381_, 0);
v_env_389_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_387_);
v_options_390_ = lean_ctor_get(v_toCold_388_, 2);
v___x_391_ = l_Lean_Environment_evalConst___redArg(v_env_389_, v_options_390_, v_constName_377_, v_checkMeta_378_);
lean_dec(v_constName_377_);
lean_dec_ref(v_env_389_);
v___x_392_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_391_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_394_; lean_object* v_toCold_395_; lean_object* v_env_396_; lean_object* v_options_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref_known(v___x_393_, 1);
v___x_394_ = lean_st_ref_get(v___y_382_);
v_toCold_395_ = lean_ctor_get(v___y_381_, 0);
v_env_396_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_394_);
v_options_397_ = lean_ctor_get(v_toCold_395_, 2);
v___x_398_ = l_Lean_Environment_evalConst___redArg(v_env_396_, v_options_397_, v_constName_377_, v_checkMeta_378_);
lean_dec(v_constName_377_);
lean_dec_ref(v_env_396_);
v___x_399_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_398_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_399_;
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_constName_377_);
v_a_400_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_393_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_393_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg___boxed(lean_object* v_constName_408_, lean_object* v_checkMeta_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
uint8_t v_checkMeta_boxed_415_; lean_object* v_res_416_; 
v_checkMeta_boxed_415_ = lean_unbox(v_checkMeta_409_);
v_res_416_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_408_, v_checkMeta_boxed_415_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_416_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__4));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_box(0);
v___x_430_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_431_ = l_Lean_mkConst(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_438_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
lean_ctor_set(v___x_438_, 2, v___x_437_);
lean_ctor_set(v___x_438_, 3, v___x_437_);
lean_ctor_set(v___x_438_, 4, v___x_437_);
lean_ctor_set(v___x_438_, 5, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v_tacticName_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v_a_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; lean_object* v___x_461_; lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_758_; 
v___x_461_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_440_, v___y_447_);
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_758_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_758_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_758_;
goto v_resetjp_463_;
}
v___jp_449_:
{
if (v___y_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v___y_450_);
v___x_453_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_454_ = l_Lean_MessageData_ofName(v_tacticName_439_);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_Exception_toMessageData(v___y_451_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_459_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec_ref(v___y_446_);
return v___x_460_;
}
else
{
lean_dec_ref(v___y_451_);
lean_dec_ref(v___y_446_);
lean_dec(v_tacticName_439_);
return v___y_450_;
}
}
v_resetjp_463_:
{
lean_object* v___y_467_; lean_object* v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_493_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_462_, 2);
v___x_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_494_, 0, v_a_462_);
lean_ctor_set(v___x_494_, 1, v___x_441_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
v___x_495_ = lean_box(1);
v___x_496_ = 1;
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v_a_462_);
lean_ctor_set(v___x_497_, 1, v___x_442_);
v___x_498_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_498_, 0, v___x_494_);
lean_ctor_set(v___x_498_, 1, v_a_443_);
lean_ctor_set(v___x_498_, 2, v___x_495_);
lean_ctor_set(v___x_498_, 3, v___x_497_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*4, v___x_496_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 1);
lean_ctor_set(v___x_464_, 0, v___x_498_);
v___x_500_ = v___x_464_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_757_;
goto v_reusejp_499_;
}
v___jp_466_:
{
if (lean_obj_tag(v___y_467_) == 0)
{
uint8_t v___x_468_; lean_object* v___x_469_; 
lean_dec_ref_known(v___y_467_, 1);
v___x_468_ = 1;
v___x_469_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_a_462_, v___x_468_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_dec_ref(v___y_446_);
lean_dec(v_tacticName_439_);
return v___x_469_;
}
else
{
lean_object* v_a_470_; uint8_t v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
v___x_471_ = l_Lean_Exception_isInterrupt(v_a_470_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
lean_inc(v_a_470_);
v___x_472_ = l_Lean_Exception_isRuntime(v_a_470_);
v___y_450_ = v___x_469_;
v___y_451_ = v_a_470_;
v___y_452_ = v___x_472_;
goto v___jp_449_;
}
else
{
v___y_450_ = v___x_469_;
v___y_451_ = v_a_470_;
v___y_452_ = v___x_471_;
goto v___jp_449_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_a_462_);
lean_dec_ref(v___y_446_);
lean_dec(v_tacticName_439_);
v_a_473_ = lean_ctor_get(v___y_467_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_467_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___y_467_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___y_467_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
v___jp_481_:
{
if (v___y_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v___y_483_);
v___x_485_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_439_);
v___x_486_ = l_Lean_MessageData_ofName(v_tacticName_439_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_Exception_toMessageData(v___y_482_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_491_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
v___y_467_ = v___x_492_;
goto v___jp_466_;
}
else
{
lean_dec_ref(v___y_482_);
v___y_467_ = v___y_483_;
goto v___jp_466_;
}
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v_env_502_; lean_object* v_nextMacroScope_503_; lean_object* v_ngen_504_; lean_object* v_auxDeclNGen_505_; lean_object* v_traceState_506_; lean_object* v_messages_507_; lean_object* v_infoState_508_; lean_object* v_snapshotTasks_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_755_; 
v___x_501_ = lean_st_ref_take(v___y_447_);
v_env_502_ = lean_ctor_get(v___x_501_, 0);
v_nextMacroScope_503_ = lean_ctor_get(v___x_501_, 1);
v_ngen_504_ = lean_ctor_get(v___x_501_, 2);
v_auxDeclNGen_505_ = lean_ctor_get(v___x_501_, 3);
v_traceState_506_ = lean_ctor_get(v___x_501_, 4);
v_messages_507_ = lean_ctor_get(v___x_501_, 6);
v_infoState_508_ = lean_ctor_get(v___x_501_, 7);
v_snapshotTasks_509_ = lean_ctor_get(v___x_501_, 8);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v___x_501_, 5);
lean_dec(v_unused_756_);
v___x_511_ = v___x_501_;
v_isShared_512_ = v_isSharedCheck_755_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snapshotTasks_509_);
lean_inc(v_infoState_508_);
lean_inc(v_messages_507_);
lean_inc(v_traceState_506_);
lean_inc(v_auxDeclNGen_505_);
lean_inc(v_ngen_504_);
lean_inc(v_nextMacroScope_503_);
lean_inc(v_env_502_);
lean_dec(v___x_501_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_755_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_inc(v_a_462_);
v___x_513_ = l_Lean_markMeta(v_env_502_, v_a_462_);
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
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_nextMacroScope_503_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_ngen_504_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_auxDeclNGen_505_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_traceState_506_);
lean_ctor_set(v_reuseFailAlloc_754_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_754_, 6, v_messages_507_);
lean_ctor_set(v_reuseFailAlloc_754_, 7, v_infoState_508_);
lean_ctor_set(v_reuseFailAlloc_754_, 8, v_snapshotTasks_509_);
v___x_516_ = v_reuseFailAlloc_754_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_mctx_519_; lean_object* v_zetaDeltaFVarIds_520_; lean_object* v_postponed_521_; lean_object* v_diag_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_752_; 
v___x_517_ = lean_st_ref_put(v___y_447_, v___x_516_);
v___x_518_ = lean_st_ref_take(v___y_445_);
v_mctx_519_ = lean_ctor_get(v___x_518_, 0);
v_zetaDeltaFVarIds_520_ = lean_ctor_get(v___x_518_, 2);
v_postponed_521_ = lean_ctor_get(v___x_518_, 3);
v_diag_522_ = lean_ctor_get(v___x_518_, 4);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v___x_518_, 1);
lean_dec(v_unused_753_);
v___x_524_ = v___x_518_;
v_isShared_525_ = v_isSharedCheck_752_;
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
v_isShared_525_ = v_isSharedCheck_752_;
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
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_mctx_519_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_zetaDeltaFVarIds_520_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_postponed_521_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_diag_522_);
v___x_528_ = v_reuseFailAlloc_751_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v_toCold_530_; lean_object* v_currRecDepth_531_; lean_object* v_ref_532_; uint8_t v_suppressElabErrors_533_; lean_object* v_fileName_534_; lean_object* v_fileMap_535_; lean_object* v_options_536_; lean_object* v_currNamespace_537_; lean_object* v_openDecls_538_; lean_object* v_initHeartbeats_539_; lean_object* v_maxHeartbeats_540_; lean_object* v_quotContext_541_; lean_object* v_currMacroScope_542_; lean_object* v_cancelTk_x3f_543_; lean_object* v_inheritedTraceOptions_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_749_; 
v___x_529_ = lean_st_ref_put(v___y_445_, v___x_528_);
v_toCold_530_ = lean_ctor_get(v___y_446_, 0);
lean_inc_ref(v_toCold_530_);
v_currRecDepth_531_ = lean_ctor_get(v___y_446_, 1);
v_ref_532_ = lean_ctor_get(v___y_446_, 2);
v_suppressElabErrors_533_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*3 + 1);
v_fileName_534_ = lean_ctor_get(v_toCold_530_, 0);
v_fileMap_535_ = lean_ctor_get(v_toCold_530_, 1);
v_options_536_ = lean_ctor_get(v_toCold_530_, 2);
v_currNamespace_537_ = lean_ctor_get(v_toCold_530_, 4);
v_openDecls_538_ = lean_ctor_get(v_toCold_530_, 5);
v_initHeartbeats_539_ = lean_ctor_get(v_toCold_530_, 6);
v_maxHeartbeats_540_ = lean_ctor_get(v_toCold_530_, 7);
v_quotContext_541_ = lean_ctor_get(v_toCold_530_, 8);
v_currMacroScope_542_ = lean_ctor_get(v_toCold_530_, 9);
v_cancelTk_x3f_543_ = lean_ctor_get(v_toCold_530_, 10);
v_inheritedTraceOptions_544_ = lean_ctor_get(v_toCold_530_, 11);
v_isSharedCheck_749_ = !lean_is_exclusive(v_toCold_530_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_toCold_530_, 3);
lean_dec(v_unused_750_);
v___x_546_ = v_toCold_530_;
v_isShared_547_ = v_isSharedCheck_749_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_inheritedTraceOptions_544_);
lean_inc(v_cancelTk_x3f_543_);
lean_inc(v_currMacroScope_542_);
lean_inc(v_quotContext_541_);
lean_inc(v_maxHeartbeats_540_);
lean_inc(v_initHeartbeats_539_);
lean_inc(v_openDecls_538_);
lean_inc(v_currNamespace_537_);
lean_inc(v_options_536_);
lean_inc(v_fileMap_535_);
lean_inc(v_fileName_534_);
lean_dec(v_toCold_530_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_749_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v___x_548_; uint8_t v___x_549_; lean_object* v___y_551_; lean_object* v___y_552_; uint8_t v___y_553_; lean_object* v_fileName_554_; lean_object* v_fileMap_555_; lean_object* v_currNamespace_556_; lean_object* v_openDecls_557_; lean_object* v_initHeartbeats_558_; lean_object* v_maxHeartbeats_559_; lean_object* v_quotContext_560_; lean_object* v_currMacroScope_561_; lean_object* v_cancelTk_x3f_562_; lean_object* v_inheritedTraceOptions_563_; lean_object* v_currRecDepth_564_; lean_object* v_ref_565_; uint8_t v_suppressElabErrors_566_; lean_object* v___y_567_; lean_object* v___y_578_; lean_object* v___y_579_; uint8_t v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_598_; lean_object* v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v_fileName_630_; lean_object* v_fileMap_631_; lean_object* v_currNamespace_632_; lean_object* v_openDecls_633_; lean_object* v_initHeartbeats_634_; lean_object* v_maxHeartbeats_635_; lean_object* v_quotContext_636_; lean_object* v_currMacroScope_637_; lean_object* v_cancelTk_x3f_638_; lean_object* v_inheritedTraceOptions_639_; lean_object* v_currRecDepth_640_; lean_object* v_ref_641_; uint8_t v_suppressElabErrors_642_; lean_object* v___y_643_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; uint8_t v___y_679_; uint8_t v___x_699_; lean_object* v_fileName_701_; lean_object* v_fileMap_702_; lean_object* v_currNamespace_703_; lean_object* v_openDecls_704_; lean_object* v_initHeartbeats_705_; lean_object* v_maxHeartbeats_706_; lean_object* v_quotContext_707_; lean_object* v_currMacroScope_708_; lean_object* v_cancelTk_x3f_709_; lean_object* v_inheritedTraceOptions_710_; lean_object* v_currRecDepth_711_; lean_object* v_ref_712_; uint8_t v_suppressElabErrors_713_; lean_object* v___y_714_; lean_object* v___x_725_; uint8_t v___y_727_; lean_object* v_env_747_; uint8_t v___x_748_; 
v___x_548_ = 1;
v___x_549_ = 0;
v___x_623_ = l_Lean_Elab_async;
v___x_624_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v_options_536_, v___x_623_, v___x_549_);
v___x_625_ = l_Lean_diagnostics;
v___x_699_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_624_, v___x_625_);
v___x_725_ = lean_st_ref_get(v___y_447_);
v_env_747_ = lean_ctor_get(v___x_725_, 0);
lean_inc_ref(v_env_747_);
lean_dec(v___x_725_);
v___x_748_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_747_);
lean_dec_ref(v_env_747_);
if (v___x_699_ == 0)
{
if (v___x_748_ == 0)
{
lean_inc(v_ref_532_);
lean_inc(v_currRecDepth_531_);
v_fileName_701_ = v_fileName_534_;
v_fileMap_702_ = v_fileMap_535_;
v_currNamespace_703_ = v_currNamespace_537_;
v_openDecls_704_ = v_openDecls_538_;
v_initHeartbeats_705_ = v_initHeartbeats_539_;
v_maxHeartbeats_706_ = v_maxHeartbeats_540_;
v_quotContext_707_ = v_quotContext_541_;
v_currMacroScope_708_ = v_currMacroScope_542_;
v_cancelTk_x3f_709_ = v_cancelTk_x3f_543_;
v_inheritedTraceOptions_710_ = v_inheritedTraceOptions_544_;
v_currRecDepth_711_ = v_currRecDepth_531_;
v_ref_712_ = v_ref_532_;
v_suppressElabErrors_713_ = v_suppressElabErrors_533_;
v___y_714_ = v___y_447_;
goto v___jp_700_;
}
else
{
v___y_727_ = v___x_699_;
goto v___jp_726_;
}
}
else
{
v___y_727_ = v___x_748_;
goto v___jp_726_;
}
v___jp_550_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_552_, v___y_551_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 11, v_inheritedTraceOptions_563_);
lean_ctor_set(v___x_546_, 10, v_cancelTk_x3f_562_);
lean_ctor_set(v___x_546_, 9, v_currMacroScope_561_);
lean_ctor_set(v___x_546_, 8, v_quotContext_560_);
lean_ctor_set(v___x_546_, 7, v_maxHeartbeats_559_);
lean_ctor_set(v___x_546_, 6, v_initHeartbeats_558_);
lean_ctor_set(v___x_546_, 5, v_openDecls_557_);
lean_ctor_set(v___x_546_, 4, v_currNamespace_556_);
lean_ctor_set(v___x_546_, 3, v___x_568_);
lean_ctor_set(v___x_546_, 2, v___y_552_);
lean_ctor_set(v___x_546_, 1, v_fileMap_555_);
lean_ctor_set(v___x_546_, 0, v_fileName_554_);
v___x_570_ = v___x_546_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_fileName_554_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_fileMap_555_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v___y_552_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_currNamespace_556_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v_openDecls_557_);
lean_ctor_set(v_reuseFailAlloc_576_, 6, v_initHeartbeats_558_);
lean_ctor_set(v_reuseFailAlloc_576_, 7, v_maxHeartbeats_559_);
lean_ctor_set(v_reuseFailAlloc_576_, 8, v_quotContext_560_);
lean_ctor_set(v_reuseFailAlloc_576_, 9, v_currMacroScope_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 10, v_cancelTk_x3f_562_);
lean_ctor_set(v_reuseFailAlloc_576_, 11, v_inheritedTraceOptions_563_);
v___x_570_ = v_reuseFailAlloc_576_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_currRecDepth_564_);
lean_ctor_set(v___x_571_, 2, v_ref_565_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*3, v___y_553_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*3 + 1, v_suppressElabErrors_566_);
v___x_572_ = l_Lean_addAndCompile(v___x_500_, v___x_548_, v___x_549_, v___x_571_, v___y_567_);
lean_dec_ref_known(v___x_571_, 3);
if (lean_obj_tag(v___x_572_) == 0)
{
v___y_467_ = v___x_572_;
goto v___jp_466_;
}
else
{
lean_object* v_a_573_; uint8_t v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
v___x_574_ = l_Lean_Exception_isInterrupt(v_a_573_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; 
lean_inc(v_a_573_);
v___x_575_ = l_Lean_Exception_isRuntime(v_a_573_);
v___y_482_ = v_a_573_;
v___y_483_ = v___x_572_;
v___y_484_ = v___x_575_;
goto v___jp_481_;
}
else
{
v___y_482_ = v_a_573_;
v___y_483_ = v___x_572_;
v___y_484_ = v___x_574_;
goto v___jp_481_;
}
}
}
}
v___jp_577_:
{
lean_object* v_toCold_583_; lean_object* v_currRecDepth_584_; lean_object* v_ref_585_; uint8_t v_suppressElabErrors_586_; lean_object* v_fileName_587_; lean_object* v_fileMap_588_; lean_object* v_currNamespace_589_; lean_object* v_openDecls_590_; lean_object* v_initHeartbeats_591_; lean_object* v_maxHeartbeats_592_; lean_object* v_quotContext_593_; lean_object* v_currMacroScope_594_; lean_object* v_cancelTk_x3f_595_; lean_object* v_inheritedTraceOptions_596_; 
v_toCold_583_ = lean_ctor_get(v___y_581_, 0);
lean_inc_ref(v_toCold_583_);
v_currRecDepth_584_ = lean_ctor_get(v___y_581_, 1);
lean_inc(v_currRecDepth_584_);
v_ref_585_ = lean_ctor_get(v___y_581_, 2);
lean_inc(v_ref_585_);
v_suppressElabErrors_586_ = lean_ctor_get_uint8(v___y_581_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_581_);
v_fileName_587_ = lean_ctor_get(v_toCold_583_, 0);
lean_inc_ref(v_fileName_587_);
v_fileMap_588_ = lean_ctor_get(v_toCold_583_, 1);
lean_inc_ref(v_fileMap_588_);
v_currNamespace_589_ = lean_ctor_get(v_toCold_583_, 4);
lean_inc(v_currNamespace_589_);
v_openDecls_590_ = lean_ctor_get(v_toCold_583_, 5);
lean_inc(v_openDecls_590_);
v_initHeartbeats_591_ = lean_ctor_get(v_toCold_583_, 6);
lean_inc(v_initHeartbeats_591_);
v_maxHeartbeats_592_ = lean_ctor_get(v_toCold_583_, 7);
lean_inc(v_maxHeartbeats_592_);
v_quotContext_593_ = lean_ctor_get(v_toCold_583_, 8);
lean_inc(v_quotContext_593_);
v_currMacroScope_594_ = lean_ctor_get(v_toCold_583_, 9);
lean_inc(v_currMacroScope_594_);
v_cancelTk_x3f_595_ = lean_ctor_get(v_toCold_583_, 10);
lean_inc(v_cancelTk_x3f_595_);
v_inheritedTraceOptions_596_ = lean_ctor_get(v_toCold_583_, 11);
lean_inc_ref(v_inheritedTraceOptions_596_);
lean_dec_ref(v_toCold_583_);
v___y_551_ = v___y_578_;
v___y_552_ = v___y_579_;
v___y_553_ = v___y_580_;
v_fileName_554_ = v_fileName_587_;
v_fileMap_555_ = v_fileMap_588_;
v_currNamespace_556_ = v_currNamespace_589_;
v_openDecls_557_ = v_openDecls_590_;
v_initHeartbeats_558_ = v_initHeartbeats_591_;
v_maxHeartbeats_559_ = v_maxHeartbeats_592_;
v_quotContext_560_ = v_quotContext_593_;
v_currMacroScope_561_ = v_currMacroScope_594_;
v_cancelTk_x3f_562_ = v_cancelTk_x3f_595_;
v_inheritedTraceOptions_563_ = v_inheritedTraceOptions_596_;
v_currRecDepth_564_ = v_currRecDepth_584_;
v_ref_565_ = v_ref_585_;
v_suppressElabErrors_566_ = v_suppressElabErrors_586_;
v___y_567_ = v___y_582_;
goto v___jp_550_;
}
v___jp_597_:
{
if (v___y_603_ == 0)
{
lean_object* v___x_604_; lean_object* v_env_605_; lean_object* v_nextMacroScope_606_; lean_object* v_ngen_607_; lean_object* v_auxDeclNGen_608_; lean_object* v_traceState_609_; lean_object* v_messages_610_; lean_object* v_infoState_611_; lean_object* v_snapshotTasks_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_621_; 
v___x_604_ = lean_st_ref_take(v___y_602_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
v_nextMacroScope_606_ = lean_ctor_get(v___x_604_, 1);
v_ngen_607_ = lean_ctor_get(v___x_604_, 2);
v_auxDeclNGen_608_ = lean_ctor_get(v___x_604_, 3);
v_traceState_609_ = lean_ctor_get(v___x_604_, 4);
v_messages_610_ = lean_ctor_get(v___x_604_, 6);
v_infoState_611_ = lean_ctor_get(v___x_604_, 7);
v_snapshotTasks_612_ = lean_ctor_get(v___x_604_, 8);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_604_, 5);
lean_dec(v_unused_622_);
v___x_614_ = v___x_604_;
v_isShared_615_ = v_isSharedCheck_621_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snapshotTasks_612_);
lean_inc(v_infoState_611_);
lean_inc(v_messages_610_);
lean_inc(v_traceState_609_);
lean_inc(v_auxDeclNGen_608_);
lean_inc(v_ngen_607_);
lean_inc(v_nextMacroScope_606_);
lean_inc(v_env_605_);
lean_dec(v___x_604_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_621_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = l_Lean_Kernel_enableDiag(v_env_605_, v___y_600_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 5, v___x_514_);
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_nextMacroScope_606_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_ngen_607_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_auxDeclNGen_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_traceState_609_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v_messages_610_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v_infoState_611_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v_snapshotTasks_612_);
v___x_618_ = v_reuseFailAlloc_620_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; 
v___x_619_ = lean_st_ref_put(v___y_602_, v___x_618_);
v___y_578_ = v___y_598_;
v___y_579_ = v___y_599_;
v___y_580_ = v___y_600_;
v___y_581_ = v___y_601_;
v___y_582_ = v___y_602_;
goto v___jp_577_;
}
}
}
else
{
v___y_578_ = v___y_598_;
v___y_579_ = v___y_599_;
v___y_580_ = v___y_600_;
v___y_581_ = v___y_601_;
v___y_582_ = v___y_602_;
goto v___jp_577_;
}
}
v___jp_626_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v_env_651_; uint8_t v___x_652_; 
v___x_644_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_629_, v___y_628_);
lean_inc_ref(v_inheritedTraceOptions_639_);
lean_inc(v_cancelTk_x3f_638_);
lean_inc(v_currMacroScope_637_);
lean_inc(v_quotContext_636_);
lean_inc(v_maxHeartbeats_635_);
lean_inc(v_initHeartbeats_634_);
lean_inc(v_openDecls_633_);
lean_inc(v_currNamespace_632_);
lean_inc_ref(v___y_629_);
lean_inc_ref(v_fileMap_631_);
lean_inc_ref(v_fileName_630_);
v___x_645_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_645_, 0, v_fileName_630_);
lean_ctor_set(v___x_645_, 1, v_fileMap_631_);
lean_ctor_set(v___x_645_, 2, v___y_629_);
lean_ctor_set(v___x_645_, 3, v___x_644_);
lean_ctor_set(v___x_645_, 4, v_currNamespace_632_);
lean_ctor_set(v___x_645_, 5, v_openDecls_633_);
lean_ctor_set(v___x_645_, 6, v_initHeartbeats_634_);
lean_ctor_set(v___x_645_, 7, v_maxHeartbeats_635_);
lean_ctor_set(v___x_645_, 8, v_quotContext_636_);
lean_ctor_set(v___x_645_, 9, v_currMacroScope_637_);
lean_ctor_set(v___x_645_, 10, v_cancelTk_x3f_638_);
lean_ctor_set(v___x_645_, 11, v_inheritedTraceOptions_639_);
lean_inc(v_ref_641_);
lean_inc(v_currRecDepth_640_);
v___x_646_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_currRecDepth_640_);
lean_ctor_set(v___x_646_, 2, v_ref_641_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*3, v___y_627_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*3 + 1, v_suppressElabErrors_642_);
v___x_647_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_648_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_629_, v___x_647_, v___x_548_);
v___x_649_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_648_, v___x_625_);
v___x_650_ = lean_st_ref_get(v___y_643_);
v_env_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_env_651_);
lean_dec(v___x_650_);
v___x_652_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_651_);
lean_dec_ref(v_env_651_);
if (v___x_649_ == 0)
{
if (v___x_652_ == 0)
{
lean_dec_ref_known(v___x_646_, 3);
v___y_551_ = v___y_628_;
v___y_552_ = v___x_648_;
v___y_553_ = v___x_649_;
v_fileName_554_ = v_fileName_630_;
v_fileMap_555_ = v_fileMap_631_;
v_currNamespace_556_ = v_currNamespace_632_;
v_openDecls_557_ = v_openDecls_633_;
v_initHeartbeats_558_ = v_initHeartbeats_634_;
v_maxHeartbeats_559_ = v_maxHeartbeats_635_;
v_quotContext_560_ = v_quotContext_636_;
v_currMacroScope_561_ = v_currMacroScope_637_;
v_cancelTk_x3f_562_ = v_cancelTk_x3f_638_;
v_inheritedTraceOptions_563_ = v_inheritedTraceOptions_639_;
v_currRecDepth_564_ = v_currRecDepth_640_;
v_ref_565_ = v_ref_641_;
v_suppressElabErrors_566_ = v_suppressElabErrors_642_;
v___y_567_ = v___y_643_;
goto v___jp_550_;
}
else
{
lean_dec(v_ref_641_);
lean_dec(v_currRecDepth_640_);
lean_dec_ref(v_inheritedTraceOptions_639_);
lean_dec(v_cancelTk_x3f_638_);
lean_dec(v_currMacroScope_637_);
lean_dec(v_quotContext_636_);
lean_dec(v_maxHeartbeats_635_);
lean_dec(v_initHeartbeats_634_);
lean_dec(v_openDecls_633_);
lean_dec(v_currNamespace_632_);
lean_dec_ref(v_fileMap_631_);
lean_dec_ref(v_fileName_630_);
v___y_598_ = v___y_628_;
v___y_599_ = v___x_648_;
v___y_600_ = v___x_649_;
v___y_601_ = v___x_646_;
v___y_602_ = v___y_643_;
v___y_603_ = v___x_649_;
goto v___jp_597_;
}
}
else
{
lean_dec(v_ref_641_);
lean_dec(v_currRecDepth_640_);
lean_dec_ref(v_inheritedTraceOptions_639_);
lean_dec(v_cancelTk_x3f_638_);
lean_dec(v_currMacroScope_637_);
lean_dec(v_quotContext_636_);
lean_dec(v_maxHeartbeats_635_);
lean_dec(v_initHeartbeats_634_);
lean_dec(v_openDecls_633_);
lean_dec(v_currNamespace_632_);
lean_dec_ref(v_fileMap_631_);
lean_dec_ref(v_fileName_630_);
v___y_598_ = v___y_628_;
v___y_599_ = v___x_648_;
v___y_600_ = v___x_649_;
v___y_601_ = v___x_646_;
v___y_602_ = v___y_643_;
v___y_603_ = v___x_652_;
goto v___jp_597_;
}
}
v___jp_653_:
{
lean_object* v_toCold_659_; lean_object* v_currRecDepth_660_; lean_object* v_ref_661_; uint8_t v_suppressElabErrors_662_; lean_object* v_fileName_663_; lean_object* v_fileMap_664_; lean_object* v_currNamespace_665_; lean_object* v_openDecls_666_; lean_object* v_initHeartbeats_667_; lean_object* v_maxHeartbeats_668_; lean_object* v_quotContext_669_; lean_object* v_currMacroScope_670_; lean_object* v_cancelTk_x3f_671_; lean_object* v_inheritedTraceOptions_672_; 
v_toCold_659_ = lean_ctor_get(v___y_657_, 0);
lean_inc_ref(v_toCold_659_);
v_currRecDepth_660_ = lean_ctor_get(v___y_657_, 1);
lean_inc(v_currRecDepth_660_);
v_ref_661_ = lean_ctor_get(v___y_657_, 2);
lean_inc(v_ref_661_);
v_suppressElabErrors_662_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_657_);
v_fileName_663_ = lean_ctor_get(v_toCold_659_, 0);
lean_inc_ref(v_fileName_663_);
v_fileMap_664_ = lean_ctor_get(v_toCold_659_, 1);
lean_inc_ref(v_fileMap_664_);
v_currNamespace_665_ = lean_ctor_get(v_toCold_659_, 4);
lean_inc(v_currNamespace_665_);
v_openDecls_666_ = lean_ctor_get(v_toCold_659_, 5);
lean_inc(v_openDecls_666_);
v_initHeartbeats_667_ = lean_ctor_get(v_toCold_659_, 6);
lean_inc(v_initHeartbeats_667_);
v_maxHeartbeats_668_ = lean_ctor_get(v_toCold_659_, 7);
lean_inc(v_maxHeartbeats_668_);
v_quotContext_669_ = lean_ctor_get(v_toCold_659_, 8);
lean_inc(v_quotContext_669_);
v_currMacroScope_670_ = lean_ctor_get(v_toCold_659_, 9);
lean_inc(v_currMacroScope_670_);
v_cancelTk_x3f_671_ = lean_ctor_get(v_toCold_659_, 10);
lean_inc(v_cancelTk_x3f_671_);
v_inheritedTraceOptions_672_ = lean_ctor_get(v_toCold_659_, 11);
lean_inc_ref(v_inheritedTraceOptions_672_);
lean_dec_ref(v_toCold_659_);
v___y_627_ = v___y_654_;
v___y_628_ = v___y_655_;
v___y_629_ = v___y_656_;
v_fileName_630_ = v_fileName_663_;
v_fileMap_631_ = v_fileMap_664_;
v_currNamespace_632_ = v_currNamespace_665_;
v_openDecls_633_ = v_openDecls_666_;
v_initHeartbeats_634_ = v_initHeartbeats_667_;
v_maxHeartbeats_635_ = v_maxHeartbeats_668_;
v_quotContext_636_ = v_quotContext_669_;
v_currMacroScope_637_ = v_currMacroScope_670_;
v_cancelTk_x3f_638_ = v_cancelTk_x3f_671_;
v_inheritedTraceOptions_639_ = v_inheritedTraceOptions_672_;
v_currRecDepth_640_ = v_currRecDepth_660_;
v_ref_641_ = v_ref_661_;
v_suppressElabErrors_642_ = v_suppressElabErrors_662_;
v___y_643_ = v___y_658_;
goto v___jp_626_;
}
v___jp_673_:
{
if (v___y_679_ == 0)
{
lean_object* v___x_680_; lean_object* v_env_681_; lean_object* v_nextMacroScope_682_; lean_object* v_ngen_683_; lean_object* v_auxDeclNGen_684_; lean_object* v_traceState_685_; lean_object* v_messages_686_; lean_object* v_infoState_687_; lean_object* v_snapshotTasks_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_697_; 
v___x_680_ = lean_st_ref_take(v___y_675_);
v_env_681_ = lean_ctor_get(v___x_680_, 0);
v_nextMacroScope_682_ = lean_ctor_get(v___x_680_, 1);
v_ngen_683_ = lean_ctor_get(v___x_680_, 2);
v_auxDeclNGen_684_ = lean_ctor_get(v___x_680_, 3);
v_traceState_685_ = lean_ctor_get(v___x_680_, 4);
v_messages_686_ = lean_ctor_get(v___x_680_, 6);
v_infoState_687_ = lean_ctor_get(v___x_680_, 7);
v_snapshotTasks_688_ = lean_ctor_get(v___x_680_, 8);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_680_, 5);
lean_dec(v_unused_698_);
v___x_690_ = v___x_680_;
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snapshotTasks_688_);
lean_inc(v_infoState_687_);
lean_inc(v_messages_686_);
lean_inc(v_traceState_685_);
lean_inc(v_auxDeclNGen_684_);
lean_inc(v_ngen_683_);
lean_inc(v_nextMacroScope_682_);
lean_inc(v_env_681_);
lean_dec(v___x_680_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_Kernel_enableDiag(v_env_681_, v___y_674_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 5, v___x_514_);
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_nextMacroScope_682_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_ngen_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_auxDeclNGen_684_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_traceState_685_);
lean_ctor_set(v_reuseFailAlloc_696_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_696_, 6, v_messages_686_);
lean_ctor_set(v_reuseFailAlloc_696_, 7, v_infoState_687_);
lean_ctor_set(v_reuseFailAlloc_696_, 8, v_snapshotTasks_688_);
v___x_694_ = v_reuseFailAlloc_696_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; 
v___x_695_ = lean_st_ref_put(v___y_675_, v___x_694_);
v___y_654_ = v___y_674_;
v___y_655_ = v___y_676_;
v___y_656_ = v___y_677_;
v___y_657_ = v___y_678_;
v___y_658_ = v___y_675_;
goto v___jp_653_;
}
}
}
else
{
v___y_654_ = v___y_674_;
v___y_655_ = v___y_676_;
v___y_656_ = v___y_677_;
v___y_657_ = v___y_678_;
v___y_658_ = v___y_675_;
goto v___jp_653_;
}
}
v___jp_700_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v_env_723_; uint8_t v___x_724_; 
v___x_715_ = l_Lean_maxRecDepth;
v___x_716_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___x_624_, v___x_715_);
lean_inc_ref(v_inheritedTraceOptions_710_);
lean_inc(v_cancelTk_x3f_709_);
lean_inc(v_currMacroScope_708_);
lean_inc(v_quotContext_707_);
lean_inc(v_maxHeartbeats_706_);
lean_inc(v_initHeartbeats_705_);
lean_inc(v_openDecls_704_);
lean_inc(v_currNamespace_703_);
lean_inc_ref(v___x_624_);
lean_inc_ref(v_fileMap_702_);
lean_inc_ref(v_fileName_701_);
v___x_717_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_717_, 0, v_fileName_701_);
lean_ctor_set(v___x_717_, 1, v_fileMap_702_);
lean_ctor_set(v___x_717_, 2, v___x_624_);
lean_ctor_set(v___x_717_, 3, v___x_716_);
lean_ctor_set(v___x_717_, 4, v_currNamespace_703_);
lean_ctor_set(v___x_717_, 5, v_openDecls_704_);
lean_ctor_set(v___x_717_, 6, v_initHeartbeats_705_);
lean_ctor_set(v___x_717_, 7, v_maxHeartbeats_706_);
lean_ctor_set(v___x_717_, 8, v_quotContext_707_);
lean_ctor_set(v___x_717_, 9, v_currMacroScope_708_);
lean_ctor_set(v___x_717_, 10, v_cancelTk_x3f_709_);
lean_ctor_set(v___x_717_, 11, v_inheritedTraceOptions_710_);
lean_inc(v_ref_712_);
lean_inc(v_currRecDepth_711_);
v___x_718_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_currRecDepth_711_);
lean_ctor_set(v___x_718_, 2, v_ref_712_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*3, v___x_699_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*3 + 1, v_suppressElabErrors_713_);
v___x_719_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_720_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_624_, v___x_719_, v___x_549_);
v___x_721_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_720_, v___x_625_);
v___x_722_ = lean_st_ref_get(v___y_714_);
v_env_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_env_723_);
lean_dec(v___x_722_);
v___x_724_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_723_);
lean_dec_ref(v_env_723_);
if (v___x_721_ == 0)
{
if (v___x_724_ == 0)
{
lean_dec_ref_known(v___x_718_, 3);
v___y_627_ = v___x_721_;
v___y_628_ = v___x_715_;
v___y_629_ = v___x_720_;
v_fileName_630_ = v_fileName_701_;
v_fileMap_631_ = v_fileMap_702_;
v_currNamespace_632_ = v_currNamespace_703_;
v_openDecls_633_ = v_openDecls_704_;
v_initHeartbeats_634_ = v_initHeartbeats_705_;
v_maxHeartbeats_635_ = v_maxHeartbeats_706_;
v_quotContext_636_ = v_quotContext_707_;
v_currMacroScope_637_ = v_currMacroScope_708_;
v_cancelTk_x3f_638_ = v_cancelTk_x3f_709_;
v_inheritedTraceOptions_639_ = v_inheritedTraceOptions_710_;
v_currRecDepth_640_ = v_currRecDepth_711_;
v_ref_641_ = v_ref_712_;
v_suppressElabErrors_642_ = v_suppressElabErrors_713_;
v___y_643_ = v___y_714_;
goto v___jp_626_;
}
else
{
lean_dec(v_ref_712_);
lean_dec(v_currRecDepth_711_);
lean_dec_ref(v_inheritedTraceOptions_710_);
lean_dec(v_cancelTk_x3f_709_);
lean_dec(v_currMacroScope_708_);
lean_dec(v_quotContext_707_);
lean_dec(v_maxHeartbeats_706_);
lean_dec(v_initHeartbeats_705_);
lean_dec(v_openDecls_704_);
lean_dec(v_currNamespace_703_);
lean_dec_ref(v_fileMap_702_);
lean_dec_ref(v_fileName_701_);
v___y_674_ = v___x_721_;
v___y_675_ = v___y_714_;
v___y_676_ = v___x_715_;
v___y_677_ = v___x_720_;
v___y_678_ = v___x_718_;
v___y_679_ = v___x_721_;
goto v___jp_673_;
}
}
else
{
lean_dec(v_ref_712_);
lean_dec(v_currRecDepth_711_);
lean_dec_ref(v_inheritedTraceOptions_710_);
lean_dec(v_cancelTk_x3f_709_);
lean_dec(v_currMacroScope_708_);
lean_dec(v_quotContext_707_);
lean_dec(v_maxHeartbeats_706_);
lean_dec(v_initHeartbeats_705_);
lean_dec(v_openDecls_704_);
lean_dec(v_currNamespace_703_);
lean_dec_ref(v_fileMap_702_);
lean_dec_ref(v_fileName_701_);
v___y_674_ = v___x_721_;
v___y_675_ = v___y_714_;
v___y_676_ = v___x_715_;
v___y_677_ = v___x_720_;
v___y_678_ = v___x_718_;
v___y_679_ = v___x_724_;
goto v___jp_673_;
}
}
v___jp_726_:
{
if (v___y_727_ == 0)
{
lean_object* v___x_728_; lean_object* v_env_729_; lean_object* v_nextMacroScope_730_; lean_object* v_ngen_731_; lean_object* v_auxDeclNGen_732_; lean_object* v_traceState_733_; lean_object* v_messages_734_; lean_object* v_infoState_735_; lean_object* v_snapshotTasks_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_745_; 
v___x_728_ = lean_st_ref_take(v___y_447_);
v_env_729_ = lean_ctor_get(v___x_728_, 0);
v_nextMacroScope_730_ = lean_ctor_get(v___x_728_, 1);
v_ngen_731_ = lean_ctor_get(v___x_728_, 2);
v_auxDeclNGen_732_ = lean_ctor_get(v___x_728_, 3);
v_traceState_733_ = lean_ctor_get(v___x_728_, 4);
v_messages_734_ = lean_ctor_get(v___x_728_, 6);
v_infoState_735_ = lean_ctor_get(v___x_728_, 7);
v_snapshotTasks_736_ = lean_ctor_get(v___x_728_, 8);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v___x_728_, 5);
lean_dec(v_unused_746_);
v___x_738_ = v___x_728_;
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snapshotTasks_736_);
lean_inc(v_infoState_735_);
lean_inc(v_messages_734_);
lean_inc(v_traceState_733_);
lean_inc(v_auxDeclNGen_732_);
lean_inc(v_ngen_731_);
lean_inc(v_nextMacroScope_730_);
lean_inc(v_env_729_);
lean_dec(v___x_728_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = l_Lean_Kernel_enableDiag(v_env_729_, v___x_699_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 5, v___x_514_);
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_nextMacroScope_730_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_ngen_731_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_auxDeclNGen_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_traceState_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_744_, 6, v_messages_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 7, v_infoState_735_);
lean_ctor_set(v_reuseFailAlloc_744_, 8, v_snapshotTasks_736_);
v___x_742_ = v_reuseFailAlloc_744_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
v___x_743_ = lean_st_ref_put(v___y_447_, v___x_742_);
lean_inc(v_ref_532_);
lean_inc(v_currRecDepth_531_);
v_fileName_701_ = v_fileName_534_;
v_fileMap_702_ = v_fileMap_535_;
v_currNamespace_703_ = v_currNamespace_537_;
v_openDecls_704_ = v_openDecls_538_;
v_initHeartbeats_705_ = v_initHeartbeats_539_;
v_maxHeartbeats_706_ = v_maxHeartbeats_540_;
v_quotContext_707_ = v_quotContext_541_;
v_currMacroScope_708_ = v_currMacroScope_542_;
v_cancelTk_x3f_709_ = v_cancelTk_x3f_543_;
v_inheritedTraceOptions_710_ = v_inheritedTraceOptions_544_;
v_currRecDepth_711_ = v_currRecDepth_531_;
v_ref_712_ = v_ref_532_;
v_suppressElabErrors_713_ = v_suppressElabErrors_533_;
v___y_714_ = v___y_447_;
goto v___jp_700_;
}
}
}
else
{
lean_inc(v_ref_532_);
lean_inc(v_currRecDepth_531_);
v_fileName_701_ = v_fileName_534_;
v_fileMap_702_ = v_fileMap_535_;
v_currNamespace_703_ = v_currNamespace_537_;
v_openDecls_704_ = v_openDecls_538_;
v_initHeartbeats_705_ = v_initHeartbeats_539_;
v_maxHeartbeats_706_ = v_maxHeartbeats_540_;
v_quotContext_707_ = v_quotContext_541_;
v_currMacroScope_708_ = v_currMacroScope_542_;
v_cancelTk_x3f_709_ = v_cancelTk_x3f_543_;
v_inheritedTraceOptions_710_ = v_inheritedTraceOptions_544_;
v_currRecDepth_711_ = v_currRecDepth_531_;
v_ref_712_ = v_ref_532_;
v_suppressElabErrors_713_ = v_suppressElabErrors_533_;
v___y_714_ = v___y_447_;
goto v___jp_700_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v_tacticName_759_, lean_object* v___x_760_, lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v_a_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_nativeEqTrue___lam__0(v_tacticName_759_, v___x_760_, v___x_761_, v___x_762_, v_a_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(lean_object* v_stx_770_, lean_object* v___y_771_){
_start:
{
uint8_t v___x_773_; lean_object* v___x_774_; 
v___x_773_ = 0;
v___x_774_ = l_Lean_Syntax_getRange_x3f(v_stx_770_, v___x_773_);
if (lean_obj_tag(v___x_774_) == 1)
{
lean_object* v_toCold_775_; lean_object* v_val_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_788_; 
v_toCold_775_ = lean_ctor_get(v___y_771_, 0);
v_val_776_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_778_ = v___x_774_;
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_val_776_);
lean_dec(v___x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_fileMap_780_; lean_object* v_start_781_; lean_object* v_stop_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v_fileMap_780_ = lean_ctor_get(v_toCold_775_, 1);
v_start_781_ = lean_ctor_get(v_val_776_, 0);
lean_inc(v_start_781_);
v_stop_782_ = lean_ctor_get(v_val_776_, 1);
lean_inc(v_stop_782_);
lean_dec(v_val_776_);
lean_inc_ref(v_fileMap_780_);
v___x_783_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_780_, v_start_781_, v_stop_782_);
lean_dec(v_stop_782_);
lean_dec(v_start_781_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_783_);
v___x_785_ = v___x_778_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; 
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v___x_774_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg___boxed(lean_object* v_stx_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_stx_791_, v___y_792_);
lean_dec_ref(v___y_792_);
lean_dec(v_stx_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(lean_object* v_declName_795_, lean_object* v_declRanges_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = l_Lean_Name_isAnonymous(v_declName_795_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v_env_802_; lean_object* v_nextMacroScope_803_; lean_object* v_ngen_804_; lean_object* v_auxDeclNGen_805_; lean_object* v_traceState_806_; lean_object* v_messages_807_; lean_object* v_infoState_808_; lean_object* v_snapshotTasks_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_837_; 
v___x_801_ = lean_st_ref_take(v___y_798_);
v_env_802_ = lean_ctor_get(v___x_801_, 0);
v_nextMacroScope_803_ = lean_ctor_get(v___x_801_, 1);
v_ngen_804_ = lean_ctor_get(v___x_801_, 2);
v_auxDeclNGen_805_ = lean_ctor_get(v___x_801_, 3);
v_traceState_806_ = lean_ctor_get(v___x_801_, 4);
v_messages_807_ = lean_ctor_get(v___x_801_, 6);
v_infoState_808_ = lean_ctor_get(v___x_801_, 7);
v_snapshotTasks_809_ = lean_ctor_get(v___x_801_, 8);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v___x_801_, 5);
lean_dec(v_unused_838_);
v___x_811_ = v___x_801_;
v_isShared_812_ = v_isSharedCheck_837_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snapshotTasks_809_);
lean_inc(v_infoState_808_);
lean_inc(v_messages_807_);
lean_inc(v_traceState_806_);
lean_inc(v_auxDeclNGen_805_);
lean_inc(v_ngen_804_);
lean_inc(v_nextMacroScope_803_);
lean_inc(v_env_802_);
lean_dec(v___x_801_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_837_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_813_ = l_Lean_declRangeExt;
v___x_814_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_813_, v_env_802_, v_declName_795_, v_declRanges_796_);
v___x_815_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 5, v___x_815_);
lean_ctor_set(v___x_811_, 0, v___x_814_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_nextMacroScope_803_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_ngen_804_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_auxDeclNGen_805_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_traceState_806_);
lean_ctor_set(v_reuseFailAlloc_836_, 5, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_836_, 6, v_messages_807_);
lean_ctor_set(v_reuseFailAlloc_836_, 7, v_infoState_808_);
lean_ctor_set(v_reuseFailAlloc_836_, 8, v_snapshotTasks_809_);
v___x_817_ = v_reuseFailAlloc_836_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_mctx_820_; lean_object* v_zetaDeltaFVarIds_821_; lean_object* v_postponed_822_; lean_object* v_diag_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_834_; 
v___x_818_ = lean_st_ref_put(v___y_798_, v___x_817_);
v___x_819_ = lean_st_ref_take(v___y_797_);
v_mctx_820_ = lean_ctor_get(v___x_819_, 0);
v_zetaDeltaFVarIds_821_ = lean_ctor_get(v___x_819_, 2);
v_postponed_822_ = lean_ctor_get(v___x_819_, 3);
v_diag_823_ = lean_ctor_get(v___x_819_, 4);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_819_, 1);
lean_dec(v_unused_835_);
v___x_825_ = v___x_819_;
v_isShared_826_ = v_isSharedCheck_834_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_diag_823_);
lean_inc(v_postponed_822_);
lean_inc(v_zetaDeltaFVarIds_821_);
lean_inc(v_mctx_820_);
lean_dec(v___x_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_834_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_box(0);
v___x_828_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_mctx_820_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_zetaDeltaFVarIds_821_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_postponed_822_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_diag_823_);
v___x_830_ = v_reuseFailAlloc_833_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_st_ref_put(v___y_797_, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_827_);
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_declRanges_796_);
lean_dec(v_declName_795_);
v___x_839_ = lean_box(0);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg___boxed(lean_object* v_declName_841_, lean_object* v_declRanges_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_841_, v_declRanges_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(lean_object* v_declName_847_, lean_object* v_rangeStx_848_, lean_object* v_selectionRangeStx_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_872_; 
v___x_855_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_rangeStx_848_, v___y_852_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_872_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_872_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_872_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
if (lean_obj_tag(v_a_856_) == 1)
{
lean_object* v_val_860_; lean_object* v_a_862_; lean_object* v___x_865_; lean_object* v_a_866_; 
lean_del_object(v___x_858_);
v_val_860_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_a_856_, 1);
v___x_865_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_selectionRangeStx_849_, v___y_852_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
if (lean_obj_tag(v_a_866_) == 0)
{
lean_inc(v_val_860_);
v_a_862_ = v_val_860_;
goto v___jp_861_;
}
else
{
lean_object* v_val_867_; 
v_val_867_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v_a_866_, 1);
v_a_862_ = v_val_867_;
goto v___jp_861_;
}
v___jp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_val_860_);
lean_ctor_set(v___x_863_, 1, v_a_862_);
v___x_864_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_847_, v___x_863_, v___y_851_, v___y_853_);
return v___x_864_;
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec(v_a_856_);
lean_dec(v_declName_847_);
v___x_868_ = lean_box(0);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_868_);
v___x_870_ = v___x_858_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9___boxed(lean_object* v_declName_873_, lean_object* v_rangeStx_874_, lean_object* v_selectionRangeStx_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_declName_873_, v_rangeStx_874_, v_selectionRangeStx_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_selectionRangeStx_875_);
lean_dec(v_rangeStx_874_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
if (lean_obj_tag(v_a_882_) == 0)
{
lean_object* v___x_884_; 
v___x_884_ = l_List_reverse___redArg(v_a_883_);
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_895_; 
v_head_885_ = lean_ctor_get(v_a_882_, 0);
v_tail_886_ = lean_ctor_get(v_a_882_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_895_ == 0)
{
v___x_888_ = v_a_882_;
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_tail_886_);
lean_inc(v_head_885_);
lean_dec(v_a_882_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = l_Lean_mkLevelParam(v_head_885_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_a_883_);
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_a_883_);
v___x_892_ = v_reuseFailAlloc_894_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
v_a_882_ = v_tail_886_;
v_a_883_ = v___x_892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(lean_object* v_env_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; lean_object* v_nextMacroScope_901_; lean_object* v_ngen_902_; lean_object* v_auxDeclNGen_903_; lean_object* v_traceState_904_; lean_object* v_messages_905_; lean_object* v_infoState_906_; lean_object* v_snapshotTasks_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_933_; 
v___x_900_ = lean_st_ref_take(v___y_898_);
v_nextMacroScope_901_ = lean_ctor_get(v___x_900_, 1);
v_ngen_902_ = lean_ctor_get(v___x_900_, 2);
v_auxDeclNGen_903_ = lean_ctor_get(v___x_900_, 3);
v_traceState_904_ = lean_ctor_get(v___x_900_, 4);
v_messages_905_ = lean_ctor_get(v___x_900_, 6);
v_infoState_906_ = lean_ctor_get(v___x_900_, 7);
v_snapshotTasks_907_ = lean_ctor_get(v___x_900_, 8);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_934_ = lean_ctor_get(v___x_900_, 5);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v___x_900_, 0);
lean_dec(v_unused_935_);
v___x_909_ = v___x_900_;
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snapshotTasks_907_);
lean_inc(v_infoState_906_);
lean_inc(v_messages_905_);
lean_inc(v_traceState_904_);
lean_inc(v_auxDeclNGen_903_);
lean_inc(v_ngen_902_);
lean_inc(v_nextMacroScope_901_);
lean_dec(v___x_900_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 5, v___x_911_);
lean_ctor_set(v___x_909_, 0, v_env_896_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_env_896_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_nextMacroScope_901_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_ngen_902_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_auxDeclNGen_903_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_traceState_904_);
lean_ctor_set(v_reuseFailAlloc_932_, 5, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_932_, 6, v_messages_905_);
lean_ctor_set(v_reuseFailAlloc_932_, 7, v_infoState_906_);
lean_ctor_set(v_reuseFailAlloc_932_, 8, v_snapshotTasks_907_);
v___x_913_ = v_reuseFailAlloc_932_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_mctx_916_; lean_object* v_zetaDeltaFVarIds_917_; lean_object* v_postponed_918_; lean_object* v_diag_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_930_; 
v___x_914_ = lean_st_ref_put(v___y_898_, v___x_913_);
v___x_915_ = lean_st_ref_take(v___y_897_);
v_mctx_916_ = lean_ctor_get(v___x_915_, 0);
v_zetaDeltaFVarIds_917_ = lean_ctor_get(v___x_915_, 2);
v_postponed_918_ = lean_ctor_get(v___x_915_, 3);
v_diag_919_ = lean_ctor_get(v___x_915_, 4);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_915_, 1);
lean_dec(v_unused_931_);
v___x_921_ = v___x_915_;
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_diag_919_);
lean_inc(v_postponed_918_);
lean_inc(v_zetaDeltaFVarIds_917_);
lean_inc(v_mctx_916_);
lean_dec(v___x_915_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = lean_box(0);
v___x_924_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_mctx_916_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_zetaDeltaFVarIds_917_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_postponed_918_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_diag_919_);
v___x_926_ = v_reuseFailAlloc_929_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_st_ref_put(v___y_897_, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_923_);
return v___x_928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg___boxed(lean_object* v_env_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(lean_object* v_env_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_env_949_; lean_object* v_a_951_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_948_ = lean_st_ref_get(v___y_946_);
v_env_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_ref(v_env_949_);
lean_dec(v___x_948_);
v___x_961_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_941_, v___y_944_, v___y_946_);
lean_dec_ref(v___x_961_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
v___x_962_ = lean_apply_5(v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, lean_box(0));
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_949_, v___y_944_, v___y_946_);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v___x_964_, 0);
lean_dec(v_unused_972_);
v___x_966_ = v___x_964_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_dec(v___x_964_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_a_963_);
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_963_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_973_; 
v_a_973_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_962_, 1);
v_a_951_ = v_a_973_;
goto v___jp_950_;
}
v___jp_950_:
{
lean_object* v___x_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v___x_952_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_949_, v___y_944_, v___y_946_);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_960_);
v___x_954_ = v___x_952_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_dec(v___x_952_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 1);
lean_ctor_set(v___x_954_, 0, v_a_951_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_951_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg___boxed(lean_object* v_env_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_974_, v_x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_981_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = lean_unsigned_to_nat(16u);
v___x_984_ = lean_mk_array(v___x_983_, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_985_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_991_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_ctor_set(v___x_992_, 2, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = l_Lean_Level_ofNat(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_1011_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_1012_ = l_Lean_mkConst(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_1015_ = l_Lean_mkConst(v___x_1014_, v___x_1013_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_1022_ = l_Lean_mkConst(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_1029_, lean_object* v_e_1030_, lean_object* v_axiomDeclRange_x3f_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___x_1045_; lean_object* v_a_1046_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; uint8_t v___x_1152_; 
v___x_1045_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_1030_, v_a_1033_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v___x_1045_);
v___x_1152_ = l_Lean_Expr_hasFVar(v_a_1046_);
if (v___x_1152_ == 0)
{
v___y_1131_ = v_a_1032_;
v___y_1132_ = v_a_1033_;
v___y_1133_ = v_a_1034_;
v___y_1134_ = v_a_1035_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v___x_1153_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1154_ = l_Lean_MessageData_ofName(v_tacticName_1029_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_indentExpr(v_a_1046_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1159_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
v___jp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(v___y_1038_, v___x_1040_);
v___x_1042_ = l_Lean_mkConst(v___y_1039_, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
v___jp_1047_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_params_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1127_; 
v___x_1052_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1046_);
v___x_1053_ = l_Lean_collectLevelParams(v___x_1052_, v_a_1046_);
v_params_1054_ = lean_ctor_get(v___x_1053_, 2);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; lean_object* v_unused_1129_; 
v_unused_1128_ = lean_ctor_get(v___x_1053_, 1);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v___x_1053_, 0);
lean_dec(v_unused_1129_);
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1127_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_params_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1127_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v_env_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_array_to_list(v_params_1054_);
v___x_1060_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_1029_);
v___x_1061_ = l_Lean_Name_append(v___x_1060_, v_tacticName_1029_);
v___x_1062_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1061_);
v___x_1063_ = l_Lean_Name_append(v___x_1061_, v___x_1062_);
lean_inc(v_a_1046_);
lean_inc(v___x_1059_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1064_, 0, v_tacticName_1029_);
lean_closure_set(v___f_1064_, 1, v___x_1063_);
lean_closure_set(v___f_1064_, 2, v___x_1059_);
lean_closure_set(v___f_1064_, 3, v___x_1058_);
lean_closure_set(v___f_1064_, 4, v_a_1046_);
v___x_1065_ = lean_st_ref_get(v___y_1051_);
v_env_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc_ref(v_env_1066_);
lean_dec(v___x_1065_);
v___x_1067_ = l_Lean_Environment_unlockAsync(v_env_1066_);
v___x_1068_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v___x_1067_, v___f_1064_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1118_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1118_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1118_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_unbox(v_a_1069_);
lean_dec(v_a_1069_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_dec(v___x_1061_);
lean_dec(v___x_1059_);
lean_del_object(v___x_1056_);
lean_dec(v_a_1046_);
v___x_1074_ = lean_box(1);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1117_; 
lean_del_object(v___x_1071_);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1079_ = l_Lean_Name_append(v___x_1061_, v___x_1078_);
v___x_1080_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1079_, v___y_1051_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1117_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1117_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1085_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1086_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1087_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1088_ = l_Lean_mkApp3(v___x_1085_, v___x_1086_, v_a_1046_, v___x_1087_);
lean_inc(v___x_1059_);
lean_inc(v_a_1081_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 2, v___x_1088_);
lean_ctor_set(v___x_1056_, 1, v___x_1059_);
lean_ctor_set(v___x_1056_, 0, v_a_1081_);
v___x_1090_ = v___x_1056_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1081_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1091_ = 0;
v___x_1092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_1091_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1092_);
v___x_1094_ = v___x_1083_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_addDecl(v___x_1094_, v___x_1091_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref_known(v___x_1095_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1031_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_val_1096_ = lean_ctor_get(v_axiomDeclRange_x3f_1031_, 0);
v___x_1097_ = lean_box(0);
lean_inc(v_a_1081_);
v___x_1098_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_a_1081_, v_val_1096_, v___x_1097_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref_known(v___x_1098_, 1);
v___y_1038_ = v___x_1059_;
v___y_1039_ = v_a_1081_;
goto v___jp_1037_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_a_1081_);
lean_dec(v___x_1059_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
v___y_1038_ = v___x_1059_;
v___y_1039_ = v_a_1081_;
goto v___jp_1037_;
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v_a_1081_);
lean_dec(v___x_1059_);
v_a_1107_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1095_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1095_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
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
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v___x_1061_);
lean_dec(v___x_1059_);
lean_del_object(v___x_1056_);
lean_dec(v_a_1046_);
v_a_1119_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1068_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1068_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
v___jp_1130_:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_Expr_hasMVar(v_a_1046_);
if (v___x_1135_ == 0)
{
v___y_1048_ = v___y_1131_;
v___y_1049_ = v___y_1132_;
v___y_1050_ = v___y_1133_;
v___y_1051_ = v___y_1134_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
v___x_1136_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1137_ = l_Lean_MessageData_ofName(v_tacticName_1029_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_indentExpr(v_a_1046_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1142_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1169_, lean_object* v_e_1170_, lean_object* v_axiomDeclRange_x3f_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1169_, v_e_1170_, v_axiomDeclRange_x3f_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_axiomDeclRange_x3f_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1192_, lean_object* v_constName_1193_, uint8_t v_checkMeta_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1193_, v_checkMeta_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_constName_1202_, lean_object* v_checkMeta_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_checkMeta_boxed_1209_; lean_object* v_res_1210_; 
v_checkMeta_boxed_1209_ = lean_unbox(v_checkMeta_1203_);
v_res_1210_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1201_, v_constName_1202_, v_checkMeta_boxed_1209_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1219_, v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11(lean_object* v_env_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_1227_, v___y_1229_, v___y_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___boxed(lean_object* v_env_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11(v_env_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_00_u03b1_1241_, lean_object* v_env_1242_, lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_1242_, v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_env_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(v_00_u03b1_1250_, v_env_1251_, v_x_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14(lean_object* v_stx_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_stx_1259_, v___y_1262_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___boxed(lean_object* v_stx_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14(v_stx_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v_stx_1266_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(lean_object* v_declName_1273_, lean_object* v_declRanges_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_1273_, v_declRanges_1274_, v___y_1276_, v___y_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___boxed(lean_object* v_declName_1281_, lean_object* v_declRanges_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(v_declName_1281_, v_declRanges_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1297_, v_x_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1304_;
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

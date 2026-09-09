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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__12_value;
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19_value)} };
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
v___x_38_ = l_instMonadEIO(lean_box(0));
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
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_toMonadRef_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_22__overap_131_; lean_object* v___x_132_; 
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
v___x_22__overap_131_ = l_Lean_evalConst___redArg(v___x_121_, v___x_122_, v___x_128_, v___x_129_, v_auxDeclName_76_, v___x_130_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
v___x_132_ = lean_apply_5(v___x_22__overap_131_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, lean_box(0));
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
v___x_432_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v_tacticName_442_, lean_object* v_a_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; lean_object* v___x_461_; lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_767_; 
v___x_461_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_439_, v___y_447_);
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_767_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_767_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_767_;
goto v_resetjp_463_;
}
v___jp_449_:
{
if (v___y_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v___y_450_);
v___x_453_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_454_ = l_Lean_MessageData_ofName(v_tacticName_442_);
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
lean_dec(v_tacticName_442_);
return v___y_450_;
}
}
v_resetjp_463_:
{
lean_object* v___y_467_; lean_object* v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; lean_object* v___x_493_; lean_object* v_env_494_; lean_object* v_nextMacroScope_495_; lean_object* v_ngen_496_; lean_object* v_auxDeclNGen_497_; lean_object* v_traceState_498_; lean_object* v_messages_499_; lean_object* v_infoState_500_; lean_object* v_snapshotTasks_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_765_; 
v___x_493_ = lean_st_ref_take(v___y_447_);
v_env_494_ = lean_ctor_get(v___x_493_, 0);
v_nextMacroScope_495_ = lean_ctor_get(v___x_493_, 1);
v_ngen_496_ = lean_ctor_get(v___x_493_, 2);
v_auxDeclNGen_497_ = lean_ctor_get(v___x_493_, 3);
v_traceState_498_ = lean_ctor_get(v___x_493_, 4);
v_messages_499_ = lean_ctor_get(v___x_493_, 6);
v_infoState_500_ = lean_ctor_get(v___x_493_, 7);
v_snapshotTasks_501_ = lean_ctor_get(v___x_493_, 8);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_493_, 5);
lean_dec(v_unused_766_);
v___x_503_ = v___x_493_;
v_isShared_504_ = v_isSharedCheck_765_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_snapshotTasks_501_);
lean_inc(v_infoState_500_);
lean_inc(v_messages_499_);
lean_inc(v_traceState_498_);
lean_inc(v_auxDeclNGen_497_);
lean_inc(v_ngen_496_);
lean_inc(v_nextMacroScope_495_);
lean_inc(v_env_494_);
lean_dec(v___x_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_765_;
goto v_resetjp_502_;
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
lean_dec(v_tacticName_442_);
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
lean_dec(v_tacticName_442_);
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
lean_dec_ref(v___y_482_);
v___x_485_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_442_);
v___x_486_ = l_Lean_MessageData_ofName(v_tacticName_442_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_Exception_toMessageData(v___y_483_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_491_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
v___y_467_ = v___x_492_;
goto v___jp_466_;
}
else
{
lean_dec_ref(v___y_483_);
v___y_467_ = v___y_482_;
goto v___jp_466_;
}
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_505_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_462_, 3);
v___x_506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_506_, 0, v_a_462_);
lean_ctor_set(v___x_506_, 1, v___x_440_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v_a_462_);
lean_ctor_set(v___x_507_, 1, v___x_441_);
v___x_508_ = l_Lean_markMeta(v_env_494_, v_a_462_);
v___x_509_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 5, v___x_509_);
lean_ctor_set(v___x_503_, 0, v___x_508_);
v___x_511_ = v___x_503_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_nextMacroScope_495_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_ngen_496_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_auxDeclNGen_497_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_traceState_498_);
lean_ctor_set(v_reuseFailAlloc_764_, 5, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_764_, 6, v_messages_499_);
lean_ctor_set(v_reuseFailAlloc_764_, 7, v_infoState_500_);
lean_ctor_set(v_reuseFailAlloc_764_, 8, v_snapshotTasks_501_);
v___x_511_ = v_reuseFailAlloc_764_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_mctx_514_; lean_object* v_zetaDeltaFVarIds_515_; lean_object* v_postponed_516_; lean_object* v_diag_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_762_; 
v___x_512_ = lean_st_ref_put(v___y_447_, v___x_511_);
v___x_513_ = lean_st_ref_take(v___y_445_);
v_mctx_514_ = lean_ctor_get(v___x_513_, 0);
v_zetaDeltaFVarIds_515_ = lean_ctor_get(v___x_513_, 2);
v_postponed_516_ = lean_ctor_get(v___x_513_, 3);
v_diag_517_ = lean_ctor_get(v___x_513_, 4);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_513_, 1);
lean_dec(v_unused_763_);
v___x_519_ = v___x_513_;
v_isShared_520_ = v_isSharedCheck_762_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_diag_517_);
lean_inc(v_postponed_516_);
lean_inc(v_zetaDeltaFVarIds_515_);
lean_inc(v_mctx_514_);
lean_dec(v___x_513_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_762_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_mctx_514_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_zetaDeltaFVarIds_515_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_postponed_516_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_diag_517_);
v___x_523_ = v_reuseFailAlloc_761_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_toCold_526_; lean_object* v_options_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_749_; 
v___x_524_ = lean_st_ref_put(v___y_445_, v___x_523_);
v___x_525_ = lean_st_ref_get(v___y_447_);
v_toCold_526_ = lean_ctor_get(v___y_446_, 0);
lean_inc_ref(v_toCold_526_);
v_options_527_ = lean_ctor_get(v_toCold_526_, 2);
v_isSharedCheck_749_ = !lean_is_exclusive(v_toCold_526_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; lean_object* v_unused_755_; lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; 
v_unused_750_ = lean_ctor_get(v_toCold_526_, 11);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_toCold_526_, 10);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_toCold_526_, 9);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_toCold_526_, 8);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_toCold_526_, 7);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_toCold_526_, 6);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_toCold_526_, 5);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_toCold_526_, 4);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_toCold_526_, 3);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_toCold_526_, 1);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_toCold_526_, 0);
lean_dec(v_unused_760_);
v___x_529_ = v_toCold_526_;
v_isShared_530_ = v_isSharedCheck_749_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_options_527_);
lean_dec(v_toCold_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_749_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_env_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v_env_531_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_525_);
v___x_532_ = lean_box(1);
v___x_533_ = 1;
v___x_534_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_534_, 0, v___x_506_);
lean_ctor_set(v___x_534_, 1, v_a_443_);
lean_ctor_set(v___x_534_, 2, v___x_532_);
lean_ctor_set(v___x_534_, 3, v___x_507_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*4, v___x_533_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 1);
lean_ctor_set(v___x_464_, 0, v___x_534_);
v___x_536_ = v___x_464_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_748_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
uint8_t v___x_537_; uint8_t v___x_538_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v_fileName_543_; lean_object* v_fileMap_544_; lean_object* v_currNamespace_545_; lean_object* v_openDecls_546_; lean_object* v_initHeartbeats_547_; lean_object* v_maxHeartbeats_548_; lean_object* v_quotContext_549_; lean_object* v_currMacroScope_550_; lean_object* v_cancelTk_x3f_551_; lean_object* v_inheritedTraceOptions_552_; lean_object* v_currRecDepth_553_; lean_object* v_ref_554_; uint8_t v_suppressElabErrors_555_; lean_object* v___y_556_; lean_object* v___y_567_; lean_object* v___y_568_; uint8_t v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; uint8_t v___y_591_; uint8_t v___y_592_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; uint8_t v___y_664_; uint8_t v___x_684_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___y_727_; uint8_t v___x_747_; 
v___x_537_ = 1;
v___x_538_ = 0;
v___x_612_ = l_Lean_Elab_async;
v___x_613_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v_options_527_, v___x_612_, v___x_538_);
v___x_614_ = l_Lean_diagnostics;
v___x_684_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_613_, v___x_614_);
v___x_747_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_531_);
lean_dec_ref(v_env_531_);
if (v___x_684_ == 0)
{
if (v___x_747_ == 0)
{
lean_inc_ref(v___y_446_);
v___y_686_ = v___y_446_;
v___y_687_ = v___y_447_;
goto v___jp_685_;
}
else
{
v___y_727_ = v___x_684_;
goto v___jp_726_;
}
}
else
{
v___y_727_ = v___x_747_;
goto v___jp_726_;
}
v___jp_539_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_540_, v___y_541_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 11, v_inheritedTraceOptions_552_);
lean_ctor_set(v___x_529_, 10, v_cancelTk_x3f_551_);
lean_ctor_set(v___x_529_, 9, v_currMacroScope_550_);
lean_ctor_set(v___x_529_, 8, v_quotContext_549_);
lean_ctor_set(v___x_529_, 7, v_maxHeartbeats_548_);
lean_ctor_set(v___x_529_, 6, v_initHeartbeats_547_);
lean_ctor_set(v___x_529_, 5, v_openDecls_546_);
lean_ctor_set(v___x_529_, 4, v_currNamespace_545_);
lean_ctor_set(v___x_529_, 3, v___x_557_);
lean_ctor_set(v___x_529_, 2, v___y_540_);
lean_ctor_set(v___x_529_, 1, v_fileMap_544_);
lean_ctor_set(v___x_529_, 0, v_fileName_543_);
v___x_559_ = v___x_529_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_fileName_543_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_fileMap_544_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v___y_540_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_currNamespace_545_);
lean_ctor_set(v_reuseFailAlloc_565_, 5, v_openDecls_546_);
lean_ctor_set(v_reuseFailAlloc_565_, 6, v_initHeartbeats_547_);
lean_ctor_set(v_reuseFailAlloc_565_, 7, v_maxHeartbeats_548_);
lean_ctor_set(v_reuseFailAlloc_565_, 8, v_quotContext_549_);
lean_ctor_set(v_reuseFailAlloc_565_, 9, v_currMacroScope_550_);
lean_ctor_set(v_reuseFailAlloc_565_, 10, v_cancelTk_x3f_551_);
lean_ctor_set(v_reuseFailAlloc_565_, 11, v_inheritedTraceOptions_552_);
v___x_559_ = v_reuseFailAlloc_565_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_currRecDepth_553_);
lean_ctor_set(v___x_560_, 2, v_ref_554_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3, v___y_542_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3 + 1, v_suppressElabErrors_555_);
v___x_561_ = l_Lean_addAndCompile(v___x_536_, v___x_537_, v___x_538_, v___x_560_, v___y_556_);
lean_dec_ref_known(v___x_560_, 3);
if (lean_obj_tag(v___x_561_) == 0)
{
v___y_467_ = v___x_561_;
goto v___jp_466_;
}
else
{
lean_object* v_a_562_; uint8_t v___x_563_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
v___x_563_ = l_Lean_Exception_isInterrupt(v_a_562_);
if (v___x_563_ == 0)
{
uint8_t v___x_564_; 
lean_inc(v_a_562_);
v___x_564_ = l_Lean_Exception_isRuntime(v_a_562_);
v___y_482_ = v___x_561_;
v___y_483_ = v_a_562_;
v___y_484_ = v___x_564_;
goto v___jp_481_;
}
else
{
v___y_482_ = v___x_561_;
v___y_483_ = v_a_562_;
v___y_484_ = v___x_563_;
goto v___jp_481_;
}
}
}
}
v___jp_566_:
{
lean_object* v_toCold_572_; lean_object* v_currRecDepth_573_; lean_object* v_ref_574_; uint8_t v_suppressElabErrors_575_; lean_object* v_fileName_576_; lean_object* v_fileMap_577_; lean_object* v_currNamespace_578_; lean_object* v_openDecls_579_; lean_object* v_initHeartbeats_580_; lean_object* v_maxHeartbeats_581_; lean_object* v_quotContext_582_; lean_object* v_currMacroScope_583_; lean_object* v_cancelTk_x3f_584_; lean_object* v_inheritedTraceOptions_585_; 
v_toCold_572_ = lean_ctor_get(v___y_570_, 0);
lean_inc_ref(v_toCold_572_);
v_currRecDepth_573_ = lean_ctor_get(v___y_570_, 1);
lean_inc(v_currRecDepth_573_);
v_ref_574_ = lean_ctor_get(v___y_570_, 2);
lean_inc(v_ref_574_);
v_suppressElabErrors_575_ = lean_ctor_get_uint8(v___y_570_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_570_);
v_fileName_576_ = lean_ctor_get(v_toCold_572_, 0);
lean_inc_ref(v_fileName_576_);
v_fileMap_577_ = lean_ctor_get(v_toCold_572_, 1);
lean_inc_ref(v_fileMap_577_);
v_currNamespace_578_ = lean_ctor_get(v_toCold_572_, 4);
lean_inc(v_currNamespace_578_);
v_openDecls_579_ = lean_ctor_get(v_toCold_572_, 5);
lean_inc(v_openDecls_579_);
v_initHeartbeats_580_ = lean_ctor_get(v_toCold_572_, 6);
lean_inc(v_initHeartbeats_580_);
v_maxHeartbeats_581_ = lean_ctor_get(v_toCold_572_, 7);
lean_inc(v_maxHeartbeats_581_);
v_quotContext_582_ = lean_ctor_get(v_toCold_572_, 8);
lean_inc(v_quotContext_582_);
v_currMacroScope_583_ = lean_ctor_get(v_toCold_572_, 9);
lean_inc(v_currMacroScope_583_);
v_cancelTk_x3f_584_ = lean_ctor_get(v_toCold_572_, 10);
lean_inc(v_cancelTk_x3f_584_);
v_inheritedTraceOptions_585_ = lean_ctor_get(v_toCold_572_, 11);
lean_inc_ref(v_inheritedTraceOptions_585_);
lean_dec_ref(v_toCold_572_);
v___y_540_ = v___y_567_;
v___y_541_ = v___y_568_;
v___y_542_ = v___y_569_;
v_fileName_543_ = v_fileName_576_;
v_fileMap_544_ = v_fileMap_577_;
v_currNamespace_545_ = v_currNamespace_578_;
v_openDecls_546_ = v_openDecls_579_;
v_initHeartbeats_547_ = v_initHeartbeats_580_;
v_maxHeartbeats_548_ = v_maxHeartbeats_581_;
v_quotContext_549_ = v_quotContext_582_;
v_currMacroScope_550_ = v_currMacroScope_583_;
v_cancelTk_x3f_551_ = v_cancelTk_x3f_584_;
v_inheritedTraceOptions_552_ = v_inheritedTraceOptions_585_;
v_currRecDepth_553_ = v_currRecDepth_573_;
v_ref_554_ = v_ref_574_;
v_suppressElabErrors_555_ = v_suppressElabErrors_575_;
v___y_556_ = v___y_571_;
goto v___jp_539_;
}
v___jp_586_:
{
if (v___y_592_ == 0)
{
lean_object* v___x_593_; lean_object* v_env_594_; lean_object* v_nextMacroScope_595_; lean_object* v_ngen_596_; lean_object* v_auxDeclNGen_597_; lean_object* v_traceState_598_; lean_object* v_messages_599_; lean_object* v_infoState_600_; lean_object* v_snapshotTasks_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_610_; 
v___x_593_ = lean_st_ref_take(v___y_587_);
v_env_594_ = lean_ctor_get(v___x_593_, 0);
v_nextMacroScope_595_ = lean_ctor_get(v___x_593_, 1);
v_ngen_596_ = lean_ctor_get(v___x_593_, 2);
v_auxDeclNGen_597_ = lean_ctor_get(v___x_593_, 3);
v_traceState_598_ = lean_ctor_get(v___x_593_, 4);
v_messages_599_ = lean_ctor_get(v___x_593_, 6);
v_infoState_600_ = lean_ctor_get(v___x_593_, 7);
v_snapshotTasks_601_ = lean_ctor_get(v___x_593_, 8);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_593_, 5);
lean_dec(v_unused_611_);
v___x_603_ = v___x_593_;
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snapshotTasks_601_);
lean_inc(v_infoState_600_);
lean_inc(v_messages_599_);
lean_inc(v_traceState_598_);
lean_inc(v_auxDeclNGen_597_);
lean_inc(v_ngen_596_);
lean_inc(v_nextMacroScope_595_);
lean_inc(v_env_594_);
lean_dec(v___x_593_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_Kernel_enableDiag(v_env_594_, v___y_591_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 5, v___x_509_);
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_nextMacroScope_595_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_ngen_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_auxDeclNGen_597_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_traceState_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_messages_599_);
lean_ctor_set(v_reuseFailAlloc_609_, 7, v_infoState_600_);
lean_ctor_set(v_reuseFailAlloc_609_, 8, v_snapshotTasks_601_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = lean_st_ref_put(v___y_587_, v___x_607_);
v___y_567_ = v___y_589_;
v___y_568_ = v___y_590_;
v___y_569_ = v___y_591_;
v___y_570_ = v___y_588_;
v___y_571_ = v___y_587_;
goto v___jp_566_;
}
}
}
else
{
v___y_567_ = v___y_589_;
v___y_568_ = v___y_590_;
v___y_569_ = v___y_591_;
v___y_570_ = v___y_588_;
v___y_571_ = v___y_587_;
goto v___jp_566_;
}
}
v___jp_615_:
{
lean_object* v___x_621_; lean_object* v_toCold_622_; lean_object* v_currRecDepth_623_; lean_object* v_ref_624_; uint8_t v_suppressElabErrors_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_657_; 
v___x_621_ = lean_st_ref_get(v___y_620_);
v_toCold_622_ = lean_ctor_get(v___y_619_, 0);
v_currRecDepth_623_ = lean_ctor_get(v___y_619_, 1);
v_ref_624_ = lean_ctor_get(v___y_619_, 2);
v_suppressElabErrors_625_ = lean_ctor_get_uint8(v___y_619_, sizeof(void*)*3 + 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___y_619_);
if (v_isSharedCheck_657_ == 0)
{
v___x_627_ = v___y_619_;
v_isShared_628_ = v_isSharedCheck_657_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_ref_624_);
lean_inc(v_currRecDepth_623_);
lean_inc(v_toCold_622_);
lean_dec(v___y_619_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_657_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_fileName_629_; lean_object* v_fileMap_630_; lean_object* v_currNamespace_631_; lean_object* v_openDecls_632_; lean_object* v_initHeartbeats_633_; lean_object* v_maxHeartbeats_634_; lean_object* v_quotContext_635_; lean_object* v_currMacroScope_636_; lean_object* v_cancelTk_x3f_637_; lean_object* v_inheritedTraceOptions_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_654_; 
v_fileName_629_ = lean_ctor_get(v_toCold_622_, 0);
v_fileMap_630_ = lean_ctor_get(v_toCold_622_, 1);
v_currNamespace_631_ = lean_ctor_get(v_toCold_622_, 4);
v_openDecls_632_ = lean_ctor_get(v_toCold_622_, 5);
v_initHeartbeats_633_ = lean_ctor_get(v_toCold_622_, 6);
v_maxHeartbeats_634_ = lean_ctor_get(v_toCold_622_, 7);
v_quotContext_635_ = lean_ctor_get(v_toCold_622_, 8);
v_currMacroScope_636_ = lean_ctor_get(v_toCold_622_, 9);
v_cancelTk_x3f_637_ = lean_ctor_get(v_toCold_622_, 10);
v_inheritedTraceOptions_638_ = lean_ctor_get(v_toCold_622_, 11);
v_isSharedCheck_654_ = !lean_is_exclusive(v_toCold_622_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_655_ = lean_ctor_get(v_toCold_622_, 3);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_toCold_622_, 2);
lean_dec(v_unused_656_);
v___x_640_ = v_toCold_622_;
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_inheritedTraceOptions_638_);
lean_inc(v_cancelTk_x3f_637_);
lean_inc(v_currMacroScope_636_);
lean_inc(v_quotContext_635_);
lean_inc(v_maxHeartbeats_634_);
lean_inc(v_initHeartbeats_633_);
lean_inc(v_openDecls_632_);
lean_inc(v_currNamespace_631_);
lean_inc(v_fileMap_630_);
lean_inc(v_fileName_629_);
lean_dec(v_toCold_622_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_env_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v_env_642_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref(v_env_642_);
lean_dec(v___x_621_);
v___x_643_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_618_, v___y_617_);
lean_inc_ref(v_inheritedTraceOptions_638_);
lean_inc(v_cancelTk_x3f_637_);
lean_inc(v_currMacroScope_636_);
lean_inc(v_quotContext_635_);
lean_inc(v_maxHeartbeats_634_);
lean_inc(v_initHeartbeats_633_);
lean_inc(v_openDecls_632_);
lean_inc(v_currNamespace_631_);
lean_inc_ref(v___y_618_);
lean_inc_ref(v_fileMap_630_);
lean_inc_ref(v_fileName_629_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 3, v___x_643_);
lean_ctor_set(v___x_640_, 2, v___y_618_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fileName_629_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_fileMap_630_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v___y_618_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_currNamespace_631_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v_openDecls_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 6, v_initHeartbeats_633_);
lean_ctor_set(v_reuseFailAlloc_653_, 7, v_maxHeartbeats_634_);
lean_ctor_set(v_reuseFailAlloc_653_, 8, v_quotContext_635_);
lean_ctor_set(v_reuseFailAlloc_653_, 9, v_currMacroScope_636_);
lean_ctor_set(v_reuseFailAlloc_653_, 10, v_cancelTk_x3f_637_);
lean_ctor_set(v_reuseFailAlloc_653_, 11, v_inheritedTraceOptions_638_);
v___x_645_ = v_reuseFailAlloc_653_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
lean_inc(v_ref_624_);
lean_inc(v_currRecDepth_623_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_645_);
v___x_647_ = v___x_627_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_currRecDepth_623_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_ref_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_652_, sizeof(void*)*3 + 1, v_suppressElabErrors_625_);
v___x_647_ = v_reuseFailAlloc_652_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; uint8_t v___x_651_; 
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*3, v___y_616_);
v___x_648_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_649_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_618_, v___x_648_, v___x_537_);
v___x_650_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_649_, v___x_614_);
v___x_651_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_642_);
lean_dec_ref(v_env_642_);
if (v___x_650_ == 0)
{
if (v___x_651_ == 0)
{
lean_dec_ref(v___x_647_);
v___y_540_ = v___x_649_;
v___y_541_ = v___y_617_;
v___y_542_ = v___x_650_;
v_fileName_543_ = v_fileName_629_;
v_fileMap_544_ = v_fileMap_630_;
v_currNamespace_545_ = v_currNamespace_631_;
v_openDecls_546_ = v_openDecls_632_;
v_initHeartbeats_547_ = v_initHeartbeats_633_;
v_maxHeartbeats_548_ = v_maxHeartbeats_634_;
v_quotContext_549_ = v_quotContext_635_;
v_currMacroScope_550_ = v_currMacroScope_636_;
v_cancelTk_x3f_551_ = v_cancelTk_x3f_637_;
v_inheritedTraceOptions_552_ = v_inheritedTraceOptions_638_;
v_currRecDepth_553_ = v_currRecDepth_623_;
v_ref_554_ = v_ref_624_;
v_suppressElabErrors_555_ = v_suppressElabErrors_625_;
v___y_556_ = v___y_620_;
goto v___jp_539_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_638_);
lean_dec(v_cancelTk_x3f_637_);
lean_dec(v_currMacroScope_636_);
lean_dec(v_quotContext_635_);
lean_dec(v_maxHeartbeats_634_);
lean_dec(v_initHeartbeats_633_);
lean_dec(v_openDecls_632_);
lean_dec(v_currNamespace_631_);
lean_dec_ref(v_fileMap_630_);
lean_dec_ref(v_fileName_629_);
lean_dec(v_ref_624_);
lean_dec(v_currRecDepth_623_);
v___y_587_ = v___y_620_;
v___y_588_ = v___x_647_;
v___y_589_ = v___x_649_;
v___y_590_ = v___y_617_;
v___y_591_ = v___x_650_;
v___y_592_ = v___x_650_;
goto v___jp_586_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_638_);
lean_dec(v_cancelTk_x3f_637_);
lean_dec(v_currMacroScope_636_);
lean_dec(v_quotContext_635_);
lean_dec(v_maxHeartbeats_634_);
lean_dec(v_initHeartbeats_633_);
lean_dec(v_openDecls_632_);
lean_dec(v_currNamespace_631_);
lean_dec_ref(v_fileMap_630_);
lean_dec_ref(v_fileName_629_);
lean_dec(v_ref_624_);
lean_dec(v_currRecDepth_623_);
v___y_587_ = v___y_620_;
v___y_588_ = v___x_647_;
v___y_589_ = v___x_649_;
v___y_590_ = v___y_617_;
v___y_591_ = v___x_650_;
v___y_592_ = v___x_651_;
goto v___jp_586_;
}
}
}
}
}
}
v___jp_658_:
{
if (v___y_664_ == 0)
{
lean_object* v___x_665_; lean_object* v_env_666_; lean_object* v_nextMacroScope_667_; lean_object* v_ngen_668_; lean_object* v_auxDeclNGen_669_; lean_object* v_traceState_670_; lean_object* v_messages_671_; lean_object* v_infoState_672_; lean_object* v_snapshotTasks_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_682_; 
v___x_665_ = lean_st_ref_take(v___y_663_);
v_env_666_ = lean_ctor_get(v___x_665_, 0);
v_nextMacroScope_667_ = lean_ctor_get(v___x_665_, 1);
v_ngen_668_ = lean_ctor_get(v___x_665_, 2);
v_auxDeclNGen_669_ = lean_ctor_get(v___x_665_, 3);
v_traceState_670_ = lean_ctor_get(v___x_665_, 4);
v_messages_671_ = lean_ctor_get(v___x_665_, 6);
v_infoState_672_ = lean_ctor_get(v___x_665_, 7);
v_snapshotTasks_673_ = lean_ctor_get(v___x_665_, 8);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_665_, 5);
lean_dec(v_unused_683_);
v___x_675_ = v___x_665_;
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snapshotTasks_673_);
lean_inc(v_infoState_672_);
lean_inc(v_messages_671_);
lean_inc(v_traceState_670_);
lean_inc(v_auxDeclNGen_669_);
lean_inc(v_ngen_668_);
lean_inc(v_nextMacroScope_667_);
lean_inc(v_env_666_);
lean_dec(v___x_665_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = l_Lean_Kernel_enableDiag(v_env_666_, v___y_660_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 5, v___x_509_);
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_nextMacroScope_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_ngen_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_auxDeclNGen_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_traceState_670_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_messages_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v_infoState_672_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v_snapshotTasks_673_);
v___x_679_ = v_reuseFailAlloc_681_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_st_ref_put(v___y_663_, v___x_679_);
v___y_616_ = v___y_660_;
v___y_617_ = v___y_661_;
v___y_618_ = v___y_662_;
v___y_619_ = v___y_659_;
v___y_620_ = v___y_663_;
goto v___jp_615_;
}
}
}
else
{
v___y_616_ = v___y_660_;
v___y_617_ = v___y_661_;
v___y_618_ = v___y_662_;
v___y_619_ = v___y_659_;
v___y_620_ = v___y_663_;
goto v___jp_615_;
}
}
v___jp_685_:
{
lean_object* v___x_688_; lean_object* v_toCold_689_; lean_object* v_currRecDepth_690_; lean_object* v_ref_691_; uint8_t v_suppressElabErrors_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_725_; 
v___x_688_ = lean_st_ref_get(v___y_687_);
v_toCold_689_ = lean_ctor_get(v___y_686_, 0);
v_currRecDepth_690_ = lean_ctor_get(v___y_686_, 1);
v_ref_691_ = lean_ctor_get(v___y_686_, 2);
v_suppressElabErrors_692_ = lean_ctor_get_uint8(v___y_686_, sizeof(void*)*3 + 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v___y_686_);
if (v_isSharedCheck_725_ == 0)
{
v___x_694_ = v___y_686_;
v_isShared_695_ = v_isSharedCheck_725_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_ref_691_);
lean_inc(v_currRecDepth_690_);
lean_inc(v_toCold_689_);
lean_dec(v___y_686_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_725_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fileName_696_; lean_object* v_fileMap_697_; lean_object* v_currNamespace_698_; lean_object* v_openDecls_699_; lean_object* v_initHeartbeats_700_; lean_object* v_maxHeartbeats_701_; lean_object* v_quotContext_702_; lean_object* v_currMacroScope_703_; lean_object* v_cancelTk_x3f_704_; lean_object* v_inheritedTraceOptions_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_722_; 
v_fileName_696_ = lean_ctor_get(v_toCold_689_, 0);
v_fileMap_697_ = lean_ctor_get(v_toCold_689_, 1);
v_currNamespace_698_ = lean_ctor_get(v_toCold_689_, 4);
v_openDecls_699_ = lean_ctor_get(v_toCold_689_, 5);
v_initHeartbeats_700_ = lean_ctor_get(v_toCold_689_, 6);
v_maxHeartbeats_701_ = lean_ctor_get(v_toCold_689_, 7);
v_quotContext_702_ = lean_ctor_get(v_toCold_689_, 8);
v_currMacroScope_703_ = lean_ctor_get(v_toCold_689_, 9);
v_cancelTk_x3f_704_ = lean_ctor_get(v_toCold_689_, 10);
v_inheritedTraceOptions_705_ = lean_ctor_get(v_toCold_689_, 11);
v_isSharedCheck_722_ = !lean_is_exclusive(v_toCold_689_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_723_ = lean_ctor_get(v_toCold_689_, 3);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_toCold_689_, 2);
lean_dec(v_unused_724_);
v___x_707_ = v_toCold_689_;
v_isShared_708_ = v_isSharedCheck_722_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_inheritedTraceOptions_705_);
lean_inc(v_cancelTk_x3f_704_);
lean_inc(v_currMacroScope_703_);
lean_inc(v_quotContext_702_);
lean_inc(v_maxHeartbeats_701_);
lean_inc(v_initHeartbeats_700_);
lean_inc(v_openDecls_699_);
lean_inc(v_currNamespace_698_);
lean_inc(v_fileMap_697_);
lean_inc(v_fileName_696_);
lean_dec(v_toCold_689_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_722_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_env_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v_env_709_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_env_709_);
lean_dec(v___x_688_);
v___x_710_ = l_Lean_maxRecDepth;
v___x_711_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___x_613_, v___x_710_);
lean_inc_ref(v___x_613_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 3, v___x_711_);
lean_ctor_set(v___x_707_, 2, v___x_613_);
v___x_713_ = v___x_707_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fileName_696_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_fileMap_697_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_currNamespace_698_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v_openDecls_699_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_initHeartbeats_700_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v_maxHeartbeats_701_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v_quotContext_702_);
lean_ctor_set(v_reuseFailAlloc_721_, 9, v_currMacroScope_703_);
lean_ctor_set(v_reuseFailAlloc_721_, 10, v_cancelTk_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_721_, 11, v_inheritedTraceOptions_705_);
v___x_713_ = v_reuseFailAlloc_721_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_713_);
v___x_715_ = v___x_694_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_currRecDepth_690_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_ref_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_720_, sizeof(void*)*3 + 1, v_suppressElabErrors_692_);
v___x_715_ = v_reuseFailAlloc_720_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; uint8_t v___x_719_; 
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3, v___x_684_);
v___x_716_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_717_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_613_, v___x_716_, v___x_538_);
v___x_718_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_717_, v___x_614_);
v___x_719_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_709_);
lean_dec_ref(v_env_709_);
if (v___x_718_ == 0)
{
if (v___x_719_ == 0)
{
v___y_616_ = v___x_718_;
v___y_617_ = v___x_710_;
v___y_618_ = v___x_717_;
v___y_619_ = v___x_715_;
v___y_620_ = v___y_687_;
goto v___jp_615_;
}
else
{
v___y_659_ = v___x_715_;
v___y_660_ = v___x_718_;
v___y_661_ = v___x_710_;
v___y_662_ = v___x_717_;
v___y_663_ = v___y_687_;
v___y_664_ = v___x_718_;
goto v___jp_658_;
}
}
else
{
v___y_659_ = v___x_715_;
v___y_660_ = v___x_718_;
v___y_661_ = v___x_710_;
v___y_662_ = v___x_717_;
v___y_663_ = v___y_687_;
v___y_664_ = v___x_719_;
goto v___jp_658_;
}
}
}
}
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
v___x_740_ = l_Lean_Kernel_enableDiag(v_env_729_, v___x_684_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 5, v___x_509_);
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
lean_ctor_set(v_reuseFailAlloc_744_, 5, v___x_509_);
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
lean_inc_ref(v___y_446_);
v___y_686_ = v___y_446_;
v___y_687_ = v___y_447_;
goto v___jp_685_;
}
}
}
else
{
lean_inc_ref(v___y_446_);
v___y_686_ = v___y_446_;
v___y_687_ = v___y_447_;
goto v___jp_685_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v_tacticName_771_, lean_object* v_a_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_768_, v___x_769_, v___x_770_, v_tacticName_771_, v_a_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(lean_object* v_stx_779_, lean_object* v___y_780_){
_start:
{
uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_782_ = 0;
v___x_783_ = l_Lean_Syntax_getRange_x3f(v_stx_779_, v___x_782_);
if (lean_obj_tag(v___x_783_) == 1)
{
lean_object* v_toCold_784_; lean_object* v_val_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_797_; 
v_toCold_784_ = lean_ctor_get(v___y_780_, 0);
v_val_785_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_797_ == 0)
{
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_val_785_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_797_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_fileMap_789_; lean_object* v_start_790_; lean_object* v_stop_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v_fileMap_789_ = lean_ctor_get(v_toCold_784_, 1);
v_start_790_ = lean_ctor_get(v_val_785_, 0);
lean_inc(v_start_790_);
v_stop_791_ = lean_ctor_get(v_val_785_, 1);
lean_inc(v_stop_791_);
lean_dec(v_val_785_);
lean_inc_ref(v_fileMap_789_);
v___x_792_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_789_, v_start_790_, v_stop_791_);
lean_dec(v_stop_791_);
lean_dec(v_start_790_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_792_);
v___x_794_ = v___x_787_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v___x_783_);
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg___boxed(lean_object* v_stx_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_stx_800_, v___y_801_);
lean_dec_ref(v___y_801_);
lean_dec(v_stx_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(lean_object* v_declName_804_, lean_object* v_declRanges_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = l_Lean_Name_isAnonymous(v_declName_804_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v_nextMacroScope_812_; lean_object* v_ngen_813_; lean_object* v_auxDeclNGen_814_; lean_object* v_traceState_815_; lean_object* v_messages_816_; lean_object* v_infoState_817_; lean_object* v_snapshotTasks_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_846_; 
v___x_810_ = lean_st_ref_take(v___y_807_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
v_nextMacroScope_812_ = lean_ctor_get(v___x_810_, 1);
v_ngen_813_ = lean_ctor_get(v___x_810_, 2);
v_auxDeclNGen_814_ = lean_ctor_get(v___x_810_, 3);
v_traceState_815_ = lean_ctor_get(v___x_810_, 4);
v_messages_816_ = lean_ctor_get(v___x_810_, 6);
v_infoState_817_ = lean_ctor_get(v___x_810_, 7);
v_snapshotTasks_818_ = lean_ctor_get(v___x_810_, 8);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v___x_810_, 5);
lean_dec(v_unused_847_);
v___x_820_ = v___x_810_;
v_isShared_821_ = v_isSharedCheck_846_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snapshotTasks_818_);
lean_inc(v_infoState_817_);
lean_inc(v_messages_816_);
lean_inc(v_traceState_815_);
lean_inc(v_auxDeclNGen_814_);
lean_inc(v_ngen_813_);
lean_inc(v_nextMacroScope_812_);
lean_inc(v_env_811_);
lean_dec(v___x_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_846_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_822_ = l_Lean_declRangeExt;
v___x_823_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_822_, v_env_811_, v_declName_804_, v_declRanges_805_);
v___x_824_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 5, v___x_824_);
lean_ctor_set(v___x_820_, 0, v___x_823_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_nextMacroScope_812_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_ngen_813_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_auxDeclNGen_814_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_traceState_815_);
lean_ctor_set(v_reuseFailAlloc_845_, 5, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_845_, 6, v_messages_816_);
lean_ctor_set(v_reuseFailAlloc_845_, 7, v_infoState_817_);
lean_ctor_set(v_reuseFailAlloc_845_, 8, v_snapshotTasks_818_);
v___x_826_ = v_reuseFailAlloc_845_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_mctx_829_; lean_object* v_zetaDeltaFVarIds_830_; lean_object* v_postponed_831_; lean_object* v_diag_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_843_; 
v___x_827_ = lean_st_ref_put(v___y_807_, v___x_826_);
v___x_828_ = lean_st_ref_take(v___y_806_);
v_mctx_829_ = lean_ctor_get(v___x_828_, 0);
v_zetaDeltaFVarIds_830_ = lean_ctor_get(v___x_828_, 2);
v_postponed_831_ = lean_ctor_get(v___x_828_, 3);
v_diag_832_ = lean_ctor_get(v___x_828_, 4);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v___x_828_, 1);
lean_dec(v_unused_844_);
v___x_834_ = v___x_828_;
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_diag_832_);
lean_inc(v_postponed_831_);
lean_inc(v_zetaDeltaFVarIds_830_);
lean_inc(v_mctx_829_);
lean_dec(v___x_828_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_mctx_829_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_zetaDeltaFVarIds_830_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_postponed_831_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_diag_832_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_st_ref_put(v___y_806_, v___x_838_);
v___x_840_ = lean_box(0);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_declRanges_805_);
lean_dec(v_declName_804_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg___boxed(lean_object* v_declName_850_, lean_object* v_declRanges_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_850_, v_declRanges_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec(v___y_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(lean_object* v_declName_856_, lean_object* v_rangeStx_857_, lean_object* v_selectionRangeStx_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_881_; 
v___x_864_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_rangeStx_857_, v___y_861_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_881_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
if (lean_obj_tag(v_a_865_) == 1)
{
lean_object* v_val_869_; lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v_a_873_; 
lean_del_object(v___x_867_);
v_val_869_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_a_865_, 1);
v___x_870_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_selectionRangeStx_858_, v___y_861_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v___x_870_);
if (lean_obj_tag(v_a_871_) == 0)
{
lean_inc(v_val_869_);
v_a_873_ = v_val_869_;
goto v___jp_872_;
}
else
{
lean_object* v_val_876_; 
v_val_876_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v_a_871_, 1);
v_a_873_ = v_val_876_;
goto v___jp_872_;
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_val_869_);
lean_ctor_set(v___x_874_, 1, v_a_873_);
v___x_875_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_856_, v___x_874_, v___y_860_, v___y_862_);
return v___x_875_;
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_dec(v_a_865_);
lean_dec(v_declName_856_);
v___x_877_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_877_);
v___x_879_ = v___x_867_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9___boxed(lean_object* v_declName_882_, lean_object* v_rangeStx_883_, lean_object* v_selectionRangeStx_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_declName_882_, v_rangeStx_883_, v_selectionRangeStx_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v_selectionRangeStx_884_);
lean_dec(v_rangeStx_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
if (lean_obj_tag(v_a_891_) == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l_List_reverse___redArg(v_a_892_);
return v___x_893_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_904_; 
v_head_894_ = lean_ctor_get(v_a_891_, 0);
v_tail_895_ = lean_ctor_get(v_a_891_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_904_ == 0)
{
v___x_897_ = v_a_891_;
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_tail_895_);
lean_inc(v_head_894_);
lean_dec(v_a_891_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = l_Lean_mkLevelParam(v_head_894_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v_a_892_);
lean_ctor_set(v___x_897_, 0, v___x_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_a_892_);
v___x_901_ = v_reuseFailAlloc_903_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
v_a_891_ = v_tail_895_;
v_a_892_ = v___x_901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(lean_object* v_env_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v_nextMacroScope_910_; lean_object* v_ngen_911_; lean_object* v_auxDeclNGen_912_; lean_object* v_traceState_913_; lean_object* v_messages_914_; lean_object* v_infoState_915_; lean_object* v_snapshotTasks_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_942_; 
v___x_909_ = lean_st_ref_take(v___y_907_);
v_nextMacroScope_910_ = lean_ctor_get(v___x_909_, 1);
v_ngen_911_ = lean_ctor_get(v___x_909_, 2);
v_auxDeclNGen_912_ = lean_ctor_get(v___x_909_, 3);
v_traceState_913_ = lean_ctor_get(v___x_909_, 4);
v_messages_914_ = lean_ctor_get(v___x_909_, 6);
v_infoState_915_ = lean_ctor_get(v___x_909_, 7);
v_snapshotTasks_916_ = lean_ctor_get(v___x_909_, 8);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_943_ = lean_ctor_get(v___x_909_, 5);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v___x_909_, 0);
lean_dec(v_unused_944_);
v___x_918_ = v___x_909_;
v_isShared_919_ = v_isSharedCheck_942_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snapshotTasks_916_);
lean_inc(v_infoState_915_);
lean_inc(v_messages_914_);
lean_inc(v_traceState_913_);
lean_inc(v_auxDeclNGen_912_);
lean_inc(v_ngen_911_);
lean_inc(v_nextMacroScope_910_);
lean_dec(v___x_909_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_942_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 5, v___x_920_);
lean_ctor_set(v___x_918_, 0, v_env_905_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_env_905_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_nextMacroScope_910_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_ngen_911_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_auxDeclNGen_912_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_traceState_913_);
lean_ctor_set(v_reuseFailAlloc_941_, 5, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_941_, 6, v_messages_914_);
lean_ctor_set(v_reuseFailAlloc_941_, 7, v_infoState_915_);
lean_ctor_set(v_reuseFailAlloc_941_, 8, v_snapshotTasks_916_);
v___x_922_ = v_reuseFailAlloc_941_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_mctx_925_; lean_object* v_zetaDeltaFVarIds_926_; lean_object* v_postponed_927_; lean_object* v_diag_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_939_; 
v___x_923_ = lean_st_ref_put(v___y_907_, v___x_922_);
v___x_924_ = lean_st_ref_take(v___y_906_);
v_mctx_925_ = lean_ctor_get(v___x_924_, 0);
v_zetaDeltaFVarIds_926_ = lean_ctor_get(v___x_924_, 2);
v_postponed_927_ = lean_ctor_get(v___x_924_, 3);
v_diag_928_ = lean_ctor_get(v___x_924_, 4);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___x_924_, 1);
lean_dec(v_unused_940_);
v___x_930_ = v___x_924_;
v_isShared_931_ = v_isSharedCheck_939_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_diag_928_);
lean_inc(v_postponed_927_);
lean_inc(v_zetaDeltaFVarIds_926_);
lean_inc(v_mctx_925_);
lean_dec(v___x_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_939_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_mctx_925_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_zetaDeltaFVarIds_926_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_postponed_927_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_diag_928_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_st_ref_put(v___y_906_, v___x_934_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg___boxed(lean_object* v_env_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(lean_object* v_env_950_, lean_object* v_x_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_env_958_; lean_object* v_a_960_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_957_ = lean_st_ref_get(v___y_955_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_957_);
v___x_970_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_950_, v___y_953_, v___y_955_);
lean_dec_ref(v___x_970_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
v___x_971_ = lean_apply_5(v_x_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, lean_box(0));
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_958_, v___y_953_, v___y_955_);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_981_);
v___x_975_ = v___x_973_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_dec(v___x_973_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_a_972_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_972_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v_a_982_; 
v_a_982_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_971_, 1);
v_a_960_ = v_a_982_;
goto v___jp_959_;
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v___x_961_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_958_, v___y_953_, v___y_955_);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v___x_961_, 0);
lean_dec(v_unused_969_);
v___x_963_ = v___x_961_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_dec(v___x_961_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 1);
lean_ctor_set(v___x_963_, 0, v_a_960_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_960_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg___boxed(lean_object* v_env_983_, lean_object* v_x_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_983_, v_x_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_990_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
v___x_992_ = lean_unsigned_to_nat(16u);
v___x_993_ = lean_mk_array(v___x_992_, v___x_991_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_1000_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
lean_ctor_set(v___x_1001_, 2, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = l_Lean_Level_ofNat(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_1018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_1020_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_1021_ = l_Lean_mkConst(v___x_1020_, v___x_1019_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_1024_ = l_Lean_mkConst(v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_1031_ = l_Lean_mkConst(v___x_1030_, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_1038_, lean_object* v_e_1039_, lean_object* v_axiomDeclRange_x3f_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___x_1054_; lean_object* v_a_1055_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v___x_1161_; 
v___x_1054_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_1039_, v_a_1042_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref(v___x_1054_);
v___x_1161_ = l_Lean_Expr_hasFVar(v_a_1055_);
if (v___x_1161_ == 0)
{
v___y_1140_ = v_a_1041_;
v___y_1141_ = v_a_1042_;
v___y_1142_ = v_a_1043_;
v___y_1143_ = v_a_1044_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v___x_1162_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1163_ = l_Lean_MessageData_ofName(v_tacticName_1038_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_indentExpr(v_a_1055_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1168_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
v___jp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(v___y_1047_, v___x_1049_);
v___x_1051_ = l_Lean_mkConst(v___y_1048_, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
v___jp_1056_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_params_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1136_; 
v___x_1061_ = lean_st_ref_get(v___y_1060_);
v___x_1062_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1055_);
v___x_1063_ = l_Lean_collectLevelParams(v___x_1062_, v_a_1055_);
v_params_1064_ = lean_ctor_get(v___x_1063_, 2);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; lean_object* v_unused_1138_; 
v_unused_1137_ = lean_ctor_get(v___x_1063_, 1);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v___x_1063_, 0);
lean_dec(v_unused_1138_);
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1136_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_params_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1136_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_env_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_env_1068_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_ref(v_env_1068_);
lean_dec(v___x_1061_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_array_to_list(v_params_1064_);
v___x_1071_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_1038_);
v___x_1072_ = l_Lean_Name_append(v___x_1071_, v_tacticName_1038_);
v___x_1073_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1072_);
v___x_1074_ = l_Lean_Name_append(v___x_1072_, v___x_1073_);
lean_inc(v_a_1055_);
lean_inc(v___x_1070_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1075_, 0, v___x_1074_);
lean_closure_set(v___f_1075_, 1, v___x_1070_);
lean_closure_set(v___f_1075_, 2, v___x_1069_);
lean_closure_set(v___f_1075_, 3, v_tacticName_1038_);
lean_closure_set(v___f_1075_, 4, v_a_1055_);
v___x_1076_ = l_Lean_Environment_unlockAsync(v_env_1068_);
v___x_1077_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v___x_1076_, v___f_1075_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1127_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1127_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1127_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_unbox(v_a_1078_);
lean_dec(v_a_1078_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_dec(v___x_1072_);
lean_dec(v___x_1070_);
lean_del_object(v___x_1066_);
lean_dec(v_a_1055_);
v___x_1083_ = lean_box(1);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1083_);
v___x_1085_ = v___x_1080_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1126_; 
lean_del_object(v___x_1080_);
v___x_1087_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1088_ = l_Lean_Name_append(v___x_1072_, v___x_1087_);
v___x_1089_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1088_, v___y_1060_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1126_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1126_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1094_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1095_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1096_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1097_ = l_Lean_mkApp3(v___x_1094_, v___x_1095_, v_a_1055_, v___x_1096_);
lean_inc(v___x_1070_);
lean_inc(v_a_1090_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 2, v___x_1097_);
lean_ctor_set(v___x_1066_, 1, v___x_1070_);
lean_ctor_set(v___x_1066_, 0, v_a_1090_);
v___x_1099_ = v___x_1066_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1090_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = 0;
v___x_1101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*1, v___x_1100_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1101_);
v___x_1103_ = v___x_1092_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_addDecl(v___x_1103_, v___x_1100_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref_known(v___x_1104_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1040_) == 1)
{
lean_object* v_val_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_val_1105_ = lean_ctor_get(v_axiomDeclRange_x3f_1040_, 0);
v___x_1106_ = lean_box(0);
lean_inc(v_a_1090_);
v___x_1107_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_a_1090_, v_val_1105_, v___x_1106_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref_known(v___x_1107_, 1);
v___y_1047_ = v___x_1070_;
v___y_1048_ = v_a_1090_;
goto v___jp_1046_;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_a_1090_);
lean_dec(v___x_1070_);
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
v___y_1047_ = v___x_1070_;
v___y_1048_ = v_a_1090_;
goto v___jp_1046_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_a_1090_);
lean_dec(v___x_1070_);
v_a_1116_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1104_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1104_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
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
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v___x_1072_);
lean_dec(v___x_1070_);
lean_del_object(v___x_1066_);
lean_dec(v_a_1055_);
v_a_1128_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1077_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1077_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
v___jp_1139_:
{
uint8_t v___x_1144_; 
v___x_1144_ = l_Lean_Expr_hasMVar(v_a_1055_);
if (v___x_1144_ == 0)
{
v___y_1057_ = v___y_1140_;
v___y_1058_ = v___y_1141_;
v___y_1059_ = v___y_1142_;
v___y_1060_ = v___y_1143_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v___x_1145_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1146_ = l_Lean_MessageData_ofName(v_tacticName_1038_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_indentExpr(v_a_1055_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1151_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1178_, lean_object* v_e_1179_, lean_object* v_axiomDeclRange_x3f_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1178_, v_e_1179_, v_axiomDeclRange_x3f_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_axiomDeclRange_x3f_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1201_, lean_object* v_constName_1202_, uint8_t v_checkMeta_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1202_, v_checkMeta_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_constName_1211_, lean_object* v_checkMeta_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_checkMeta_boxed_1218_; lean_object* v_res_1219_; 
v_checkMeta_boxed_1218_ = lean_unbox(v_checkMeta_1212_);
v_res_1219_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1210_, v_constName_1211_, v_checkMeta_boxed_1218_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1220_, lean_object* v_msg_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1228_, v_msg_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11(lean_object* v_env_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_1236_, v___y_1238_, v___y_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___boxed(lean_object* v_env_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11(v_env_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_00_u03b1_1250_, lean_object* v_env_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_1251_, v_x_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_00_u03b1_1259_, lean_object* v_env_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(v_00_u03b1_1259_, v_env_1260_, v_x_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14(lean_object* v_stx_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_stx_1268_, v___y_1271_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___boxed(lean_object* v_stx_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14(v_stx_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v_stx_1275_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(lean_object* v_declName_1282_, lean_object* v_declRanges_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_1282_, v_declRanges_1283_, v___y_1285_, v___y_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___boxed(lean_object* v_declName_1290_, lean_object* v_declRanges_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(v_declName_1290_, v_declRanges_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1298_, lean_object* v_x_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_x_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1306_, v_x_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1313_;
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

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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
v___x_166_ = lean_st_ref_set(v___y_147_, v___x_165_);
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
v___x_213_ = lean_st_ref_set(v___y_190_, v___x_212_);
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
lean_object* v___x_267_; lean_object* v_env_268_; lean_object* v___x_269_; lean_object* v_mctx_270_; lean_object* v_lctx_271_; lean_object* v_options_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_267_ = lean_st_ref_get(v___y_265_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_env_268_);
lean_dec(v___x_267_);
v___x_269_ = lean_st_ref_get(v___y_263_);
v_mctx_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_mctx_270_);
lean_dec(v___x_269_);
v_lctx_271_ = lean_ctor_get(v___y_262_, 2);
v_options_272_ = lean_ctor_get(v___y_264_, 2);
lean_inc_ref(v_options_272_);
lean_inc_ref(v_lctx_271_);
v___x_273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_273_, 0, v_env_268_);
lean_ctor_set(v___x_273_, 1, v_mctx_270_);
lean_ctor_set(v___x_273_, 2, v_lctx_271_);
lean_ctor_set(v___x_273_, 3, v_options_272_);
v___x_274_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v_msgData_261_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object* v_msgData_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msgData_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object* v_msg_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_ref_289_; lean_object* v___x_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_ref_289_ = lean_ctor_get(v___y_286_, 5);
v___x_290_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msg_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
lean_inc(v_ref_289_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_ref_289_);
lean_ctor_set(v___x_295_, 1, v_a_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 1);
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(lean_object* v_o_310_, lean_object* v_k_311_, uint8_t v_v_312_){
_start:
{
lean_object* v_map_313_; uint8_t v_hasTrace_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_328_; 
v_map_313_ = lean_ctor_get(v_o_310_, 0);
v_hasTrace_314_ = lean_ctor_get_uint8(v_o_310_, sizeof(void*)*1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_o_310_);
if (v_isSharedCheck_328_ == 0)
{
v___x_316_ = v_o_310_;
v_isShared_317_ = v_isSharedCheck_328_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_map_313_);
lean_dec(v_o_310_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_328_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_318_, 0, v_v_312_);
lean_inc(v_k_311_);
v___x_319_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_311_, v___x_318_, v_map_313_);
if (v_hasTrace_314_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_323_; 
v___x_320_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__1));
v___x_321_ = l_Lean_Name_isPrefixOf(v___x_320_, v_k_311_);
lean_dec(v_k_311_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_323_ = v___x_316_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_319_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*1, v___x_321_);
return v___x_323_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec(v_k_311_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_326_ = v___x_316_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*1, v_hasTrace_314_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___boxed(lean_object* v_o_329_, lean_object* v_k_330_, lean_object* v_v_331_){
_start:
{
uint8_t v_v_boxed_332_; lean_object* v_res_333_; 
v_v_boxed_332_ = lean_unbox(v_v_331_);
v_res_333_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(v_o_329_, v_k_330_, v_v_boxed_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_334_, lean_object* v_opt_335_, uint8_t v_val_336_){
_start:
{
lean_object* v_name_337_; lean_object* v___x_338_; 
v_name_337_ = lean_ctor_get(v_opt_335_, 0);
lean_inc(v_name_337_);
lean_dec_ref(v_opt_335_);
v___x_338_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(v_opts_334_, v_name_337_, v_val_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_339_, lean_object* v_opt_340_, lean_object* v_val_341_){
_start:
{
uint8_t v_val_boxed_342_; lean_object* v_res_343_; 
v_val_boxed_342_ = lean_unbox(v_val_341_);
v_res_343_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_339_, v_opt_340_, v_val_boxed_342_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_box(0);
v___x_345_ = l_Lean_Elab_abortCommandExceptionId;
v___x_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___boxed(lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
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
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg___boxed(lean_object* v_x_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(lean_object* v_constName_376_, uint8_t v_checkMeta_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v_env_384_; uint8_t v___x_385_; 
v___x_383_ = lean_st_ref_get(v___y_381_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
lean_inc(v_constName_376_);
v___x_385_ = lean_has_compile_error(v_env_384_, v_constName_376_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v_env_387_; lean_object* v_options_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_386_ = lean_st_ref_get(v___y_381_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v_options_388_ = lean_ctor_get(v___y_380_, 2);
v___x_389_ = l_Lean_Environment_evalConst___redArg(v_env_387_, v_options_388_, v_constName_376_, v_checkMeta_377_);
lean_dec(v_constName_376_);
lean_dec_ref(v_env_387_);
v___x_390_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_389_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v___x_392_; lean_object* v_env_393_; lean_object* v_options_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref_known(v___x_391_, 1);
v___x_392_ = lean_st_ref_get(v___y_381_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_env_393_);
lean_dec(v___x_392_);
v_options_394_ = lean_ctor_get(v___y_380_, 2);
v___x_395_ = l_Lean_Environment_evalConst___redArg(v_env_393_, v_options_394_, v_constName_376_, v_checkMeta_377_);
lean_dec(v_constName_376_);
lean_dec_ref(v_env_393_);
v___x_396_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_395_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
return v___x_396_;
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_constName_376_);
v_a_397_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_391_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_391_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg___boxed(lean_object* v_constName_405_, lean_object* v_checkMeta_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_checkMeta_boxed_412_; lean_object* v_res_413_; 
v_checkMeta_boxed_412_ = lean_unbox(v_checkMeta_406_);
v_res_413_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_405_, v_checkMeta_boxed_412_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_413_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__4));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_box(0);
v___x_427_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_428_ = l_Lean_mkConst(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_435_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
lean_ctor_set(v___x_435_, 3, v___x_434_);
lean_ctor_set(v___x_435_, 4, v___x_434_);
lean_ctor_set(v___x_435_, 5, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v_tacticName_439_, lean_object* v_a_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___y_447_; lean_object* v___y_448_; uint8_t v___y_449_; lean_object* v___x_458_; lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_728_; 
v___x_458_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_436_, v___y_444_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_728_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_728_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_728_;
goto v_resetjp_460_;
}
v___jp_446_:
{
if (v___y_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref(v___y_447_);
v___x_450_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_451_ = l_Lean_MessageData_ofName(v_tacticName_439_);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_Exception_toMessageData(v___y_448_);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_456_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec_ref(v___y_443_);
return v___x_457_;
}
else
{
lean_dec_ref(v___y_448_);
lean_dec_ref(v___y_443_);
lean_dec(v_tacticName_439_);
return v___y_447_;
}
}
v_resetjp_460_:
{
lean_object* v___y_464_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_traceState_495_; lean_object* v_messages_496_; lean_object* v_infoState_497_; lean_object* v_snapshotTasks_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_726_; 
v___x_490_ = lean_st_ref_take(v___y_444_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_490_, 1);
v_ngen_493_ = lean_ctor_get(v___x_490_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_490_, 3);
v_traceState_495_ = lean_ctor_get(v___x_490_, 4);
v_messages_496_ = lean_ctor_get(v___x_490_, 6);
v_infoState_497_ = lean_ctor_get(v___x_490_, 7);
v_snapshotTasks_498_ = lean_ctor_get(v___x_490_, 8);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_490_, 5);
lean_dec(v_unused_727_);
v___x_500_ = v___x_490_;
v_isShared_501_ = v_isSharedCheck_726_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snapshotTasks_498_);
lean_inc(v_infoState_497_);
lean_inc(v_messages_496_);
lean_inc(v_traceState_495_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_490_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_726_;
goto v_resetjp_499_;
}
v___jp_463_:
{
if (lean_obj_tag(v___y_464_) == 0)
{
uint8_t v___x_465_; lean_object* v___x_466_; 
lean_dec_ref_known(v___y_464_, 1);
v___x_465_ = 1;
v___x_466_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_a_459_, v___x_465_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_dec_ref(v___y_443_);
lean_dec(v_tacticName_439_);
return v___x_466_;
}
else
{
lean_object* v_a_467_; uint8_t v___x_468_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
v___x_468_ = l_Lean_Exception_isInterrupt(v_a_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; 
lean_inc(v_a_467_);
v___x_469_ = l_Lean_Exception_isRuntime(v_a_467_);
v___y_447_ = v___x_466_;
v___y_448_ = v_a_467_;
v___y_449_ = v___x_469_;
goto v___jp_446_;
}
else
{
v___y_447_ = v___x_466_;
v___y_448_ = v_a_467_;
v___y_449_ = v___x_468_;
goto v___jp_446_;
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec(v_a_459_);
lean_dec_ref(v___y_443_);
lean_dec(v_tacticName_439_);
v_a_470_ = lean_ctor_get(v___y_464_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___y_464_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___y_464_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___y_464_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
v___jp_478_:
{
if (v___y_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref(v___y_479_);
v___x_482_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_439_);
v___x_483_ = l_Lean_MessageData_ofName(v_tacticName_439_);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_Exception_toMessageData(v___y_480_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_488_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
v___y_464_ = v___x_489_;
goto v___jp_463_;
}
else
{
lean_dec_ref(v___y_480_);
v___y_464_ = v___y_479_;
goto v___jp_463_;
}
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_502_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_459_, 3);
v___x_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_503_, 0, v_a_459_);
lean_ctor_set(v___x_503_, 1, v___x_437_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v_a_459_);
lean_ctor_set(v___x_504_, 1, v___x_438_);
v___x_505_ = l_Lean_markMeta(v_env_491_, v_a_459_);
v___x_506_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 5, v___x_506_);
lean_ctor_set(v___x_500_, 0, v___x_505_);
v___x_508_ = v___x_500_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_traceState_495_);
lean_ctor_set(v_reuseFailAlloc_725_, 5, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_725_, 6, v_messages_496_);
lean_ctor_set(v_reuseFailAlloc_725_, 7, v_infoState_497_);
lean_ctor_set(v_reuseFailAlloc_725_, 8, v_snapshotTasks_498_);
v___x_508_ = v_reuseFailAlloc_725_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_mctx_511_; lean_object* v_zetaDeltaFVarIds_512_; lean_object* v_postponed_513_; lean_object* v_diag_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_723_; 
v___x_509_ = lean_st_ref_set(v___y_444_, v___x_508_);
v___x_510_ = lean_st_ref_take(v___y_442_);
v_mctx_511_ = lean_ctor_get(v___x_510_, 0);
v_zetaDeltaFVarIds_512_ = lean_ctor_get(v___x_510_, 2);
v_postponed_513_ = lean_ctor_get(v___x_510_, 3);
v_diag_514_ = lean_ctor_get(v___x_510_, 4);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_510_, 1);
lean_dec(v_unused_724_);
v___x_516_ = v___x_510_;
v_isShared_517_ = v_isSharedCheck_723_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_diag_514_);
lean_inc(v_postponed_513_);
lean_inc(v_zetaDeltaFVarIds_512_);
lean_inc(v_mctx_511_);
lean_dec(v___x_510_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_723_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_mctx_511_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_zetaDeltaFVarIds_512_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_postponed_513_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_diag_514_);
v___x_520_ = v_reuseFailAlloc_722_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_options_523_; lean_object* v_env_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_521_ = lean_st_ref_set(v___y_442_, v___x_520_);
v___x_522_ = lean_st_ref_get(v___y_444_);
v_options_523_ = lean_ctor_get(v___y_443_, 2);
v_env_524_ = lean_ctor_get(v___x_522_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(1);
v___x_526_ = 1;
v___x_527_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_527_, 0, v___x_503_);
lean_ctor_set(v___x_527_, 1, v_a_440_);
lean_ctor_set(v___x_527_, 2, v___x_525_);
lean_ctor_set(v___x_527_, 3, v___x_504_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*4, v___x_526_);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 1);
lean_ctor_set(v___x_461_, 0, v___x_527_);
v___x_529_ = v___x_461_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_721_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
uint8_t v___x_530_; uint8_t v___x_531_; uint8_t v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v_fileName_536_; lean_object* v_fileMap_537_; lean_object* v_currRecDepth_538_; lean_object* v_ref_539_; lean_object* v_currNamespace_540_; lean_object* v_openDecls_541_; lean_object* v_initHeartbeats_542_; lean_object* v_maxHeartbeats_543_; lean_object* v_quotContext_544_; lean_object* v_currMacroScope_545_; lean_object* v_cancelTk_x3f_546_; uint8_t v_suppressElabErrors_547_; lean_object* v_inheritedTraceOptions_548_; lean_object* v___y_549_; uint8_t v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; uint8_t v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; uint8_t v___y_581_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; uint8_t v___x_665_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_700_; uint8_t v___x_720_; 
v___x_530_ = 1;
v___x_531_ = 0;
v___x_601_ = l_Lean_Elab_async;
lean_inc_ref(v_options_523_);
v___x_602_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v_options_523_, v___x_601_, v___x_531_);
v___x_603_ = l_Lean_diagnostics;
v___x_665_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_602_, v___x_603_);
v___x_720_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_524_);
lean_dec_ref(v_env_524_);
if (v___x_720_ == 0)
{
if (v___x_665_ == 0)
{
lean_inc_ref(v___y_443_);
v___y_667_ = v___y_443_;
v___y_668_ = v___y_444_;
goto v___jp_666_;
}
else
{
v___y_700_ = v___x_720_;
goto v___jp_699_;
}
}
else
{
v___y_700_ = v___x_665_;
goto v___jp_699_;
}
v___jp_532_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_535_, v___y_534_);
v___x_551_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_551_, 0, v_fileName_536_);
lean_ctor_set(v___x_551_, 1, v_fileMap_537_);
lean_ctor_set(v___x_551_, 2, v___y_535_);
lean_ctor_set(v___x_551_, 3, v_currRecDepth_538_);
lean_ctor_set(v___x_551_, 4, v___x_550_);
lean_ctor_set(v___x_551_, 5, v_ref_539_);
lean_ctor_set(v___x_551_, 6, v_currNamespace_540_);
lean_ctor_set(v___x_551_, 7, v_openDecls_541_);
lean_ctor_set(v___x_551_, 8, v_initHeartbeats_542_);
lean_ctor_set(v___x_551_, 9, v_maxHeartbeats_543_);
lean_ctor_set(v___x_551_, 10, v_quotContext_544_);
lean_ctor_set(v___x_551_, 11, v_currMacroScope_545_);
lean_ctor_set(v___x_551_, 12, v_cancelTk_x3f_546_);
lean_ctor_set(v___x_551_, 13, v_inheritedTraceOptions_548_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*14, v___y_533_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*14 + 1, v_suppressElabErrors_547_);
v___x_552_ = l_Lean_addAndCompile(v___x_529_, v___x_530_, v___x_531_, v___x_551_, v___y_549_);
lean_dec_ref_known(v___x_551_, 14);
if (lean_obj_tag(v___x_552_) == 0)
{
v___y_464_ = v___x_552_;
goto v___jp_463_;
}
else
{
lean_object* v_a_553_; uint8_t v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
v___x_554_ = l_Lean_Exception_isInterrupt(v_a_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; 
lean_inc(v_a_553_);
v___x_555_ = l_Lean_Exception_isRuntime(v_a_553_);
v___y_479_ = v___x_552_;
v___y_480_ = v_a_553_;
v___y_481_ = v___x_555_;
goto v___jp_478_;
}
else
{
v___y_479_ = v___x_552_;
v___y_480_ = v_a_553_;
v___y_481_ = v___x_554_;
goto v___jp_478_;
}
}
}
v___jp_556_:
{
lean_object* v_fileName_562_; lean_object* v_fileMap_563_; lean_object* v_currRecDepth_564_; lean_object* v_ref_565_; lean_object* v_currNamespace_566_; lean_object* v_openDecls_567_; lean_object* v_initHeartbeats_568_; lean_object* v_maxHeartbeats_569_; lean_object* v_quotContext_570_; lean_object* v_currMacroScope_571_; lean_object* v_cancelTk_x3f_572_; uint8_t v_suppressElabErrors_573_; lean_object* v_inheritedTraceOptions_574_; 
v_fileName_562_ = lean_ctor_get(v___y_560_, 0);
lean_inc_ref(v_fileName_562_);
v_fileMap_563_ = lean_ctor_get(v___y_560_, 1);
lean_inc_ref(v_fileMap_563_);
v_currRecDepth_564_ = lean_ctor_get(v___y_560_, 3);
lean_inc(v_currRecDepth_564_);
v_ref_565_ = lean_ctor_get(v___y_560_, 5);
lean_inc(v_ref_565_);
v_currNamespace_566_ = lean_ctor_get(v___y_560_, 6);
lean_inc(v_currNamespace_566_);
v_openDecls_567_ = lean_ctor_get(v___y_560_, 7);
lean_inc(v_openDecls_567_);
v_initHeartbeats_568_ = lean_ctor_get(v___y_560_, 8);
lean_inc(v_initHeartbeats_568_);
v_maxHeartbeats_569_ = lean_ctor_get(v___y_560_, 9);
lean_inc(v_maxHeartbeats_569_);
v_quotContext_570_ = lean_ctor_get(v___y_560_, 10);
lean_inc(v_quotContext_570_);
v_currMacroScope_571_ = lean_ctor_get(v___y_560_, 11);
lean_inc(v_currMacroScope_571_);
v_cancelTk_x3f_572_ = lean_ctor_get(v___y_560_, 12);
lean_inc(v_cancelTk_x3f_572_);
v_suppressElabErrors_573_ = lean_ctor_get_uint8(v___y_560_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_574_ = lean_ctor_get(v___y_560_, 13);
lean_inc_ref(v_inheritedTraceOptions_574_);
lean_dec_ref(v___y_560_);
v___y_533_ = v___y_557_;
v___y_534_ = v___y_558_;
v___y_535_ = v___y_559_;
v_fileName_536_ = v_fileName_562_;
v_fileMap_537_ = v_fileMap_563_;
v_currRecDepth_538_ = v_currRecDepth_564_;
v_ref_539_ = v_ref_565_;
v_currNamespace_540_ = v_currNamespace_566_;
v_openDecls_541_ = v_openDecls_567_;
v_initHeartbeats_542_ = v_initHeartbeats_568_;
v_maxHeartbeats_543_ = v_maxHeartbeats_569_;
v_quotContext_544_ = v_quotContext_570_;
v_currMacroScope_545_ = v_currMacroScope_571_;
v_cancelTk_x3f_546_ = v_cancelTk_x3f_572_;
v_suppressElabErrors_547_ = v_suppressElabErrors_573_;
v_inheritedTraceOptions_548_ = v_inheritedTraceOptions_574_;
v___y_549_ = v___y_561_;
goto v___jp_532_;
}
v___jp_575_:
{
if (v___y_581_ == 0)
{
lean_object* v___x_582_; lean_object* v_env_583_; lean_object* v_nextMacroScope_584_; lean_object* v_ngen_585_; lean_object* v_auxDeclNGen_586_; lean_object* v_traceState_587_; lean_object* v_messages_588_; lean_object* v_infoState_589_; lean_object* v_snapshotTasks_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_599_; 
v___x_582_ = lean_st_ref_take(v___y_577_);
v_env_583_ = lean_ctor_get(v___x_582_, 0);
v_nextMacroScope_584_ = lean_ctor_get(v___x_582_, 1);
v_ngen_585_ = lean_ctor_get(v___x_582_, 2);
v_auxDeclNGen_586_ = lean_ctor_get(v___x_582_, 3);
v_traceState_587_ = lean_ctor_get(v___x_582_, 4);
v_messages_588_ = lean_ctor_get(v___x_582_, 6);
v_infoState_589_ = lean_ctor_get(v___x_582_, 7);
v_snapshotTasks_590_ = lean_ctor_get(v___x_582_, 8);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_582_, 5);
lean_dec(v_unused_600_);
v___x_592_ = v___x_582_;
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snapshotTasks_590_);
lean_inc(v_infoState_589_);
lean_inc(v_messages_588_);
lean_inc(v_traceState_587_);
lean_inc(v_auxDeclNGen_586_);
lean_inc(v_ngen_585_);
lean_inc(v_nextMacroScope_584_);
lean_inc(v_env_583_);
lean_dec(v___x_582_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_Kernel_enableDiag(v_env_583_, v___y_576_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 5, v___x_506_);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_nextMacroScope_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_ngen_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_auxDeclNGen_586_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_traceState_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_messages_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_infoState_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_snapshotTasks_590_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_st_ref_set(v___y_577_, v___x_596_);
v___y_557_ = v___y_576_;
v___y_558_ = v___y_579_;
v___y_559_ = v___y_580_;
v___y_560_ = v___y_578_;
v___y_561_ = v___y_577_;
goto v___jp_556_;
}
}
}
else
{
v___y_557_ = v___y_576_;
v___y_558_ = v___y_579_;
v___y_559_ = v___y_580_;
v___y_560_ = v___y_578_;
v___y_561_ = v___y_577_;
goto v___jp_556_;
}
}
v___jp_604_:
{
lean_object* v___x_610_; lean_object* v_fileName_611_; lean_object* v_fileMap_612_; lean_object* v_currRecDepth_613_; lean_object* v_ref_614_; lean_object* v_currNamespace_615_; lean_object* v_openDecls_616_; lean_object* v_initHeartbeats_617_; lean_object* v_maxHeartbeats_618_; lean_object* v_quotContext_619_; lean_object* v_currMacroScope_620_; lean_object* v_cancelTk_x3f_621_; uint8_t v_suppressElabErrors_622_; lean_object* v_inheritedTraceOptions_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_636_; 
v___x_610_ = lean_st_ref_get(v___y_609_);
v_fileName_611_ = lean_ctor_get(v___y_608_, 0);
v_fileMap_612_ = lean_ctor_get(v___y_608_, 1);
v_currRecDepth_613_ = lean_ctor_get(v___y_608_, 3);
v_ref_614_ = lean_ctor_get(v___y_608_, 5);
v_currNamespace_615_ = lean_ctor_get(v___y_608_, 6);
v_openDecls_616_ = lean_ctor_get(v___y_608_, 7);
v_initHeartbeats_617_ = lean_ctor_get(v___y_608_, 8);
v_maxHeartbeats_618_ = lean_ctor_get(v___y_608_, 9);
v_quotContext_619_ = lean_ctor_get(v___y_608_, 10);
v_currMacroScope_620_ = lean_ctor_get(v___y_608_, 11);
v_cancelTk_x3f_621_ = lean_ctor_get(v___y_608_, 12);
v_suppressElabErrors_622_ = lean_ctor_get_uint8(v___y_608_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_623_ = lean_ctor_get(v___y_608_, 13);
v_isSharedCheck_636_ = !lean_is_exclusive(v___y_608_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_637_ = lean_ctor_get(v___y_608_, 4);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v___y_608_, 2);
lean_dec(v_unused_638_);
v___x_625_ = v___y_608_;
v_isShared_626_ = v_isSharedCheck_636_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_inheritedTraceOptions_623_);
lean_inc(v_cancelTk_x3f_621_);
lean_inc(v_currMacroScope_620_);
lean_inc(v_quotContext_619_);
lean_inc(v_maxHeartbeats_618_);
lean_inc(v_initHeartbeats_617_);
lean_inc(v_openDecls_616_);
lean_inc(v_currNamespace_615_);
lean_inc(v_ref_614_);
lean_inc(v_currRecDepth_613_);
lean_inc(v_fileMap_612_);
lean_inc(v_fileName_611_);
lean_dec(v___y_608_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_636_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_env_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v_env_627_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_627_);
lean_dec(v___x_610_);
v___x_628_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_606_, v___y_607_);
lean_inc_ref(v_inheritedTraceOptions_623_);
lean_inc(v_cancelTk_x3f_621_);
lean_inc(v_currMacroScope_620_);
lean_inc(v_quotContext_619_);
lean_inc(v_maxHeartbeats_618_);
lean_inc(v_initHeartbeats_617_);
lean_inc(v_openDecls_616_);
lean_inc(v_currNamespace_615_);
lean_inc(v_ref_614_);
lean_inc(v_currRecDepth_613_);
lean_inc_ref(v___y_606_);
lean_inc_ref(v_fileMap_612_);
lean_inc_ref(v_fileName_611_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_628_);
lean_ctor_set(v___x_625_, 2, v___y_606_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_fileName_611_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_fileMap_612_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v___y_606_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_currRecDepth_613_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_635_, 5, v_ref_614_);
lean_ctor_set(v_reuseFailAlloc_635_, 6, v_currNamespace_615_);
lean_ctor_set(v_reuseFailAlloc_635_, 7, v_openDecls_616_);
lean_ctor_set(v_reuseFailAlloc_635_, 8, v_initHeartbeats_617_);
lean_ctor_set(v_reuseFailAlloc_635_, 9, v_maxHeartbeats_618_);
lean_ctor_set(v_reuseFailAlloc_635_, 10, v_quotContext_619_);
lean_ctor_set(v_reuseFailAlloc_635_, 11, v_currMacroScope_620_);
lean_ctor_set(v_reuseFailAlloc_635_, 12, v_cancelTk_x3f_621_);
lean_ctor_set(v_reuseFailAlloc_635_, 13, v_inheritedTraceOptions_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_635_, sizeof(void*)*14 + 1, v_suppressElabErrors_622_);
v___x_630_ = v_reuseFailAlloc_635_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; uint8_t v___x_634_; 
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*14, v___y_605_);
v___x_631_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_632_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_606_, v___x_631_, v___x_530_);
v___x_633_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_632_, v___x_603_);
v___x_634_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_627_);
lean_dec_ref(v_env_627_);
if (v___x_634_ == 0)
{
if (v___x_633_ == 0)
{
lean_dec_ref(v___x_630_);
v___y_533_ = v___x_633_;
v___y_534_ = v___y_607_;
v___y_535_ = v___x_632_;
v_fileName_536_ = v_fileName_611_;
v_fileMap_537_ = v_fileMap_612_;
v_currRecDepth_538_ = v_currRecDepth_613_;
v_ref_539_ = v_ref_614_;
v_currNamespace_540_ = v_currNamespace_615_;
v_openDecls_541_ = v_openDecls_616_;
v_initHeartbeats_542_ = v_initHeartbeats_617_;
v_maxHeartbeats_543_ = v_maxHeartbeats_618_;
v_quotContext_544_ = v_quotContext_619_;
v_currMacroScope_545_ = v_currMacroScope_620_;
v_cancelTk_x3f_546_ = v_cancelTk_x3f_621_;
v_suppressElabErrors_547_ = v_suppressElabErrors_622_;
v_inheritedTraceOptions_548_ = v_inheritedTraceOptions_623_;
v___y_549_ = v___y_609_;
goto v___jp_532_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_623_);
lean_dec(v_cancelTk_x3f_621_);
lean_dec(v_currMacroScope_620_);
lean_dec(v_quotContext_619_);
lean_dec(v_maxHeartbeats_618_);
lean_dec(v_initHeartbeats_617_);
lean_dec(v_openDecls_616_);
lean_dec(v_currNamespace_615_);
lean_dec(v_ref_614_);
lean_dec(v_currRecDepth_613_);
lean_dec_ref(v_fileMap_612_);
lean_dec_ref(v_fileName_611_);
v___y_576_ = v___x_633_;
v___y_577_ = v___y_609_;
v___y_578_ = v___x_630_;
v___y_579_ = v___y_607_;
v___y_580_ = v___x_632_;
v___y_581_ = v___x_634_;
goto v___jp_575_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_623_);
lean_dec(v_cancelTk_x3f_621_);
lean_dec(v_currMacroScope_620_);
lean_dec(v_quotContext_619_);
lean_dec(v_maxHeartbeats_618_);
lean_dec(v_initHeartbeats_617_);
lean_dec(v_openDecls_616_);
lean_dec(v_currNamespace_615_);
lean_dec(v_ref_614_);
lean_dec(v_currRecDepth_613_);
lean_dec_ref(v_fileMap_612_);
lean_dec_ref(v_fileName_611_);
v___y_576_ = v___x_633_;
v___y_577_ = v___y_609_;
v___y_578_ = v___x_630_;
v___y_579_ = v___y_607_;
v___y_580_ = v___x_632_;
v___y_581_ = v___x_633_;
goto v___jp_575_;
}
}
}
}
v___jp_639_:
{
if (v___y_645_ == 0)
{
lean_object* v___x_646_; lean_object* v_env_647_; lean_object* v_nextMacroScope_648_; lean_object* v_ngen_649_; lean_object* v_auxDeclNGen_650_; lean_object* v_traceState_651_; lean_object* v_messages_652_; lean_object* v_infoState_653_; lean_object* v_snapshotTasks_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_663_; 
v___x_646_ = lean_st_ref_take(v___y_644_);
v_env_647_ = lean_ctor_get(v___x_646_, 0);
v_nextMacroScope_648_ = lean_ctor_get(v___x_646_, 1);
v_ngen_649_ = lean_ctor_get(v___x_646_, 2);
v_auxDeclNGen_650_ = lean_ctor_get(v___x_646_, 3);
v_traceState_651_ = lean_ctor_get(v___x_646_, 4);
v_messages_652_ = lean_ctor_get(v___x_646_, 6);
v_infoState_653_ = lean_ctor_get(v___x_646_, 7);
v_snapshotTasks_654_ = lean_ctor_get(v___x_646_, 8);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_646_, 5);
lean_dec(v_unused_664_);
v___x_656_ = v___x_646_;
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snapshotTasks_654_);
lean_inc(v_infoState_653_);
lean_inc(v_messages_652_);
lean_inc(v_traceState_651_);
lean_inc(v_auxDeclNGen_650_);
lean_inc(v_ngen_649_);
lean_inc(v_nextMacroScope_648_);
lean_inc(v_env_647_);
lean_dec(v___x_646_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_Kernel_enableDiag(v_env_647_, v___y_640_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 5, v___x_506_);
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_nextMacroScope_648_);
lean_ctor_set(v_reuseFailAlloc_662_, 2, v_ngen_649_);
lean_ctor_set(v_reuseFailAlloc_662_, 3, v_auxDeclNGen_650_);
lean_ctor_set(v_reuseFailAlloc_662_, 4, v_traceState_651_);
lean_ctor_set(v_reuseFailAlloc_662_, 5, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_662_, 6, v_messages_652_);
lean_ctor_set(v_reuseFailAlloc_662_, 7, v_infoState_653_);
lean_ctor_set(v_reuseFailAlloc_662_, 8, v_snapshotTasks_654_);
v___x_660_ = v_reuseFailAlloc_662_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; 
v___x_661_ = lean_st_ref_set(v___y_644_, v___x_660_);
v___y_605_ = v___y_640_;
v___y_606_ = v___y_641_;
v___y_607_ = v___y_643_;
v___y_608_ = v___y_642_;
v___y_609_ = v___y_644_;
goto v___jp_604_;
}
}
}
else
{
v___y_605_ = v___y_640_;
v___y_606_ = v___y_641_;
v___y_607_ = v___y_643_;
v___y_608_ = v___y_642_;
v___y_609_ = v___y_644_;
goto v___jp_604_;
}
}
v___jp_666_:
{
lean_object* v___x_669_; lean_object* v_fileName_670_; lean_object* v_fileMap_671_; lean_object* v_currRecDepth_672_; lean_object* v_ref_673_; lean_object* v_currNamespace_674_; lean_object* v_openDecls_675_; lean_object* v_initHeartbeats_676_; lean_object* v_maxHeartbeats_677_; lean_object* v_quotContext_678_; lean_object* v_currMacroScope_679_; lean_object* v_cancelTk_x3f_680_; uint8_t v_suppressElabErrors_681_; lean_object* v_inheritedTraceOptions_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_696_; 
v___x_669_ = lean_st_ref_get(v___y_668_);
v_fileName_670_ = lean_ctor_get(v___y_667_, 0);
v_fileMap_671_ = lean_ctor_get(v___y_667_, 1);
v_currRecDepth_672_ = lean_ctor_get(v___y_667_, 3);
v_ref_673_ = lean_ctor_get(v___y_667_, 5);
v_currNamespace_674_ = lean_ctor_get(v___y_667_, 6);
v_openDecls_675_ = lean_ctor_get(v___y_667_, 7);
v_initHeartbeats_676_ = lean_ctor_get(v___y_667_, 8);
v_maxHeartbeats_677_ = lean_ctor_get(v___y_667_, 9);
v_quotContext_678_ = lean_ctor_get(v___y_667_, 10);
v_currMacroScope_679_ = lean_ctor_get(v___y_667_, 11);
v_cancelTk_x3f_680_ = lean_ctor_get(v___y_667_, 12);
v_suppressElabErrors_681_ = lean_ctor_get_uint8(v___y_667_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_682_ = lean_ctor_get(v___y_667_, 13);
v_isSharedCheck_696_ = !lean_is_exclusive(v___y_667_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; 
v_unused_697_ = lean_ctor_get(v___y_667_, 4);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v___y_667_, 2);
lean_dec(v_unused_698_);
v___x_684_ = v___y_667_;
v_isShared_685_ = v_isSharedCheck_696_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_inheritedTraceOptions_682_);
lean_inc(v_cancelTk_x3f_680_);
lean_inc(v_currMacroScope_679_);
lean_inc(v_quotContext_678_);
lean_inc(v_maxHeartbeats_677_);
lean_inc(v_initHeartbeats_676_);
lean_inc(v_openDecls_675_);
lean_inc(v_currNamespace_674_);
lean_inc(v_ref_673_);
lean_inc(v_currRecDepth_672_);
lean_inc(v_fileMap_671_);
lean_inc(v_fileName_670_);
lean_dec(v___y_667_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_696_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_env_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_env_686_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_env_686_);
lean_dec(v___x_669_);
v___x_687_ = l_Lean_maxRecDepth;
v___x_688_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__6(v___x_602_, v___x_687_);
lean_inc_ref(v___x_602_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 4, v___x_688_);
lean_ctor_set(v___x_684_, 2, v___x_602_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_fileName_670_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_fileMap_671_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_currRecDepth_672_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v_ref_673_);
lean_ctor_set(v_reuseFailAlloc_695_, 6, v_currNamespace_674_);
lean_ctor_set(v_reuseFailAlloc_695_, 7, v_openDecls_675_);
lean_ctor_set(v_reuseFailAlloc_695_, 8, v_initHeartbeats_676_);
lean_ctor_set(v_reuseFailAlloc_695_, 9, v_maxHeartbeats_677_);
lean_ctor_set(v_reuseFailAlloc_695_, 10, v_quotContext_678_);
lean_ctor_set(v_reuseFailAlloc_695_, 11, v_currMacroScope_679_);
lean_ctor_set(v_reuseFailAlloc_695_, 12, v_cancelTk_x3f_680_);
lean_ctor_set(v_reuseFailAlloc_695_, 13, v_inheritedTraceOptions_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*14 + 1, v_suppressElabErrors_681_);
v___x_690_ = v_reuseFailAlloc_695_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; uint8_t v___x_694_; 
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*14, v___x_665_);
v___x_691_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_692_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_602_, v___x_691_, v___x_531_);
v___x_693_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_692_, v___x_603_);
v___x_694_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_686_);
lean_dec_ref(v_env_686_);
if (v___x_694_ == 0)
{
if (v___x_693_ == 0)
{
v___y_605_ = v___x_693_;
v___y_606_ = v___x_692_;
v___y_607_ = v___x_687_;
v___y_608_ = v___x_690_;
v___y_609_ = v___y_668_;
goto v___jp_604_;
}
else
{
v___y_640_ = v___x_693_;
v___y_641_ = v___x_692_;
v___y_642_ = v___x_690_;
v___y_643_ = v___x_687_;
v___y_644_ = v___y_668_;
v___y_645_ = v___x_694_;
goto v___jp_639_;
}
}
else
{
v___y_640_ = v___x_693_;
v___y_641_ = v___x_692_;
v___y_642_ = v___x_690_;
v___y_643_ = v___x_687_;
v___y_644_ = v___y_668_;
v___y_645_ = v___x_693_;
goto v___jp_639_;
}
}
}
}
v___jp_699_:
{
if (v___y_700_ == 0)
{
lean_object* v___x_701_; lean_object* v_env_702_; lean_object* v_nextMacroScope_703_; lean_object* v_ngen_704_; lean_object* v_auxDeclNGen_705_; lean_object* v_traceState_706_; lean_object* v_messages_707_; lean_object* v_infoState_708_; lean_object* v_snapshotTasks_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
v___x_701_ = lean_st_ref_take(v___y_444_);
v_env_702_ = lean_ctor_get(v___x_701_, 0);
v_nextMacroScope_703_ = lean_ctor_get(v___x_701_, 1);
v_ngen_704_ = lean_ctor_get(v___x_701_, 2);
v_auxDeclNGen_705_ = lean_ctor_get(v___x_701_, 3);
v_traceState_706_ = lean_ctor_get(v___x_701_, 4);
v_messages_707_ = lean_ctor_get(v___x_701_, 6);
v_infoState_708_ = lean_ctor_get(v___x_701_, 7);
v_snapshotTasks_709_ = lean_ctor_get(v___x_701_, 8);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v___x_701_, 5);
lean_dec(v_unused_719_);
v___x_711_ = v___x_701_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_snapshotTasks_709_);
lean_inc(v_infoState_708_);
lean_inc(v_messages_707_);
lean_inc(v_traceState_706_);
lean_inc(v_auxDeclNGen_705_);
lean_inc(v_ngen_704_);
lean_inc(v_nextMacroScope_703_);
lean_inc(v_env_702_);
lean_dec(v___x_701_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = l_Lean_Kernel_enableDiag(v_env_702_, v___x_665_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 5, v___x_506_);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_nextMacroScope_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_ngen_704_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_auxDeclNGen_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_traceState_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v_messages_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_infoState_708_);
lean_ctor_set(v_reuseFailAlloc_717_, 8, v_snapshotTasks_709_);
v___x_715_ = v_reuseFailAlloc_717_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; 
v___x_716_ = lean_st_ref_set(v___y_444_, v___x_715_);
lean_inc_ref(v___y_443_);
v___y_667_ = v___y_443_;
v___y_668_ = v___y_444_;
goto v___jp_666_;
}
}
}
else
{
lean_inc_ref(v___y_443_);
v___y_667_ = v___y_443_;
v___y_668_ = v___y_444_;
goto v___jp_666_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_729_, lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v_tacticName_732_, lean_object* v_a_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_729_, v___x_730_, v___x_731_, v_tacticName_732_, v_a_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(lean_object* v_stx_740_, lean_object* v___y_741_){
_start:
{
uint8_t v___x_743_; lean_object* v___x_744_; 
v___x_743_ = 0;
v___x_744_ = l_Lean_Syntax_getRange_x3f(v_stx_740_, v___x_743_);
if (lean_obj_tag(v___x_744_) == 1)
{
lean_object* v_val_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_757_; 
v_val_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_757_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_val_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_fileMap_749_; lean_object* v_start_750_; lean_object* v_stop_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v_fileMap_749_ = lean_ctor_get(v___y_741_, 1);
v_start_750_ = lean_ctor_get(v_val_745_, 0);
lean_inc(v_start_750_);
v_stop_751_ = lean_ctor_get(v_val_745_, 1);
lean_inc(v_stop_751_);
lean_dec(v_val_745_);
lean_inc_ref(v_fileMap_749_);
v___x_752_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_749_, v_start_750_, v_stop_751_);
lean_dec(v_stop_751_);
lean_dec(v_start_750_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_752_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v___x_744_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg___boxed(lean_object* v_stx_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_stx_760_, v___y_761_);
lean_dec_ref(v___y_761_);
lean_dec(v_stx_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(lean_object* v_declName_764_, lean_object* v_declRanges_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = l_Lean_Name_isAnonymous(v_declName_764_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v_env_771_; lean_object* v_nextMacroScope_772_; lean_object* v_ngen_773_; lean_object* v_auxDeclNGen_774_; lean_object* v_traceState_775_; lean_object* v_messages_776_; lean_object* v_infoState_777_; lean_object* v_snapshotTasks_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_806_; 
v___x_770_ = lean_st_ref_take(v___y_767_);
v_env_771_ = lean_ctor_get(v___x_770_, 0);
v_nextMacroScope_772_ = lean_ctor_get(v___x_770_, 1);
v_ngen_773_ = lean_ctor_get(v___x_770_, 2);
v_auxDeclNGen_774_ = lean_ctor_get(v___x_770_, 3);
v_traceState_775_ = lean_ctor_get(v___x_770_, 4);
v_messages_776_ = lean_ctor_get(v___x_770_, 6);
v_infoState_777_ = lean_ctor_get(v___x_770_, 7);
v_snapshotTasks_778_ = lean_ctor_get(v___x_770_, 8);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v___x_770_, 5);
lean_dec(v_unused_807_);
v___x_780_ = v___x_770_;
v_isShared_781_ = v_isSharedCheck_806_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snapshotTasks_778_);
lean_inc(v_infoState_777_);
lean_inc(v_messages_776_);
lean_inc(v_traceState_775_);
lean_inc(v_auxDeclNGen_774_);
lean_inc(v_ngen_773_);
lean_inc(v_nextMacroScope_772_);
lean_inc(v_env_771_);
lean_dec(v___x_770_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_806_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_782_ = l_Lean_declRangeExt;
v___x_783_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_782_, v_env_771_, v_declName_764_, v_declRanges_765_);
v___x_784_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 5, v___x_784_);
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_nextMacroScope_772_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_ngen_773_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_auxDeclNGen_774_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_traceState_775_);
lean_ctor_set(v_reuseFailAlloc_805_, 5, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_805_, 6, v_messages_776_);
lean_ctor_set(v_reuseFailAlloc_805_, 7, v_infoState_777_);
lean_ctor_set(v_reuseFailAlloc_805_, 8, v_snapshotTasks_778_);
v___x_786_ = v_reuseFailAlloc_805_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_mctx_789_; lean_object* v_zetaDeltaFVarIds_790_; lean_object* v_postponed_791_; lean_object* v_diag_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_803_; 
v___x_787_ = lean_st_ref_set(v___y_767_, v___x_786_);
v___x_788_ = lean_st_ref_take(v___y_766_);
v_mctx_789_ = lean_ctor_get(v___x_788_, 0);
v_zetaDeltaFVarIds_790_ = lean_ctor_get(v___x_788_, 2);
v_postponed_791_ = lean_ctor_get(v___x_788_, 3);
v_diag_792_ = lean_ctor_get(v___x_788_, 4);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_788_, 1);
lean_dec(v_unused_804_);
v___x_794_ = v___x_788_;
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_diag_792_);
lean_inc(v_postponed_791_);
lean_inc(v_zetaDeltaFVarIds_790_);
lean_inc(v_mctx_789_);
lean_dec(v___x_788_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_mctx_789_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_zetaDeltaFVarIds_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_postponed_791_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_diag_792_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_st_ref_set(v___y_766_, v___x_798_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref(v_declRanges_765_);
lean_dec(v_declName_764_);
v___x_808_ = lean_box(0);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg___boxed(lean_object* v_declName_810_, lean_object* v_declRanges_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_810_, v_declRanges_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec(v___y_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(lean_object* v_declName_816_, lean_object* v_rangeStx_817_, lean_object* v_selectionRangeStx_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_841_; 
v___x_824_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_rangeStx_817_, v___y_821_);
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_841_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_841_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_841_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
if (lean_obj_tag(v_a_825_) == 1)
{
lean_object* v_val_829_; lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v_a_833_; 
lean_del_object(v___x_827_);
v_val_829_ = lean_ctor_get(v_a_825_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_a_825_, 1);
v___x_830_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_selectionRangeStx_818_, v___y_821_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
if (lean_obj_tag(v_a_831_) == 0)
{
lean_inc(v_val_829_);
v_a_833_ = v_val_829_;
goto v___jp_832_;
}
else
{
lean_object* v_val_836_; 
v_val_836_ = lean_ctor_get(v_a_831_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v_a_831_, 1);
v_a_833_ = v_val_836_;
goto v___jp_832_;
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_val_829_);
lean_ctor_set(v___x_834_, 1, v_a_833_);
v___x_835_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_816_, v___x_834_, v___y_820_, v___y_822_);
return v___x_835_;
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_a_825_);
lean_dec(v_declName_816_);
v___x_837_ = lean_box(0);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_837_);
v___x_839_ = v___x_827_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9___boxed(lean_object* v_declName_842_, lean_object* v_rangeStx_843_, lean_object* v_selectionRangeStx_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_declName_842_, v_rangeStx_843_, v_selectionRangeStx_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v_selectionRangeStx_844_);
lean_dec(v_rangeStx_843_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
if (lean_obj_tag(v_a_851_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = l_List_reverse___redArg(v_a_852_);
return v___x_853_;
}
else
{
lean_object* v_head_854_; lean_object* v_tail_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_864_; 
v_head_854_ = lean_ctor_get(v_a_851_, 0);
v_tail_855_ = lean_ctor_get(v_a_851_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_a_851_);
if (v_isSharedCheck_864_ == 0)
{
v___x_857_ = v_a_851_;
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_tail_855_);
lean_inc(v_head_854_);
lean_dec(v_a_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = l_Lean_mkLevelParam(v_head_854_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v_a_852_);
lean_ctor_set(v___x_857_, 0, v___x_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_a_852_);
v___x_861_ = v_reuseFailAlloc_863_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v_a_851_ = v_tail_855_;
v_a_852_ = v___x_861_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(lean_object* v_env_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_nextMacroScope_870_; lean_object* v_ngen_871_; lean_object* v_auxDeclNGen_872_; lean_object* v_traceState_873_; lean_object* v_messages_874_; lean_object* v_infoState_875_; lean_object* v_snapshotTasks_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_902_; 
v___x_869_ = lean_st_ref_take(v___y_867_);
v_nextMacroScope_870_ = lean_ctor_get(v___x_869_, 1);
v_ngen_871_ = lean_ctor_get(v___x_869_, 2);
v_auxDeclNGen_872_ = lean_ctor_get(v___x_869_, 3);
v_traceState_873_ = lean_ctor_get(v___x_869_, 4);
v_messages_874_ = lean_ctor_get(v___x_869_, 6);
v_infoState_875_ = lean_ctor_get(v___x_869_, 7);
v_snapshotTasks_876_ = lean_ctor_get(v___x_869_, 8);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; lean_object* v_unused_904_; 
v_unused_903_ = lean_ctor_get(v___x_869_, 5);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v___x_869_, 0);
lean_dec(v_unused_904_);
v___x_878_ = v___x_869_;
v_isShared_879_ = v_isSharedCheck_902_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_snapshotTasks_876_);
lean_inc(v_infoState_875_);
lean_inc(v_messages_874_);
lean_inc(v_traceState_873_);
lean_inc(v_auxDeclNGen_872_);
lean_inc(v_ngen_871_);
lean_inc(v_nextMacroScope_870_);
lean_dec(v___x_869_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_902_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 5, v___x_880_);
lean_ctor_set(v___x_878_, 0, v_env_865_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_env_865_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_nextMacroScope_870_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_ngen_871_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_auxDeclNGen_872_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_traceState_873_);
lean_ctor_set(v_reuseFailAlloc_901_, 5, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_901_, 6, v_messages_874_);
lean_ctor_set(v_reuseFailAlloc_901_, 7, v_infoState_875_);
lean_ctor_set(v_reuseFailAlloc_901_, 8, v_snapshotTasks_876_);
v___x_882_ = v_reuseFailAlloc_901_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_mctx_885_; lean_object* v_zetaDeltaFVarIds_886_; lean_object* v_postponed_887_; lean_object* v_diag_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_899_; 
v___x_883_ = lean_st_ref_set(v___y_867_, v___x_882_);
v___x_884_ = lean_st_ref_take(v___y_866_);
v_mctx_885_ = lean_ctor_get(v___x_884_, 0);
v_zetaDeltaFVarIds_886_ = lean_ctor_get(v___x_884_, 2);
v_postponed_887_ = lean_ctor_get(v___x_884_, 3);
v_diag_888_ = lean_ctor_get(v___x_884_, 4);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_884_, 1);
lean_dec(v_unused_900_);
v___x_890_ = v___x_884_;
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_diag_888_);
lean_inc(v_postponed_887_);
lean_inc(v_zetaDeltaFVarIds_886_);
lean_inc(v_mctx_885_);
lean_dec(v___x_884_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v___x_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_mctx_885_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_zetaDeltaFVarIds_886_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_postponed_887_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_diag_888_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_st_ref_set(v___y_866_, v___x_894_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg___boxed(lean_object* v_env_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec(v___y_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(lean_object* v_env_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v_env_918_; lean_object* v_a_920_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_917_ = lean_st_ref_get(v___y_915_);
v_env_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_env_918_);
lean_dec(v___x_917_);
v___x_930_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_910_, v___y_913_, v___y_915_);
lean_dec_ref(v___x_930_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
lean_inc(v___y_913_);
lean_inc_ref(v___y_912_);
v___x_931_ = lean_apply_5(v_x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, lean_box(0));
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_918_, v___y_913_, v___y_915_);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_933_, 0);
lean_dec(v_unused_941_);
v___x_935_ = v___x_933_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_dec(v___x_933_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_a_932_);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_932_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v_a_942_; 
v_a_942_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_931_, 1);
v_a_920_ = v_a_942_;
goto v___jp_919_;
}
v___jp_919_:
{
lean_object* v___x_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v___x_921_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_918_, v___y_913_, v___y_915_);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v___x_921_, 0);
lean_dec(v_unused_929_);
v___x_923_ = v___x_921_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_dec(v___x_921_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 1);
lean_ctor_set(v___x_923_, 0, v_a_920_);
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_920_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg___boxed(lean_object* v_env_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_943_, v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_box(0);
v___x_952_ = lean_unsigned_to_nat(16u);
v___x_953_ = lean_mk_array(v___x_952_, v___x_951_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_960_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
lean_ctor_set(v___x_961_, 2, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = l_Lean_Level_ofNat(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_box(0);
v___x_977_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_980_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_981_ = l_Lean_mkConst(v___x_980_, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_984_ = l_Lean_mkConst(v___x_983_, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
v___x_990_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_991_ = l_Lean_mkConst(v___x_990_, v___x_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_998_, lean_object* v_e_999_, lean_object* v_axiomDeclRange_x3f_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___x_1014_; lean_object* v_a_1015_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; uint8_t v___x_1121_; 
v___x_1014_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_999_, v_a_1002_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
v___x_1121_ = l_Lean_Expr_hasFVar(v_a_1015_);
if (v___x_1121_ == 0)
{
v___y_1100_ = v_a_1001_;
v___y_1101_ = v_a_1002_;
v___y_1102_ = v_a_1003_;
v___y_1103_ = v_a_1004_;
goto v___jp_1099_;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1123_ = l_Lean_MessageData_ofName(v_tacticName_998_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_indentExpr(v_a_1015_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1128_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
v___jp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1009_ = lean_box(0);
v___x_1010_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(v___y_1007_, v___x_1009_);
v___x_1011_ = l_Lean_mkConst(v___y_1008_, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
v___jp_1016_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_params_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1096_; 
v___x_1021_ = lean_st_ref_get(v___y_1020_);
v___x_1022_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1015_);
v___x_1023_ = l_Lean_collectLevelParams(v___x_1022_, v_a_1015_);
v_params_1024_ = lean_ctor_get(v___x_1023_, 2);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1097_ = lean_ctor_get(v___x_1023_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v___x_1023_, 0);
lean_dec(v_unused_1098_);
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1096_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_params_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1096_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_env_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_env_1028_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_env_1028_);
lean_dec(v___x_1021_);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_array_to_list(v_params_1024_);
v___x_1031_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_998_);
v___x_1032_ = l_Lean_Name_append(v___x_1031_, v_tacticName_998_);
v___x_1033_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1032_);
v___x_1034_ = l_Lean_Name_append(v___x_1032_, v___x_1033_);
lean_inc(v_a_1015_);
lean_inc(v___x_1030_);
v___f_1035_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1035_, 0, v___x_1034_);
lean_closure_set(v___f_1035_, 1, v___x_1030_);
lean_closure_set(v___f_1035_, 2, v___x_1029_);
lean_closure_set(v___f_1035_, 3, v_tacticName_998_);
lean_closure_set(v___f_1035_, 4, v_a_1015_);
v___x_1036_ = l_Lean_Environment_unlockAsync(v_env_1028_);
v___x_1037_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v___x_1036_, v___f_1035_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1087_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1087_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1087_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_unbox(v_a_1038_);
lean_dec(v_a_1038_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_dec(v___x_1032_);
lean_dec(v___x_1030_);
lean_del_object(v___x_1026_);
lean_dec(v_a_1015_);
v___x_1043_ = lean_box(1);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1043_);
v___x_1045_ = v___x_1040_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_1040_);
v___x_1047_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1048_ = l_Lean_Name_append(v___x_1032_, v___x_1047_);
v___x_1049_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1048_, v___y_1020_);
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1086_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1086_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1054_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1055_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1056_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1057_ = l_Lean_mkApp3(v___x_1054_, v___x_1055_, v_a_1015_, v___x_1056_);
lean_inc(v___x_1030_);
lean_inc(v_a_1050_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 2, v___x_1057_);
lean_ctor_set(v___x_1026_, 1, v___x_1030_);
lean_ctor_set(v___x_1026_, 0, v_a_1050_);
v___x_1059_ = v___x_1026_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1050_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1060_ = 0;
v___x_1061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*1, v___x_1060_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1061_);
v___x_1063_ = v___x_1052_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_addDecl(v___x_1063_, v___x_1060_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_dec_ref_known(v___x_1064_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1000_) == 1)
{
lean_object* v_val_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_val_1065_ = lean_ctor_get(v_axiomDeclRange_x3f_1000_, 0);
v___x_1066_ = lean_box(0);
lean_inc(v_a_1050_);
v___x_1067_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_a_1050_, v_val_1065_, v___x_1066_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_dec_ref_known(v___x_1067_, 1);
v___y_1007_ = v___x_1030_;
v___y_1008_ = v_a_1050_;
goto v___jp_1006_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1050_);
lean_dec(v___x_1030_);
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
v___y_1007_ = v___x_1030_;
v___y_1008_ = v_a_1050_;
goto v___jp_1006_;
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_a_1050_);
lean_dec(v___x_1030_);
v_a_1076_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1064_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1064_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
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
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v___x_1032_);
lean_dec(v___x_1030_);
lean_del_object(v___x_1026_);
lean_dec(v_a_1015_);
v_a_1088_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1037_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1037_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
v___jp_1099_:
{
uint8_t v___x_1104_; 
v___x_1104_ = l_Lean_Expr_hasMVar(v_a_1015_);
if (v___x_1104_ == 0)
{
v___y_1017_ = v___y_1100_;
v___y_1018_ = v___y_1101_;
v___y_1019_ = v___y_1102_;
v___y_1020_ = v___y_1103_;
goto v___jp_1016_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v___x_1105_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1106_ = l_Lean_MessageData_ofName(v_tacticName_998_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_indentExpr(v_a_1015_);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1111_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1138_, lean_object* v_e_1139_, lean_object* v_axiomDeclRange_x3f_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1138_, v_e_1139_, v_axiomDeclRange_x3f_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_axiomDeclRange_x3f_1140_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1161_, lean_object* v_constName_1162_, uint8_t v_checkMeta_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1162_, v_checkMeta_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1170_, lean_object* v_constName_1171_, lean_object* v_checkMeta_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v_checkMeta_boxed_1178_; lean_object* v_res_1179_; 
v_checkMeta_boxed_1178_ = lean_unbox(v_checkMeta_1172_);
v_res_1179_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1170_, v_constName_1171_, v_checkMeta_boxed_1178_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1180_, lean_object* v_msg_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1188_, lean_object* v_msg_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1188_, v_msg_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11(lean_object* v_env_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___redArg(v_env_1196_, v___y_1198_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11___boxed(lean_object* v_env_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__11(v_env_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_00_u03b1_1210_, lean_object* v_env_1211_, lean_object* v_x_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_1211_, v_x_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_env_1220_, lean_object* v_x_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(v_00_u03b1_1219_, v_env_1220_, v_x_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14(lean_object* v_stx_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___redArg(v_stx_1228_, v___y_1231_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14___boxed(lean_object* v_stx_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__14(v_stx_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v_stx_1235_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(lean_object* v_declName_1242_, lean_object* v_declRanges_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_declName_1242_, v_declRanges_1243_, v___y_1245_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___boxed(lean_object* v_declName_1250_, lean_object* v_declRanges_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(v_declName_1250_, v_declRanges_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1258_, lean_object* v_x_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1266_, v_x_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

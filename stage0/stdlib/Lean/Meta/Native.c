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
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = l_Lean_Core_instMonadOptionsCoreM;
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__15));
v___x_73_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19(void){
_start:
{
lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__18);
v___f_75_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__13));
v___x_76_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___f_75_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1(lean_object* v_auxDeclName_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_83_; lean_object* v_toApplicative_84_; lean_object* v_toFunctor_85_; lean_object* v_toSeq_86_; lean_object* v_toSeqLeft_87_; lean_object* v_toSeqRight_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_toApplicative_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_138_; 
v___x_83_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__1);
v_toApplicative_84_ = lean_ctor_get(v___x_83_, 0);
v_toFunctor_85_ = lean_ctor_get(v_toApplicative_84_, 0);
v_toSeq_86_ = lean_ctor_get(v_toApplicative_84_, 2);
v_toSeqLeft_87_ = lean_ctor_get(v_toApplicative_84_, 3);
v_toSeqRight_88_ = lean_ctor_get(v_toApplicative_84_, 4);
v___f_89_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__2));
v___f_90_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__3));
lean_inc_ref_n(v_toFunctor_85_, 2);
v___f_91_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_91_, 0, v_toFunctor_85_);
v___f_92_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_92_, 0, v_toFunctor_85_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___f_91_);
lean_ctor_set(v___x_93_, 1, v___f_92_);
lean_inc(v_toSeqRight_88_);
v___f_94_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_94_, 0, v_toSeqRight_88_);
lean_inc(v_toSeqLeft_87_);
v___f_95_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_95_, 0, v_toSeqLeft_87_);
lean_inc(v_toSeq_86_);
v___f_96_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_96_, 0, v_toSeq_86_);
v___x_97_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_97_, 0, v___x_93_);
lean_ctor_set(v___x_97_, 1, v___f_89_);
lean_ctor_set(v___x_97_, 2, v___f_96_);
lean_ctor_set(v___x_97_, 3, v___f_95_);
lean_ctor_set(v___x_97_, 4, v___f_94_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___f_90_);
v___x_99_ = l_StateRefT_x27_instMonad___redArg(v___x_98_);
v_toApplicative_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v___x_99_, 1);
lean_dec(v_unused_139_);
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_138_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_toApplicative_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_138_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_toFunctor_104_; lean_object* v_toSeq_105_; lean_object* v_toSeqLeft_106_; lean_object* v_toSeqRight_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_136_; 
v_toFunctor_104_ = lean_ctor_get(v_toApplicative_100_, 0);
v_toSeq_105_ = lean_ctor_get(v_toApplicative_100_, 2);
v_toSeqLeft_106_ = lean_ctor_get(v_toApplicative_100_, 3);
v_toSeqRight_107_ = lean_ctor_get(v_toApplicative_100_, 4);
v_isSharedCheck_136_ = !lean_is_exclusive(v_toApplicative_100_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_toApplicative_100_, 1);
lean_dec(v_unused_137_);
v___x_109_ = v_toApplicative_100_;
v_isShared_110_ = v_isSharedCheck_136_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_toSeqRight_107_);
lean_inc(v_toSeqLeft_106_);
lean_inc(v_toSeq_105_);
lean_inc(v_toFunctor_104_);
lean_dec(v_toApplicative_100_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_136_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___x_120_; 
v___f_111_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__4));
v___f_112_ = ((lean_object*)(l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__5));
lean_inc_ref(v_toFunctor_104_);
v___f_113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_113_, 0, v_toFunctor_104_);
v___f_114_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_114_, 0, v_toFunctor_104_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___f_113_);
lean_ctor_set(v___x_115_, 1, v___f_114_);
v___f_116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_116_, 0, v_toSeqRight_107_);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_117_, 0, v_toSeqLeft_106_);
v___f_118_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_118_, 0, v_toSeq_105_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v___f_116_);
lean_ctor_set(v___x_109_, 3, v___f_117_);
lean_ctor_set(v___x_109_, 2, v___f_118_);
lean_ctor_set(v___x_109_, 1, v___f_111_);
lean_ctor_set(v___x_109_, 0, v___x_115_);
v___x_120_ = v___x_109_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___f_111_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v___f_118_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v___f_117_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v___f_116_);
v___x_120_ = v_reuseFailAlloc_135_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_122_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___f_112_);
lean_ctor_set(v___x_102_, 0, v___x_120_);
v___x_122_ = v___x_102_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___f_112_);
v___x_122_ = v_reuseFailAlloc_134_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v_toMonadRef_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_63__overap_132_; lean_object* v___x_133_; 
v___x_123_ = l_Lean_Meta_instMonadEnvMetaM;
v___x_124_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__11);
v___x_125_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__17);
v_toMonadRef_126_ = lean_ctor_get(v___x_125_, 0);
v___x_127_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_122_);
v___x_128_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_127_, v___x_122_);
lean_inc_ref(v_toMonadRef_126_);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_124_);
lean_ctor_set(v___x_129_, 1, v_toMonadRef_126_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
v___x_130_ = lean_obj_once(&l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19, &l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19_once, _init_l___private_Lean_Meta_Native_0__Lean_Meta_nativeEqTrue_unsafe__1___closed__19);
v___x_131_ = 1;
v___x_63__overap_132_ = l_Lean_evalConst___redArg(v___x_122_, v___x_123_, v___x_129_, v___x_130_, v_auxDeclName_77_, v___x_131_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
lean_inc(v_a_79_);
lean_inc_ref(v_a_78_);
v___x_133_ = lean_apply_5(v___x_63__overap_132_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, lean_box(0));
return v___x_133_;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(lean_object* v_e_147_, lean_object* v___y_148_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg___boxed(lean_object* v_e_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_172_, v___y_173_);
lean_dec(v___y_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(lean_object* v_e_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_176_, v___y_178_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___boxed(lean_object* v_e_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0(v_e_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(lean_object* v_kind_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_auxDeclNGen_194_; lean_object* v___x_195_; lean_object* v_env_196_; lean_object* v___x_197_; lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___x_200_; lean_object* v_env_201_; lean_object* v_nextMacroScope_202_; lean_object* v_ngen_203_; lean_object* v_traceState_204_; lean_object* v_cache_205_; lean_object* v_recordedDeps_206_; lean_object* v_messages_207_; lean_object* v_infoState_208_; lean_object* v_snapshotTasks_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_218_; 
v___x_193_ = lean_st_ref_get(v___y_191_);
v_auxDeclNGen_194_ = lean_ctor_get(v___x_193_, 3);
lean_inc_ref(v_auxDeclNGen_194_);
lean_dec(v___x_193_);
v___x_195_ = lean_st_ref_get(v___y_191_);
v_env_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc_ref(v_env_196_);
lean_dec(v___x_195_);
v___x_197_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_196_, v_auxDeclNGen_194_, v_kind_190_);
v_fst_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_fst_198_);
v_snd_199_ = lean_ctor_get(v___x_197_, 1);
lean_inc(v_snd_199_);
lean_dec_ref(v___x_197_);
v___x_200_ = lean_st_ref_take(v___y_191_);
v_env_201_ = lean_ctor_get(v___x_200_, 0);
v_nextMacroScope_202_ = lean_ctor_get(v___x_200_, 1);
v_ngen_203_ = lean_ctor_get(v___x_200_, 2);
v_traceState_204_ = lean_ctor_get(v___x_200_, 4);
v_cache_205_ = lean_ctor_get(v___x_200_, 5);
v_recordedDeps_206_ = lean_ctor_get(v___x_200_, 6);
v_messages_207_ = lean_ctor_get(v___x_200_, 7);
v_infoState_208_ = lean_ctor_get(v___x_200_, 8);
v_snapshotTasks_209_ = lean_ctor_get(v___x_200_, 9);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_200_, 3);
lean_dec(v_unused_219_);
v___x_211_ = v___x_200_;
v_isShared_212_ = v_isSharedCheck_218_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_snapshotTasks_209_);
lean_inc(v_infoState_208_);
lean_inc(v_messages_207_);
lean_inc(v_recordedDeps_206_);
lean_inc(v_cache_205_);
lean_inc(v_traceState_204_);
lean_inc(v_ngen_203_);
lean_inc(v_nextMacroScope_202_);
lean_inc(v_env_201_);
lean_dec(v___x_200_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_218_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 3, v_snd_199_);
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_env_201_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_nextMacroScope_202_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_ngen_203_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_snd_199_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_traceState_204_);
lean_ctor_set(v_reuseFailAlloc_217_, 5, v_cache_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 6, v_recordedDeps_206_);
lean_ctor_set(v_reuseFailAlloc_217_, 7, v_messages_207_);
lean_ctor_set(v_reuseFailAlloc_217_, 8, v_infoState_208_);
lean_ctor_set(v_reuseFailAlloc_217_, 9, v_snapshotTasks_209_);
v___x_214_ = v_reuseFailAlloc_217_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_st_ref_put(v___y_191_, v___x_214_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v_fst_198_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg___boxed(lean_object* v_kind_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_220_, v___y_221_);
lean_dec(v___y_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(lean_object* v_kind_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v_kind_224_, v___y_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___boxed(lean_object* v_kind_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1(v_kind_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_opts_238_, lean_object* v_opt_239_){
_start:
{
lean_object* v_name_240_; lean_object* v_defValue_241_; lean_object* v_map_242_; lean_object* v___x_243_; 
v_name_240_ = lean_ctor_get(v_opt_239_, 0);
v_defValue_241_ = lean_ctor_get(v_opt_239_, 1);
v_map_242_ = lean_ctor_get(v_opts_238_, 0);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_242_, v_name_240_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_inc(v_defValue_241_);
return v_defValue_241_;
}
else
{
lean_object* v_val_244_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v___x_243_, 1);
if (lean_obj_tag(v_val_244_) == 3)
{
lean_object* v_v_245_; 
v_v_245_ = lean_ctor_get(v_val_244_, 0);
lean_inc(v_v_245_);
lean_dec_ref_known(v_val_244_, 1);
return v_v_245_;
}
else
{
lean_dec(v_val_244_);
lean_inc(v_defValue_241_);
return v_defValue_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v_opts_246_, v_opt_247_);
lean_dec_ref(v_opt_247_);
lean_dec_ref(v_opts_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_env_256_; lean_object* v___x_257_; lean_object* v_toCold_258_; lean_object* v_mctx_259_; lean_object* v_lctx_260_; lean_object* v_options_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_255_ = lean_st_ref_get(v___y_253_);
v_env_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_env_256_);
lean_dec(v___x_255_);
v___x_257_ = lean_st_ref_get(v___y_251_);
v_toCold_258_ = lean_ctor_get(v___y_252_, 0);
v_mctx_259_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_mctx_259_);
lean_dec(v___x_257_);
v_lctx_260_ = lean_ctor_get(v___y_250_, 2);
v_options_261_ = lean_ctor_get(v_toCold_258_, 2);
lean_inc_ref(v_options_261_);
lean_inc_ref(v_lctx_260_);
v___x_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_262_, 0, v_env_256_);
lean_ctor_set(v___x_262_, 1, v_mctx_259_);
lean_ctor_set(v___x_262_, 2, v_lctx_260_);
lean_ctor_set(v___x_262_, 3, v_options_261_);
v___x_263_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_msgData_249_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object* v_msgData_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msgData_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object* v_msg_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_ref_278_; lean_object* v___x_279_; lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v_ref_278_ = lean_ctor_get(v___y_275_, 2);
v___x_279_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msg_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_288_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
lean_inc(v_ref_278_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_ref_278_);
lean_ctor_set(v___x_284_, 1, v_a_280_);
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 1);
lean_ctor_set(v___x_282_, 0, v___x_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(lean_object* v_o_299_, lean_object* v_k_300_, uint8_t v_v_301_){
_start:
{
lean_object* v_map_302_; uint8_t v_hasTrace_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_317_; 
v_map_302_ = lean_ctor_get(v_o_299_, 0);
v_hasTrace_303_ = lean_ctor_get_uint8(v_o_299_, sizeof(void*)*1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_o_299_);
if (v_isSharedCheck_317_ == 0)
{
v___x_305_ = v_o_299_;
v_isShared_306_ = v_isSharedCheck_317_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_map_302_);
lean_dec(v_o_299_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_317_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_307_, 0, v_v_301_);
lean_inc(v_k_300_);
v___x_308_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_300_, v___x_307_, v_map_302_);
if (v_hasTrace_303_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_312_; 
v___x_309_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___closed__1));
v___x_310_ = l_Lean_Name_isPrefixOf(v___x_309_, v_k_300_);
lean_dec(v_k_300_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_312_ = v___x_305_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_308_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*1, v___x_310_);
return v___x_312_;
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v_k_300_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_315_ = v___x_305_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*1, v_hasTrace_303_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___boxed(lean_object* v_o_318_, lean_object* v_k_319_, lean_object* v_v_320_){
_start:
{
uint8_t v_v_boxed_321_; lean_object* v_res_322_; 
v_v_boxed_321_ = lean_unbox(v_v_320_);
v_res_322_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(v_o_318_, v_k_319_, v_v_boxed_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_323_, lean_object* v_opt_324_, uint8_t v_val_325_){
_start:
{
lean_object* v_name_326_; lean_object* v___x_327_; 
v_name_326_ = lean_ctor_get(v_opt_324_, 0);
lean_inc(v_name_326_);
lean_dec_ref(v_opt_324_);
v___x_327_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(v_opts_323_, v_name_326_, v_val_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_328_, lean_object* v_opt_329_, lean_object* v_val_330_){
_start:
{
uint8_t v_val_boxed_331_; lean_object* v_res_332_; 
v_val_boxed_331_ = lean_unbox(v_val_330_);
v_res_332_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_328_, v_opt_329_, v_val_boxed_331_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_box(0);
v___x_334_ = l_Lean_Elab_abortCommandExceptionId;
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___boxed(lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(lean_object* v_x_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_347_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v_x_341_, 1);
v___x_348_ = l_Lean_stringToMessageData(v_a_347_);
v___x_349_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_348_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_a_350_ = lean_ctor_get(v_x_341_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v_x_341_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v_x_341_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 0);
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg___boxed(lean_object* v_x_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(lean_object* v_constName_365_, uint8_t v_checkMeta_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v_env_373_; uint8_t v___x_374_; 
v___x_372_ = lean_st_ref_get(v___y_370_);
v_env_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_ref(v_env_373_);
lean_dec(v___x_372_);
lean_inc(v_constName_365_);
v___x_374_ = lean_has_compile_error(v_env_373_, v_constName_365_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v_env_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_375_ = lean_st_ref_get(v___y_370_);
v_env_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_376_);
lean_dec(v___x_375_);
v___x_377_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_369_);
v___x_378_ = l_Lean_Environment_evalConst___redArg(v_env_376_, v___x_377_, v_constName_365_, v_checkMeta_366_);
lean_dec(v_constName_365_);
lean_dec_ref(v___x_377_);
lean_dec_ref(v_env_376_);
v___x_379_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_378_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_381_; lean_object* v_env_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref_known(v___x_380_, 1);
v___x_381_ = lean_st_ref_get(v___y_370_);
v_env_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_381_);
v___x_383_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_369_);
v___x_384_ = l_Lean_Environment_evalConst___redArg(v_env_382_, v___x_383_, v_constName_365_, v_checkMeta_366_);
lean_dec(v_constName_365_);
lean_dec_ref(v___x_383_);
lean_dec_ref(v_env_382_);
v___x_385_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_384_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_constName_365_);
v_a_386_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_380_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_380_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg___boxed(lean_object* v_constName_394_, lean_object* v_checkMeta_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
uint8_t v_checkMeta_boxed_401_; lean_object* v_res_402_; 
v_checkMeta_boxed_401_ = lean_unbox(v_checkMeta_395_);
v_res_402_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_394_, v_checkMeta_boxed_401_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_402_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__4));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_417_ = l_Lean_mkConst(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
v___x_424_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
lean_ctor_set(v___x_424_, 2, v___x_423_);
lean_ctor_set(v___x_424_, 3, v___x_423_);
lean_ctor_set(v___x_424_, 4, v___x_423_);
lean_ctor_set(v___x_424_, 5, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v_tacticName_425_, lean_object* v___x_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v_a_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___x_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_753_; 
v___x_447_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_426_, v___y_433_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_753_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_753_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_753_;
goto v_resetjp_449_;
}
v___jp_435_:
{
if (v___y_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v___y_437_);
v___x_439_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_440_ = l_Lean_MessageData_ofName(v_tacticName_425_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_Exception_toMessageData(v___y_436_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_445_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec_ref(v___y_432_);
return v___x_446_;
}
else
{
lean_dec_ref(v___y_436_);
lean_dec_ref(v___y_432_);
lean_dec(v_tacticName_425_);
return v___y_437_;
}
}
v_resetjp_449_:
{
lean_object* v___y_453_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___y_470_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_479_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
lean_inc_n(v_a_448_, 2);
v___x_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_480_, 0, v_a_448_);
lean_ctor_set(v___x_480_, 1, v___x_427_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
v___x_481_ = lean_box(1);
v___x_482_ = 1;
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v_a_448_);
lean_ctor_set(v___x_483_, 1, v___x_428_);
v___x_484_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_484_, 0, v___x_480_);
lean_ctor_set(v___x_484_, 1, v_a_429_);
lean_ctor_set(v___x_484_, 2, v___x_481_);
lean_ctor_set(v___x_484_, 3, v___x_483_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*4, v___x_482_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 0, v___x_484_);
v___x_486_ = v___x_450_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_752_;
goto v_reusejp_485_;
}
v___jp_452_:
{
if (lean_obj_tag(v___y_453_) == 0)
{
uint8_t v___x_454_; lean_object* v___x_455_; 
lean_dec_ref_known(v___y_453_, 1);
v___x_454_ = 1;
v___x_455_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_a_448_, v___x_454_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_dec_ref(v___y_432_);
lean_dec(v_tacticName_425_);
return v___x_455_;
}
else
{
lean_object* v_a_456_; uint8_t v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
v___x_457_ = l_Lean_Exception_isInterrupt(v_a_456_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
lean_inc(v_a_456_);
v___x_458_ = l_Lean_Exception_isRuntime(v_a_456_);
v___y_436_ = v_a_456_;
v___y_437_ = v___x_455_;
v___y_438_ = v___x_458_;
goto v___jp_435_;
}
else
{
v___y_436_ = v_a_456_;
v___y_437_ = v___x_455_;
v___y_438_ = v___x_457_;
goto v___jp_435_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_a_448_);
lean_dec_ref(v___y_432_);
lean_dec(v_tacticName_425_);
v_a_459_ = lean_ctor_get(v___y_453_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___y_453_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___y_453_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___y_453_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
v___jp_467_:
{
if (v___y_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v___y_468_);
v___x_471_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
lean_inc(v_tacticName_425_);
v___x_472_ = l_Lean_MessageData_ofName(v_tacticName_425_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__5, &l_Lean_Meta_nativeEqTrue___lam__0___closed__5_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__5);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_Exception_toMessageData(v___y_469_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_477_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
v___y_453_ = v___x_478_;
goto v___jp_452_;
}
else
{
lean_dec_ref(v___y_469_);
v___y_453_ = v___y_468_;
goto v___jp_452_;
}
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v_env_488_; lean_object* v_nextMacroScope_489_; lean_object* v_ngen_490_; lean_object* v_auxDeclNGen_491_; lean_object* v_traceState_492_; lean_object* v_recordedDeps_493_; lean_object* v_messages_494_; lean_object* v_infoState_495_; lean_object* v_snapshotTasks_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_750_; 
v___x_487_ = lean_st_ref_take(v___y_433_);
v_env_488_ = lean_ctor_get(v___x_487_, 0);
v_nextMacroScope_489_ = lean_ctor_get(v___x_487_, 1);
v_ngen_490_ = lean_ctor_get(v___x_487_, 2);
v_auxDeclNGen_491_ = lean_ctor_get(v___x_487_, 3);
v_traceState_492_ = lean_ctor_get(v___x_487_, 4);
v_recordedDeps_493_ = lean_ctor_get(v___x_487_, 6);
v_messages_494_ = lean_ctor_get(v___x_487_, 7);
v_infoState_495_ = lean_ctor_get(v___x_487_, 8);
v_snapshotTasks_496_ = lean_ctor_get(v___x_487_, 9);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_487_, 5);
lean_dec(v_unused_751_);
v___x_498_ = v___x_487_;
v_isShared_499_ = v_isSharedCheck_750_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_snapshotTasks_496_);
lean_inc(v_infoState_495_);
lean_inc(v_messages_494_);
lean_inc(v_recordedDeps_493_);
lean_inc(v_traceState_492_);
lean_inc(v_auxDeclNGen_491_);
lean_inc(v_ngen_490_);
lean_inc(v_nextMacroScope_489_);
lean_inc(v_env_488_);
lean_dec(v___x_487_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_750_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_inc(v_a_448_);
v___x_500_ = l_Lean_markMeta(v_env_488_, v_a_448_);
v___x_501_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 5, v___x_501_);
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_nextMacroScope_489_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_ngen_490_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_auxDeclNGen_491_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_traceState_492_);
lean_ctor_set(v_reuseFailAlloc_749_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_749_, 6, v_recordedDeps_493_);
lean_ctor_set(v_reuseFailAlloc_749_, 7, v_messages_494_);
lean_ctor_set(v_reuseFailAlloc_749_, 8, v_infoState_495_);
lean_ctor_set(v_reuseFailAlloc_749_, 9, v_snapshotTasks_496_);
v___x_503_ = v_reuseFailAlloc_749_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_mctx_506_; lean_object* v_zetaDeltaFVarIds_507_; lean_object* v_postponed_508_; lean_object* v_diag_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_747_; 
v___x_504_ = lean_st_ref_put(v___y_433_, v___x_503_);
v___x_505_ = lean_st_ref_take(v___y_431_);
v_mctx_506_ = lean_ctor_get(v___x_505_, 0);
v_zetaDeltaFVarIds_507_ = lean_ctor_get(v___x_505_, 2);
v_postponed_508_ = lean_ctor_get(v___x_505_, 3);
v_diag_509_ = lean_ctor_get(v___x_505_, 4);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_505_, 1);
lean_dec(v_unused_748_);
v___x_511_ = v___x_505_;
v_isShared_512_ = v_isSharedCheck_747_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_diag_509_);
lean_inc(v_postponed_508_);
lean_inc(v_zetaDeltaFVarIds_507_);
lean_inc(v_mctx_506_);
lean_dec(v___x_505_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_747_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_mctx_506_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_zetaDeltaFVarIds_507_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_postponed_508_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_diag_509_);
v___x_515_ = v_reuseFailAlloc_746_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v_toCold_517_; lean_object* v_currRecDepth_518_; lean_object* v_ref_519_; uint8_t v_suppressElabErrors_520_; uint8_t v_isRecordingDeps_521_; lean_object* v_fileName_522_; lean_object* v_fileMap_523_; lean_object* v_options_524_; lean_object* v_currNamespace_525_; lean_object* v_openDecls_526_; lean_object* v_initHeartbeats_527_; lean_object* v_maxHeartbeats_528_; lean_object* v_quotContext_529_; lean_object* v_currMacroScope_530_; lean_object* v_cancelTk_x3f_531_; lean_object* v_inheritedTraceOptions_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_744_; 
v___x_516_ = lean_st_ref_put(v___y_431_, v___x_515_);
v_toCold_517_ = lean_ctor_get(v___y_432_, 0);
lean_inc_ref(v_toCold_517_);
v_currRecDepth_518_ = lean_ctor_get(v___y_432_, 1);
v_ref_519_ = lean_ctor_get(v___y_432_, 2);
v_suppressElabErrors_520_ = lean_ctor_get_uint8(v___y_432_, sizeof(void*)*3 + 2);
v_isRecordingDeps_521_ = lean_ctor_get_uint8(v___y_432_, sizeof(void*)*3 + 3);
v_fileName_522_ = lean_ctor_get(v_toCold_517_, 0);
v_fileMap_523_ = lean_ctor_get(v_toCold_517_, 1);
v_options_524_ = lean_ctor_get(v_toCold_517_, 2);
v_currNamespace_525_ = lean_ctor_get(v_toCold_517_, 4);
v_openDecls_526_ = lean_ctor_get(v_toCold_517_, 5);
v_initHeartbeats_527_ = lean_ctor_get(v_toCold_517_, 6);
v_maxHeartbeats_528_ = lean_ctor_get(v_toCold_517_, 7);
v_quotContext_529_ = lean_ctor_get(v_toCold_517_, 8);
v_currMacroScope_530_ = lean_ctor_get(v_toCold_517_, 9);
v_cancelTk_x3f_531_ = lean_ctor_get(v_toCold_517_, 10);
v_inheritedTraceOptions_532_ = lean_ctor_get(v_toCold_517_, 11);
v_isSharedCheck_744_ = !lean_is_exclusive(v_toCold_517_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_toCold_517_, 3);
lean_dec(v_unused_745_);
v___x_534_ = v_toCold_517_;
v_isShared_535_ = v_isSharedCheck_744_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_inheritedTraceOptions_532_);
lean_inc(v_cancelTk_x3f_531_);
lean_inc(v_currMacroScope_530_);
lean_inc(v_quotContext_529_);
lean_inc(v_maxHeartbeats_528_);
lean_inc(v_initHeartbeats_527_);
lean_inc(v_openDecls_526_);
lean_inc(v_currNamespace_525_);
lean_inc(v_options_524_);
lean_inc(v_fileMap_523_);
lean_inc(v_fileName_522_);
lean_dec(v_toCold_517_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_744_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v___x_536_; uint8_t v___x_537_; uint16_t v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v_fileName_542_; lean_object* v_fileMap_543_; lean_object* v_currNamespace_544_; lean_object* v_openDecls_545_; lean_object* v_initHeartbeats_546_; lean_object* v_maxHeartbeats_547_; lean_object* v_quotContext_548_; lean_object* v_currMacroScope_549_; lean_object* v_cancelTk_x3f_550_; lean_object* v_inheritedTraceOptions_551_; lean_object* v_currRecDepth_552_; lean_object* v_ref_553_; uint8_t v_suppressElabErrors_554_; uint8_t v_isRecordingDeps_555_; lean_object* v___y_556_; uint16_t v___y_567_; lean_object* v___y_568_; uint8_t v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_609_; lean_object* v___y_610_; uint16_t v___y_611_; lean_object* v_fileName_612_; lean_object* v_fileMap_613_; lean_object* v_currNamespace_614_; lean_object* v_openDecls_615_; lean_object* v_initHeartbeats_616_; lean_object* v_maxHeartbeats_617_; lean_object* v_quotContext_618_; lean_object* v_currMacroScope_619_; lean_object* v_cancelTk_x3f_620_; lean_object* v_inheritedTraceOptions_621_; lean_object* v_currRecDepth_622_; lean_object* v_ref_623_; uint8_t v_suppressElabErrors_624_; uint8_t v_isRecordingDeps_625_; lean_object* v___y_626_; uint8_t v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint16_t v___y_645_; lean_object* v___y_646_; lean_object* v___x_682_; lean_object* v___x_683_; uint16_t v___x_684_; lean_object* v_fileName_686_; lean_object* v_fileMap_687_; lean_object* v_currNamespace_688_; lean_object* v_openDecls_689_; lean_object* v_initHeartbeats_690_; lean_object* v_maxHeartbeats_691_; lean_object* v_quotContext_692_; lean_object* v_currMacroScope_693_; lean_object* v_cancelTk_x3f_694_; lean_object* v_inheritedTraceOptions_695_; lean_object* v_currRecDepth_696_; lean_object* v_ref_697_; uint8_t v_suppressElabErrors_698_; uint8_t v_isRecordingDeps_699_; lean_object* v___y_700_; lean_object* v___x_715_; uint8_t v___y_717_; lean_object* v_env_738_; uint8_t v___x_739_; uint16_t v___x_740_; uint16_t v___x_741_; uint16_t v___x_742_; uint8_t v___x_743_; 
v___x_536_ = 1;
v___x_537_ = 0;
v___x_682_ = l_Lean_Elab_async;
v___x_683_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v_options_524_, v___x_682_, v___x_537_);
v___x_684_ = l_Lean_OptionFlags_ofOptions(v___x_683_);
v___x_715_ = lean_st_ref_get(v___y_433_);
v_env_738_ = lean_ctor_get(v___x_715_, 0);
lean_inc_ref(v_env_738_);
lean_dec(v___x_715_);
v___x_739_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_738_);
lean_dec_ref(v_env_738_);
v___x_740_ = 512;
v___x_741_ = lean_uint16_land(v___x_684_, v___x_740_);
v___x_742_ = 0;
v___x_743_ = lean_uint16_dec_eq(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
if (v___x_739_ == 0)
{
v___y_717_ = v___x_536_;
goto v___jp_716_;
}
else
{
lean_inc(v_ref_519_);
lean_inc(v_currRecDepth_518_);
v_fileName_686_ = v_fileName_522_;
v_fileMap_687_ = v_fileMap_523_;
v_currNamespace_688_ = v_currNamespace_525_;
v_openDecls_689_ = v_openDecls_526_;
v_initHeartbeats_690_ = v_initHeartbeats_527_;
v_maxHeartbeats_691_ = v_maxHeartbeats_528_;
v_quotContext_692_ = v_quotContext_529_;
v_currMacroScope_693_ = v_currMacroScope_530_;
v_cancelTk_x3f_694_ = v_cancelTk_x3f_531_;
v_inheritedTraceOptions_695_ = v_inheritedTraceOptions_532_;
v_currRecDepth_696_ = v_currRecDepth_518_;
v_ref_697_ = v_ref_519_;
v_suppressElabErrors_698_ = v_suppressElabErrors_520_;
v_isRecordingDeps_699_ = v_isRecordingDeps_521_;
v___y_700_ = v___y_433_;
goto v___jp_685_;
}
}
else
{
if (v___x_739_ == 0)
{
lean_inc(v_ref_519_);
lean_inc(v_currRecDepth_518_);
v_fileName_686_ = v_fileName_522_;
v_fileMap_687_ = v_fileMap_523_;
v_currNamespace_688_ = v_currNamespace_525_;
v_openDecls_689_ = v_openDecls_526_;
v_initHeartbeats_690_ = v_initHeartbeats_527_;
v_maxHeartbeats_691_ = v_maxHeartbeats_528_;
v_quotContext_692_ = v_quotContext_529_;
v_currMacroScope_693_ = v_currMacroScope_530_;
v_cancelTk_x3f_694_ = v_cancelTk_x3f_531_;
v_inheritedTraceOptions_695_ = v_inheritedTraceOptions_532_;
v_currRecDepth_696_ = v_currRecDepth_518_;
v_ref_697_ = v_ref_519_;
v_suppressElabErrors_698_ = v_suppressElabErrors_520_;
v_isRecordingDeps_699_ = v_isRecordingDeps_521_;
v___y_700_ = v___y_433_;
goto v___jp_685_;
}
else
{
v___y_717_ = v___x_537_;
goto v___jp_716_;
}
}
v___jp_538_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_541_, v___y_540_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 11, v_inheritedTraceOptions_551_);
lean_ctor_set(v___x_534_, 10, v_cancelTk_x3f_550_);
lean_ctor_set(v___x_534_, 9, v_currMacroScope_549_);
lean_ctor_set(v___x_534_, 8, v_quotContext_548_);
lean_ctor_set(v___x_534_, 7, v_maxHeartbeats_547_);
lean_ctor_set(v___x_534_, 6, v_initHeartbeats_546_);
lean_ctor_set(v___x_534_, 5, v_openDecls_545_);
lean_ctor_set(v___x_534_, 4, v_currNamespace_544_);
lean_ctor_set(v___x_534_, 3, v___x_557_);
lean_ctor_set(v___x_534_, 2, v___y_541_);
lean_ctor_set(v___x_534_, 1, v_fileMap_543_);
lean_ctor_set(v___x_534_, 0, v_fileName_542_);
v___x_559_ = v___x_534_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_fileName_542_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_fileMap_543_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v___y_541_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_currNamespace_544_);
lean_ctor_set(v_reuseFailAlloc_565_, 5, v_openDecls_545_);
lean_ctor_set(v_reuseFailAlloc_565_, 6, v_initHeartbeats_546_);
lean_ctor_set(v_reuseFailAlloc_565_, 7, v_maxHeartbeats_547_);
lean_ctor_set(v_reuseFailAlloc_565_, 8, v_quotContext_548_);
lean_ctor_set(v_reuseFailAlloc_565_, 9, v_currMacroScope_549_);
lean_ctor_set(v_reuseFailAlloc_565_, 10, v_cancelTk_x3f_550_);
lean_ctor_set(v_reuseFailAlloc_565_, 11, v_inheritedTraceOptions_551_);
v___x_559_ = v_reuseFailAlloc_565_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_currRecDepth_552_);
lean_ctor_set(v___x_560_, 2, v_ref_553_);
lean_ctor_set_uint16(v___x_560_, sizeof(void*)*3, v___y_539_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3 + 2, v_suppressElabErrors_554_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*3 + 3, v_isRecordingDeps_555_);
v___x_561_ = l_Lean_addAndCompile(v___x_486_, v___x_536_, v___x_537_, v___x_560_, v___y_556_);
lean_dec_ref_known(v___x_560_, 3);
if (lean_obj_tag(v___x_561_) == 0)
{
v___y_453_ = v___x_561_;
goto v___jp_452_;
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
v___y_468_ = v___x_561_;
v___y_469_ = v_a_562_;
v___y_470_ = v___x_564_;
goto v___jp_467_;
}
else
{
v___y_468_ = v___x_561_;
v___y_469_ = v_a_562_;
v___y_470_ = v___x_563_;
goto v___jp_467_;
}
}
}
}
v___jp_566_:
{
lean_object* v___x_573_; lean_object* v_env_574_; lean_object* v_nextMacroScope_575_; lean_object* v_ngen_576_; lean_object* v_auxDeclNGen_577_; lean_object* v_traceState_578_; lean_object* v_recordedDeps_579_; lean_object* v_messages_580_; lean_object* v_infoState_581_; lean_object* v_snapshotTasks_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_606_; 
v___x_573_ = lean_st_ref_take(v___y_572_);
v_env_574_ = lean_ctor_get(v___x_573_, 0);
v_nextMacroScope_575_ = lean_ctor_get(v___x_573_, 1);
v_ngen_576_ = lean_ctor_get(v___x_573_, 2);
v_auxDeclNGen_577_ = lean_ctor_get(v___x_573_, 3);
v_traceState_578_ = lean_ctor_get(v___x_573_, 4);
v_recordedDeps_579_ = lean_ctor_get(v___x_573_, 6);
v_messages_580_ = lean_ctor_get(v___x_573_, 7);
v_infoState_581_ = lean_ctor_get(v___x_573_, 8);
v_snapshotTasks_582_ = lean_ctor_get(v___x_573_, 9);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_573_, 5);
lean_dec(v_unused_607_);
v___x_584_ = v___x_573_;
v_isShared_585_ = v_isSharedCheck_606_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_snapshotTasks_582_);
lean_inc(v_infoState_581_);
lean_inc(v_messages_580_);
lean_inc(v_recordedDeps_579_);
lean_inc(v_traceState_578_);
lean_inc(v_auxDeclNGen_577_);
lean_inc(v_ngen_576_);
lean_inc(v_nextMacroScope_575_);
lean_inc(v_env_574_);
lean_dec(v___x_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_606_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = l_Lean_Kernel_enableDiag(v_env_574_, v___y_569_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 5, v___x_501_);
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_nextMacroScope_575_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_ngen_576_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_auxDeclNGen_577_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_traceState_578_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_recordedDeps_579_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_messages_580_);
lean_ctor_set(v_reuseFailAlloc_605_, 8, v_infoState_581_);
lean_ctor_set(v_reuseFailAlloc_605_, 9, v_snapshotTasks_582_);
v___x_588_ = v_reuseFailAlloc_605_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v_toCold_590_; lean_object* v_currRecDepth_591_; lean_object* v_ref_592_; uint8_t v_suppressElabErrors_593_; uint8_t v_isRecordingDeps_594_; lean_object* v_fileName_595_; lean_object* v_fileMap_596_; lean_object* v_currNamespace_597_; lean_object* v_openDecls_598_; lean_object* v_initHeartbeats_599_; lean_object* v_maxHeartbeats_600_; lean_object* v_quotContext_601_; lean_object* v_currMacroScope_602_; lean_object* v_cancelTk_x3f_603_; lean_object* v_inheritedTraceOptions_604_; 
v___x_589_ = lean_st_ref_put(v___y_572_, v___x_588_);
v_toCold_590_ = lean_ctor_get(v___y_570_, 0);
lean_inc_ref(v_toCold_590_);
v_currRecDepth_591_ = lean_ctor_get(v___y_570_, 1);
lean_inc(v_currRecDepth_591_);
v_ref_592_ = lean_ctor_get(v___y_570_, 2);
lean_inc(v_ref_592_);
v_suppressElabErrors_593_ = lean_ctor_get_uint8(v___y_570_, sizeof(void*)*3 + 2);
v_isRecordingDeps_594_ = lean_ctor_get_uint8(v___y_570_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_570_);
v_fileName_595_ = lean_ctor_get(v_toCold_590_, 0);
lean_inc_ref(v_fileName_595_);
v_fileMap_596_ = lean_ctor_get(v_toCold_590_, 1);
lean_inc_ref(v_fileMap_596_);
v_currNamespace_597_ = lean_ctor_get(v_toCold_590_, 4);
lean_inc(v_currNamespace_597_);
v_openDecls_598_ = lean_ctor_get(v_toCold_590_, 5);
lean_inc(v_openDecls_598_);
v_initHeartbeats_599_ = lean_ctor_get(v_toCold_590_, 6);
lean_inc(v_initHeartbeats_599_);
v_maxHeartbeats_600_ = lean_ctor_get(v_toCold_590_, 7);
lean_inc(v_maxHeartbeats_600_);
v_quotContext_601_ = lean_ctor_get(v_toCold_590_, 8);
lean_inc(v_quotContext_601_);
v_currMacroScope_602_ = lean_ctor_get(v_toCold_590_, 9);
lean_inc(v_currMacroScope_602_);
v_cancelTk_x3f_603_ = lean_ctor_get(v_toCold_590_, 10);
lean_inc(v_cancelTk_x3f_603_);
v_inheritedTraceOptions_604_ = lean_ctor_get(v_toCold_590_, 11);
lean_inc_ref(v_inheritedTraceOptions_604_);
lean_dec_ref(v_toCold_590_);
v___y_539_ = v___y_567_;
v___y_540_ = v___y_568_;
v___y_541_ = v___y_571_;
v_fileName_542_ = v_fileName_595_;
v_fileMap_543_ = v_fileMap_596_;
v_currNamespace_544_ = v_currNamespace_597_;
v_openDecls_545_ = v_openDecls_598_;
v_initHeartbeats_546_ = v_initHeartbeats_599_;
v_maxHeartbeats_547_ = v_maxHeartbeats_600_;
v_quotContext_548_ = v_quotContext_601_;
v_currMacroScope_549_ = v_currMacroScope_602_;
v_cancelTk_x3f_550_ = v_cancelTk_x3f_603_;
v_inheritedTraceOptions_551_ = v_inheritedTraceOptions_604_;
v_currRecDepth_552_ = v_currRecDepth_591_;
v_ref_553_ = v_ref_592_;
v_suppressElabErrors_554_ = v_suppressElabErrors_593_;
v_isRecordingDeps_555_ = v_isRecordingDeps_594_;
v___y_556_ = v___y_572_;
goto v___jp_538_;
}
}
}
v___jp_608_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint16_t v___x_632_; lean_object* v___x_633_; lean_object* v_env_634_; uint8_t v___x_635_; uint16_t v___x_636_; uint16_t v___x_637_; uint16_t v___x_638_; uint8_t v___x_639_; 
v___x_627_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_609_, v___y_610_);
lean_inc_ref(v_inheritedTraceOptions_621_);
lean_inc(v_cancelTk_x3f_620_);
lean_inc(v_currMacroScope_619_);
lean_inc(v_quotContext_618_);
lean_inc(v_maxHeartbeats_617_);
lean_inc(v_initHeartbeats_616_);
lean_inc(v_openDecls_615_);
lean_inc(v_currNamespace_614_);
lean_inc_ref(v___y_609_);
lean_inc_ref(v_fileMap_613_);
lean_inc_ref(v_fileName_612_);
v___x_628_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_628_, 0, v_fileName_612_);
lean_ctor_set(v___x_628_, 1, v_fileMap_613_);
lean_ctor_set(v___x_628_, 2, v___y_609_);
lean_ctor_set(v___x_628_, 3, v___x_627_);
lean_ctor_set(v___x_628_, 4, v_currNamespace_614_);
lean_ctor_set(v___x_628_, 5, v_openDecls_615_);
lean_ctor_set(v___x_628_, 6, v_initHeartbeats_616_);
lean_ctor_set(v___x_628_, 7, v_maxHeartbeats_617_);
lean_ctor_set(v___x_628_, 8, v_quotContext_618_);
lean_ctor_set(v___x_628_, 9, v_currMacroScope_619_);
lean_ctor_set(v___x_628_, 10, v_cancelTk_x3f_620_);
lean_ctor_set(v___x_628_, 11, v_inheritedTraceOptions_621_);
lean_inc(v_ref_623_);
lean_inc(v_currRecDepth_622_);
v___x_629_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_currRecDepth_622_);
lean_ctor_set(v___x_629_, 2, v_ref_623_);
lean_ctor_set_uint16(v___x_629_, sizeof(void*)*3, v___y_611_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*3 + 2, v_suppressElabErrors_624_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*3 + 3, v_isRecordingDeps_625_);
v___x_630_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_631_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_609_, v___x_630_, v___x_536_);
v___x_632_ = l_Lean_OptionFlags_ofOptions(v___x_631_);
v___x_633_ = lean_st_ref_get(v___y_626_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_633_);
v___x_635_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_634_);
lean_dec_ref(v_env_634_);
v___x_636_ = 512;
v___x_637_ = lean_uint16_land(v___x_632_, v___x_636_);
v___x_638_ = 0;
v___x_639_ = lean_uint16_dec_eq(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
if (v___x_635_ == 0)
{
lean_dec(v_ref_623_);
lean_dec(v_currRecDepth_622_);
lean_dec_ref(v_inheritedTraceOptions_621_);
lean_dec(v_cancelTk_x3f_620_);
lean_dec(v_currMacroScope_619_);
lean_dec(v_quotContext_618_);
lean_dec(v_maxHeartbeats_617_);
lean_dec(v_initHeartbeats_616_);
lean_dec(v_openDecls_615_);
lean_dec(v_currNamespace_614_);
lean_dec_ref(v_fileMap_613_);
lean_dec_ref(v_fileName_612_);
v___y_567_ = v___x_632_;
v___y_568_ = v___y_610_;
v___y_569_ = v___x_536_;
v___y_570_ = v___x_629_;
v___y_571_ = v___x_631_;
v___y_572_ = v___y_626_;
goto v___jp_566_;
}
else
{
lean_dec_ref_known(v___x_629_, 3);
v___y_539_ = v___x_632_;
v___y_540_ = v___y_610_;
v___y_541_ = v___x_631_;
v_fileName_542_ = v_fileName_612_;
v_fileMap_543_ = v_fileMap_613_;
v_currNamespace_544_ = v_currNamespace_614_;
v_openDecls_545_ = v_openDecls_615_;
v_initHeartbeats_546_ = v_initHeartbeats_616_;
v_maxHeartbeats_547_ = v_maxHeartbeats_617_;
v_quotContext_548_ = v_quotContext_618_;
v_currMacroScope_549_ = v_currMacroScope_619_;
v_cancelTk_x3f_550_ = v_cancelTk_x3f_620_;
v_inheritedTraceOptions_551_ = v_inheritedTraceOptions_621_;
v_currRecDepth_552_ = v_currRecDepth_622_;
v_ref_553_ = v_ref_623_;
v_suppressElabErrors_554_ = v_suppressElabErrors_624_;
v_isRecordingDeps_555_ = v_isRecordingDeps_625_;
v___y_556_ = v___y_626_;
goto v___jp_538_;
}
}
else
{
if (v___x_635_ == 0)
{
lean_dec_ref_known(v___x_629_, 3);
v___y_539_ = v___x_632_;
v___y_540_ = v___y_610_;
v___y_541_ = v___x_631_;
v_fileName_542_ = v_fileName_612_;
v_fileMap_543_ = v_fileMap_613_;
v_currNamespace_544_ = v_currNamespace_614_;
v_openDecls_545_ = v_openDecls_615_;
v_initHeartbeats_546_ = v_initHeartbeats_616_;
v_maxHeartbeats_547_ = v_maxHeartbeats_617_;
v_quotContext_548_ = v_quotContext_618_;
v_currMacroScope_549_ = v_currMacroScope_619_;
v_cancelTk_x3f_550_ = v_cancelTk_x3f_620_;
v_inheritedTraceOptions_551_ = v_inheritedTraceOptions_621_;
v_currRecDepth_552_ = v_currRecDepth_622_;
v_ref_553_ = v_ref_623_;
v_suppressElabErrors_554_ = v_suppressElabErrors_624_;
v_isRecordingDeps_555_ = v_isRecordingDeps_625_;
v___y_556_ = v___y_626_;
goto v___jp_538_;
}
else
{
lean_dec(v_ref_623_);
lean_dec(v_currRecDepth_622_);
lean_dec_ref(v_inheritedTraceOptions_621_);
lean_dec(v_cancelTk_x3f_620_);
lean_dec(v_currMacroScope_619_);
lean_dec(v_quotContext_618_);
lean_dec(v_maxHeartbeats_617_);
lean_dec(v_initHeartbeats_616_);
lean_dec(v_openDecls_615_);
lean_dec(v_currNamespace_614_);
lean_dec_ref(v_fileMap_613_);
lean_dec_ref(v_fileName_612_);
v___y_567_ = v___x_632_;
v___y_568_ = v___y_610_;
v___y_569_ = v___x_537_;
v___y_570_ = v___x_629_;
v___y_571_ = v___x_631_;
v___y_572_ = v___y_626_;
goto v___jp_566_;
}
}
}
v___jp_640_:
{
lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v_nextMacroScope_649_; lean_object* v_ngen_650_; lean_object* v_auxDeclNGen_651_; lean_object* v_traceState_652_; lean_object* v_recordedDeps_653_; lean_object* v_messages_654_; lean_object* v_infoState_655_; lean_object* v_snapshotTasks_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_680_; 
v___x_647_ = lean_st_ref_take(v___y_644_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
v_nextMacroScope_649_ = lean_ctor_get(v___x_647_, 1);
v_ngen_650_ = lean_ctor_get(v___x_647_, 2);
v_auxDeclNGen_651_ = lean_ctor_get(v___x_647_, 3);
v_traceState_652_ = lean_ctor_get(v___x_647_, 4);
v_recordedDeps_653_ = lean_ctor_get(v___x_647_, 6);
v_messages_654_ = lean_ctor_get(v___x_647_, 7);
v_infoState_655_ = lean_ctor_get(v___x_647_, 8);
v_snapshotTasks_656_ = lean_ctor_get(v___x_647_, 9);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v___x_647_, 5);
lean_dec(v_unused_681_);
v___x_658_ = v___x_647_;
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snapshotTasks_656_);
lean_inc(v_infoState_655_);
lean_inc(v_messages_654_);
lean_inc(v_recordedDeps_653_);
lean_inc(v_traceState_652_);
lean_inc(v_auxDeclNGen_651_);
lean_inc(v_ngen_650_);
lean_inc(v_nextMacroScope_649_);
lean_inc(v_env_648_);
lean_dec(v___x_647_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_Kernel_enableDiag(v_env_648_, v___y_641_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 5, v___x_501_);
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_nextMacroScope_649_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_ngen_650_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_auxDeclNGen_651_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_traceState_652_);
lean_ctor_set(v_reuseFailAlloc_679_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_679_, 6, v_recordedDeps_653_);
lean_ctor_set(v_reuseFailAlloc_679_, 7, v_messages_654_);
lean_ctor_set(v_reuseFailAlloc_679_, 8, v_infoState_655_);
lean_ctor_set(v_reuseFailAlloc_679_, 9, v_snapshotTasks_656_);
v___x_662_ = v_reuseFailAlloc_679_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v_toCold_664_; lean_object* v_currRecDepth_665_; lean_object* v_ref_666_; uint8_t v_suppressElabErrors_667_; uint8_t v_isRecordingDeps_668_; lean_object* v_fileName_669_; lean_object* v_fileMap_670_; lean_object* v_currNamespace_671_; lean_object* v_openDecls_672_; lean_object* v_initHeartbeats_673_; lean_object* v_maxHeartbeats_674_; lean_object* v_quotContext_675_; lean_object* v_currMacroScope_676_; lean_object* v_cancelTk_x3f_677_; lean_object* v_inheritedTraceOptions_678_; 
v___x_663_ = lean_st_ref_put(v___y_644_, v___x_662_);
v_toCold_664_ = lean_ctor_get(v___y_646_, 0);
lean_inc_ref(v_toCold_664_);
v_currRecDepth_665_ = lean_ctor_get(v___y_646_, 1);
lean_inc(v_currRecDepth_665_);
v_ref_666_ = lean_ctor_get(v___y_646_, 2);
lean_inc(v_ref_666_);
v_suppressElabErrors_667_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 2);
v_isRecordingDeps_668_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_646_);
v_fileName_669_ = lean_ctor_get(v_toCold_664_, 0);
lean_inc_ref(v_fileName_669_);
v_fileMap_670_ = lean_ctor_get(v_toCold_664_, 1);
lean_inc_ref(v_fileMap_670_);
v_currNamespace_671_ = lean_ctor_get(v_toCold_664_, 4);
lean_inc(v_currNamespace_671_);
v_openDecls_672_ = lean_ctor_get(v_toCold_664_, 5);
lean_inc(v_openDecls_672_);
v_initHeartbeats_673_ = lean_ctor_get(v_toCold_664_, 6);
lean_inc(v_initHeartbeats_673_);
v_maxHeartbeats_674_ = lean_ctor_get(v_toCold_664_, 7);
lean_inc(v_maxHeartbeats_674_);
v_quotContext_675_ = lean_ctor_get(v_toCold_664_, 8);
lean_inc(v_quotContext_675_);
v_currMacroScope_676_ = lean_ctor_get(v_toCold_664_, 9);
lean_inc(v_currMacroScope_676_);
v_cancelTk_x3f_677_ = lean_ctor_get(v_toCold_664_, 10);
lean_inc(v_cancelTk_x3f_677_);
v_inheritedTraceOptions_678_ = lean_ctor_get(v_toCold_664_, 11);
lean_inc_ref(v_inheritedTraceOptions_678_);
lean_dec_ref(v_toCold_664_);
v___y_609_ = v___y_642_;
v___y_610_ = v___y_643_;
v___y_611_ = v___y_645_;
v_fileName_612_ = v_fileName_669_;
v_fileMap_613_ = v_fileMap_670_;
v_currNamespace_614_ = v_currNamespace_671_;
v_openDecls_615_ = v_openDecls_672_;
v_initHeartbeats_616_ = v_initHeartbeats_673_;
v_maxHeartbeats_617_ = v_maxHeartbeats_674_;
v_quotContext_618_ = v_quotContext_675_;
v_currMacroScope_619_ = v_currMacroScope_676_;
v_cancelTk_x3f_620_ = v_cancelTk_x3f_677_;
v_inheritedTraceOptions_621_ = v_inheritedTraceOptions_678_;
v_currRecDepth_622_ = v_currRecDepth_665_;
v_ref_623_ = v_ref_666_;
v_suppressElabErrors_624_ = v_suppressElabErrors_667_;
v_isRecordingDeps_625_ = v_isRecordingDeps_668_;
v___y_626_ = v___y_644_;
goto v___jp_608_;
}
}
}
v___jp_685_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint16_t v___x_707_; lean_object* v___x_708_; lean_object* v_env_709_; uint8_t v___x_710_; uint16_t v___x_711_; uint16_t v___x_712_; uint16_t v___x_713_; uint8_t v___x_714_; 
v___x_701_ = l_Lean_maxRecDepth;
v___x_702_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___x_683_, v___x_701_);
lean_inc_ref(v_inheritedTraceOptions_695_);
lean_inc(v_cancelTk_x3f_694_);
lean_inc(v_currMacroScope_693_);
lean_inc(v_quotContext_692_);
lean_inc(v_maxHeartbeats_691_);
lean_inc(v_initHeartbeats_690_);
lean_inc(v_openDecls_689_);
lean_inc(v_currNamespace_688_);
lean_inc_ref(v___x_683_);
lean_inc_ref(v_fileMap_687_);
lean_inc_ref(v_fileName_686_);
v___x_703_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_703_, 0, v_fileName_686_);
lean_ctor_set(v___x_703_, 1, v_fileMap_687_);
lean_ctor_set(v___x_703_, 2, v___x_683_);
lean_ctor_set(v___x_703_, 3, v___x_702_);
lean_ctor_set(v___x_703_, 4, v_currNamespace_688_);
lean_ctor_set(v___x_703_, 5, v_openDecls_689_);
lean_ctor_set(v___x_703_, 6, v_initHeartbeats_690_);
lean_ctor_set(v___x_703_, 7, v_maxHeartbeats_691_);
lean_ctor_set(v___x_703_, 8, v_quotContext_692_);
lean_ctor_set(v___x_703_, 9, v_currMacroScope_693_);
lean_ctor_set(v___x_703_, 10, v_cancelTk_x3f_694_);
lean_ctor_set(v___x_703_, 11, v_inheritedTraceOptions_695_);
lean_inc(v_ref_697_);
lean_inc(v_currRecDepth_696_);
v___x_704_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_currRecDepth_696_);
lean_ctor_set(v___x_704_, 2, v_ref_697_);
lean_ctor_set_uint16(v___x_704_, sizeof(void*)*3, v___x_684_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*3 + 2, v_suppressElabErrors_698_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*3 + 3, v_isRecordingDeps_699_);
v___x_705_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_706_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__4(v___x_683_, v___x_705_, v___x_537_);
v___x_707_ = l_Lean_OptionFlags_ofOptions(v___x_706_);
v___x_708_ = lean_st_ref_get(v___y_700_);
v_env_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_env_709_);
lean_dec(v___x_708_);
v___x_710_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_709_);
lean_dec_ref(v_env_709_);
v___x_711_ = 512;
v___x_712_ = lean_uint16_land(v___x_707_, v___x_711_);
v___x_713_ = 0;
v___x_714_ = lean_uint16_dec_eq(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
if (v___x_710_ == 0)
{
lean_dec(v_ref_697_);
lean_dec(v_currRecDepth_696_);
lean_dec_ref(v_inheritedTraceOptions_695_);
lean_dec(v_cancelTk_x3f_694_);
lean_dec(v_currMacroScope_693_);
lean_dec(v_quotContext_692_);
lean_dec(v_maxHeartbeats_691_);
lean_dec(v_initHeartbeats_690_);
lean_dec(v_openDecls_689_);
lean_dec(v_currNamespace_688_);
lean_dec_ref(v_fileMap_687_);
lean_dec_ref(v_fileName_686_);
v___y_641_ = v___x_536_;
v___y_642_ = v___x_706_;
v___y_643_ = v___x_701_;
v___y_644_ = v___y_700_;
v___y_645_ = v___x_707_;
v___y_646_ = v___x_704_;
goto v___jp_640_;
}
else
{
lean_dec_ref_known(v___x_704_, 3);
v___y_609_ = v___x_706_;
v___y_610_ = v___x_701_;
v___y_611_ = v___x_707_;
v_fileName_612_ = v_fileName_686_;
v_fileMap_613_ = v_fileMap_687_;
v_currNamespace_614_ = v_currNamespace_688_;
v_openDecls_615_ = v_openDecls_689_;
v_initHeartbeats_616_ = v_initHeartbeats_690_;
v_maxHeartbeats_617_ = v_maxHeartbeats_691_;
v_quotContext_618_ = v_quotContext_692_;
v_currMacroScope_619_ = v_currMacroScope_693_;
v_cancelTk_x3f_620_ = v_cancelTk_x3f_694_;
v_inheritedTraceOptions_621_ = v_inheritedTraceOptions_695_;
v_currRecDepth_622_ = v_currRecDepth_696_;
v_ref_623_ = v_ref_697_;
v_suppressElabErrors_624_ = v_suppressElabErrors_698_;
v_isRecordingDeps_625_ = v_isRecordingDeps_699_;
v___y_626_ = v___y_700_;
goto v___jp_608_;
}
}
else
{
if (v___x_710_ == 0)
{
lean_dec_ref_known(v___x_704_, 3);
v___y_609_ = v___x_706_;
v___y_610_ = v___x_701_;
v___y_611_ = v___x_707_;
v_fileName_612_ = v_fileName_686_;
v_fileMap_613_ = v_fileMap_687_;
v_currNamespace_614_ = v_currNamespace_688_;
v_openDecls_615_ = v_openDecls_689_;
v_initHeartbeats_616_ = v_initHeartbeats_690_;
v_maxHeartbeats_617_ = v_maxHeartbeats_691_;
v_quotContext_618_ = v_quotContext_692_;
v_currMacroScope_619_ = v_currMacroScope_693_;
v_cancelTk_x3f_620_ = v_cancelTk_x3f_694_;
v_inheritedTraceOptions_621_ = v_inheritedTraceOptions_695_;
v_currRecDepth_622_ = v_currRecDepth_696_;
v_ref_623_ = v_ref_697_;
v_suppressElabErrors_624_ = v_suppressElabErrors_698_;
v_isRecordingDeps_625_ = v_isRecordingDeps_699_;
v___y_626_ = v___y_700_;
goto v___jp_608_;
}
else
{
lean_dec(v_ref_697_);
lean_dec(v_currRecDepth_696_);
lean_dec_ref(v_inheritedTraceOptions_695_);
lean_dec(v_cancelTk_x3f_694_);
lean_dec(v_currMacroScope_693_);
lean_dec(v_quotContext_692_);
lean_dec(v_maxHeartbeats_691_);
lean_dec(v_initHeartbeats_690_);
lean_dec(v_openDecls_689_);
lean_dec(v_currNamespace_688_);
lean_dec_ref(v_fileMap_687_);
lean_dec_ref(v_fileName_686_);
v___y_641_ = v___x_537_;
v___y_642_ = v___x_706_;
v___y_643_ = v___x_701_;
v___y_644_ = v___y_700_;
v___y_645_ = v___x_707_;
v___y_646_ = v___x_704_;
goto v___jp_640_;
}
}
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v_env_719_; lean_object* v_nextMacroScope_720_; lean_object* v_ngen_721_; lean_object* v_auxDeclNGen_722_; lean_object* v_traceState_723_; lean_object* v_recordedDeps_724_; lean_object* v_messages_725_; lean_object* v_infoState_726_; lean_object* v_snapshotTasks_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v___x_718_ = lean_st_ref_take(v___y_433_);
v_env_719_ = lean_ctor_get(v___x_718_, 0);
v_nextMacroScope_720_ = lean_ctor_get(v___x_718_, 1);
v_ngen_721_ = lean_ctor_get(v___x_718_, 2);
v_auxDeclNGen_722_ = lean_ctor_get(v___x_718_, 3);
v_traceState_723_ = lean_ctor_get(v___x_718_, 4);
v_recordedDeps_724_ = lean_ctor_get(v___x_718_, 6);
v_messages_725_ = lean_ctor_get(v___x_718_, 7);
v_infoState_726_ = lean_ctor_get(v___x_718_, 8);
v_snapshotTasks_727_ = lean_ctor_get(v___x_718_, 9);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_718_, 5);
lean_dec(v_unused_737_);
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snapshotTasks_727_);
lean_inc(v_infoState_726_);
lean_inc(v_messages_725_);
lean_inc(v_recordedDeps_724_);
lean_inc(v_traceState_723_);
lean_inc(v_auxDeclNGen_722_);
lean_inc(v_ngen_721_);
lean_inc(v_nextMacroScope_720_);
lean_inc(v_env_719_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = l_Lean_Kernel_enableDiag(v_env_719_, v___y_717_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 5, v___x_501_);
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_nextMacroScope_720_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_ngen_721_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_auxDeclNGen_722_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_traceState_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_735_, 6, v_recordedDeps_724_);
lean_ctor_set(v_reuseFailAlloc_735_, 7, v_messages_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 8, v_infoState_726_);
lean_ctor_set(v_reuseFailAlloc_735_, 9, v_snapshotTasks_727_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_st_ref_put(v___y_433_, v___x_733_);
lean_inc(v_ref_519_);
lean_inc(v_currRecDepth_518_);
v_fileName_686_ = v_fileName_522_;
v_fileMap_687_ = v_fileMap_523_;
v_currNamespace_688_ = v_currNamespace_525_;
v_openDecls_689_ = v_openDecls_526_;
v_initHeartbeats_690_ = v_initHeartbeats_527_;
v_maxHeartbeats_691_ = v_maxHeartbeats_528_;
v_quotContext_692_ = v_quotContext_529_;
v_currMacroScope_693_ = v_currMacroScope_530_;
v_cancelTk_x3f_694_ = v_cancelTk_x3f_531_;
v_inheritedTraceOptions_695_ = v_inheritedTraceOptions_532_;
v_currRecDepth_696_ = v_currRecDepth_518_;
v_ref_697_ = v_ref_519_;
v_suppressElabErrors_698_ = v_suppressElabErrors_520_;
v_isRecordingDeps_699_ = v_isRecordingDeps_521_;
v___y_700_ = v___y_433_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v_tacticName_754_, lean_object* v___x_755_, lean_object* v___x_756_, lean_object* v___x_757_, lean_object* v_a_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Meta_nativeEqTrue___lam__0(v_tacticName_754_, v___x_755_, v___x_756_, v___x_757_, v_a_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(lean_object* v_env_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_nextMacroScope_770_; lean_object* v_ngen_771_; lean_object* v_auxDeclNGen_772_; lean_object* v_traceState_773_; lean_object* v_recordedDeps_774_; lean_object* v_messages_775_; lean_object* v_infoState_776_; lean_object* v_snapshotTasks_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_803_; 
v___x_769_ = lean_st_ref_take(v___y_767_);
v_nextMacroScope_770_ = lean_ctor_get(v___x_769_, 1);
v_ngen_771_ = lean_ctor_get(v___x_769_, 2);
v_auxDeclNGen_772_ = lean_ctor_get(v___x_769_, 3);
v_traceState_773_ = lean_ctor_get(v___x_769_, 4);
v_recordedDeps_774_ = lean_ctor_get(v___x_769_, 6);
v_messages_775_ = lean_ctor_get(v___x_769_, 7);
v_infoState_776_ = lean_ctor_get(v___x_769_, 8);
v_snapshotTasks_777_ = lean_ctor_get(v___x_769_, 9);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; lean_object* v_unused_805_; 
v_unused_804_ = lean_ctor_get(v___x_769_, 5);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v___x_769_, 0);
lean_dec(v_unused_805_);
v___x_779_ = v___x_769_;
v_isShared_780_ = v_isSharedCheck_803_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snapshotTasks_777_);
lean_inc(v_infoState_776_);
lean_inc(v_messages_775_);
lean_inc(v_recordedDeps_774_);
lean_inc(v_traceState_773_);
lean_inc(v_auxDeclNGen_772_);
lean_inc(v_ngen_771_);
lean_inc(v_nextMacroScope_770_);
lean_dec(v___x_769_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_803_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 5, v___x_781_);
lean_ctor_set(v___x_779_, 0, v_env_765_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_env_765_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_nextMacroScope_770_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_ngen_771_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_auxDeclNGen_772_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_traceState_773_);
lean_ctor_set(v_reuseFailAlloc_802_, 5, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_802_, 6, v_recordedDeps_774_);
lean_ctor_set(v_reuseFailAlloc_802_, 7, v_messages_775_);
lean_ctor_set(v_reuseFailAlloc_802_, 8, v_infoState_776_);
lean_ctor_set(v_reuseFailAlloc_802_, 9, v_snapshotTasks_777_);
v___x_783_ = v_reuseFailAlloc_802_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_mctx_786_; lean_object* v_zetaDeltaFVarIds_787_; lean_object* v_postponed_788_; lean_object* v_diag_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_800_; 
v___x_784_ = lean_st_ref_put(v___y_767_, v___x_783_);
v___x_785_ = lean_st_ref_take(v___y_766_);
v_mctx_786_ = lean_ctor_get(v___x_785_, 0);
v_zetaDeltaFVarIds_787_ = lean_ctor_get(v___x_785_, 2);
v_postponed_788_ = lean_ctor_get(v___x_785_, 3);
v_diag_789_ = lean_ctor_get(v___x_785_, 4);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_785_, 1);
lean_dec(v_unused_801_);
v___x_791_ = v___x_785_;
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_diag_789_);
lean_inc(v_postponed_788_);
lean_inc(v_zetaDeltaFVarIds_787_);
lean_inc(v_mctx_786_);
lean_dec(v___x_785_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_800_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = lean_box(0);
v___x_794_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_794_);
v___x_796_ = v___x_791_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_mctx_786_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_zetaDeltaFVarIds_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_postponed_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_diag_789_);
v___x_796_ = v_reuseFailAlloc_799_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_st_ref_put(v___y_766_, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_793_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg___boxed(lean_object* v_env_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec(v___y_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(lean_object* v_env_811_, lean_object* v_x_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_env_819_; lean_object* v_a_821_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_818_ = lean_st_ref_get(v___y_816_);
v_env_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_env_819_);
lean_dec(v___x_818_);
v___x_831_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_811_, v___y_814_, v___y_816_);
lean_dec_ref(v___x_831_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
v___x_832_ = lean_apply_5(v_x_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, lean_box(0));
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_819_, v___y_814_, v___y_816_);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_834_, 0);
lean_dec(v_unused_842_);
v___x_836_ = v___x_834_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_dec(v___x_834_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_a_833_);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_833_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_832_, 1);
v_a_821_ = v_a_843_;
goto v___jp_820_;
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v___x_822_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_819_, v___y_814_, v___y_816_);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_830_);
v___x_824_ = v___x_822_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_dec(v___x_822_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 1);
lean_ctor_set(v___x_824_, 0, v_a_821_);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_821_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg___boxed(lean_object* v_env_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(lean_object* v_stx_852_, lean_object* v___y_853_){
_start:
{
uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = 0;
v___x_856_ = l_Lean_Syntax_getRange_x3f(v_stx_852_, v___x_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v_toCold_857_; lean_object* v_val_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_870_; 
v_toCold_857_ = lean_ctor_get(v___y_853_, 0);
v_val_858_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_870_ == 0)
{
v___x_860_ = v___x_856_;
v_isShared_861_ = v_isSharedCheck_870_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_val_858_);
lean_dec(v___x_856_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_870_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_fileMap_862_; lean_object* v_start_863_; lean_object* v_stop_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v_fileMap_862_ = lean_ctor_get(v_toCold_857_, 1);
v_start_863_ = lean_ctor_get(v_val_858_, 0);
lean_inc(v_start_863_);
v_stop_864_ = lean_ctor_get(v_val_858_, 1);
lean_inc(v_stop_864_);
lean_dec(v_val_858_);
lean_inc_ref(v_fileMap_862_);
v___x_865_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_862_, v_start_863_, v_stop_864_);
lean_dec(v_stop_864_);
lean_dec(v_start_863_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_865_);
v___x_867_ = v___x_860_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_869_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v___x_856_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg___boxed(lean_object* v_stx_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_873_, v___y_874_);
lean_dec_ref(v___y_874_);
lean_dec(v_stx_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(lean_object* v_declName_877_, lean_object* v_declRanges_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = l_Lean_Name_isAnonymous(v_declName_877_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v_env_884_; lean_object* v_nextMacroScope_885_; lean_object* v_ngen_886_; lean_object* v_auxDeclNGen_887_; lean_object* v_traceState_888_; lean_object* v_recordedDeps_889_; lean_object* v_messages_890_; lean_object* v_infoState_891_; lean_object* v_snapshotTasks_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_920_; 
v___x_883_ = lean_st_ref_take(v___y_880_);
v_env_884_ = lean_ctor_get(v___x_883_, 0);
v_nextMacroScope_885_ = lean_ctor_get(v___x_883_, 1);
v_ngen_886_ = lean_ctor_get(v___x_883_, 2);
v_auxDeclNGen_887_ = lean_ctor_get(v___x_883_, 3);
v_traceState_888_ = lean_ctor_get(v___x_883_, 4);
v_recordedDeps_889_ = lean_ctor_get(v___x_883_, 6);
v_messages_890_ = lean_ctor_get(v___x_883_, 7);
v_infoState_891_ = lean_ctor_get(v___x_883_, 8);
v_snapshotTasks_892_ = lean_ctor_get(v___x_883_, 9);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_883_, 5);
lean_dec(v_unused_921_);
v___x_894_ = v___x_883_;
v_isShared_895_ = v_isSharedCheck_920_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snapshotTasks_892_);
lean_inc(v_infoState_891_);
lean_inc(v_messages_890_);
lean_inc(v_recordedDeps_889_);
lean_inc(v_traceState_888_);
lean_inc(v_auxDeclNGen_887_);
lean_inc(v_ngen_886_);
lean_inc(v_nextMacroScope_885_);
lean_inc(v_env_884_);
lean_dec(v___x_883_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_920_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_896_ = l_Lean_declRangeExt;
v___x_897_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_896_, v_env_884_, v_declName_877_, v_declRanges_878_);
v___x_898_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 5, v___x_898_);
lean_ctor_set(v___x_894_, 0, v___x_897_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_nextMacroScope_885_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_ngen_886_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_auxDeclNGen_887_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_traceState_888_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v_recordedDeps_889_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_messages_890_);
lean_ctor_set(v_reuseFailAlloc_919_, 8, v_infoState_891_);
lean_ctor_set(v_reuseFailAlloc_919_, 9, v_snapshotTasks_892_);
v___x_900_ = v_reuseFailAlloc_919_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_mctx_903_; lean_object* v_zetaDeltaFVarIds_904_; lean_object* v_postponed_905_; lean_object* v_diag_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_917_; 
v___x_901_ = lean_st_ref_put(v___y_880_, v___x_900_);
v___x_902_ = lean_st_ref_take(v___y_879_);
v_mctx_903_ = lean_ctor_get(v___x_902_, 0);
v_zetaDeltaFVarIds_904_ = lean_ctor_get(v___x_902_, 2);
v_postponed_905_ = lean_ctor_get(v___x_902_, 3);
v_diag_906_ = lean_ctor_get(v___x_902_, 4);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v___x_902_, 1);
lean_dec(v_unused_918_);
v___x_908_ = v___x_902_;
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_diag_906_);
lean_inc(v_postponed_905_);
lean_inc(v_zetaDeltaFVarIds_904_);
lean_inc(v_mctx_903_);
lean_dec(v___x_902_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_mctx_903_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_zetaDeltaFVarIds_904_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_postponed_905_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_diag_906_);
v___x_913_ = v_reuseFailAlloc_916_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_st_ref_put(v___y_879_, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_910_);
return v___x_915_;
}
}
}
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec_ref(v_declRanges_878_);
lean_dec(v_declName_877_);
v___x_922_ = lean_box(0);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg___boxed(lean_object* v_declName_924_, lean_object* v_declRanges_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_924_, v_declRanges_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec(v___y_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_declName_930_, lean_object* v_rangeStx_931_, lean_object* v_selectionRangeStx_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_955_; 
v___x_938_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_rangeStx_931_, v___y_935_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_955_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_955_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_955_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
if (lean_obj_tag(v_a_939_) == 1)
{
lean_object* v_val_943_; lean_object* v_a_945_; lean_object* v___x_948_; lean_object* v_a_949_; 
lean_del_object(v___x_941_);
v_val_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v_a_939_, 1);
v___x_948_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_selectionRangeStx_932_, v___y_935_);
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref(v___x_948_);
if (lean_obj_tag(v_a_949_) == 0)
{
lean_inc(v_val_943_);
v_a_945_ = v_val_943_;
goto v___jp_944_;
}
else
{
lean_object* v_val_950_; 
v_val_950_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_val_950_);
lean_dec_ref_known(v_a_949_, 1);
v_a_945_ = v_val_950_;
goto v___jp_944_;
}
v___jp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_val_943_);
lean_ctor_set(v___x_946_, 1, v_a_945_);
v___x_947_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_930_, v___x_946_, v___y_934_, v___y_936_);
return v___x_947_;
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_a_939_);
lean_dec(v_declName_930_);
v___x_951_ = lean_box(0);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_951_);
v___x_953_ = v___x_941_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8___boxed(lean_object* v_declName_956_, lean_object* v_rangeStx_957_, lean_object* v_selectionRangeStx_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_declName_956_, v_rangeStx_957_, v_selectionRangeStx_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v_selectionRangeStx_958_);
lean_dec(v_rangeStx_957_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
if (lean_obj_tag(v_a_965_) == 0)
{
lean_object* v___x_967_; 
v___x_967_ = l_List_reverse___redArg(v_a_966_);
return v___x_967_;
}
else
{
lean_object* v_head_968_; lean_object* v_tail_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v_head_968_ = lean_ctor_get(v_a_965_, 0);
v_tail_969_ = lean_ctor_get(v_a_965_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v_a_965_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_tail_969_);
lean_inc(v_head_968_);
lean_dec(v_a_965_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = l_Lean_mkLevelParam(v_head_968_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v_a_966_);
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_a_966_);
v___x_975_ = v_reuseFailAlloc_977_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
v_a_965_ = v_tail_969_;
v_a_966_ = v___x_975_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_box(0);
v___x_980_ = lean_unsigned_to_nat(16u);
v___x_981_ = lean_mk_array(v___x_980_, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_988_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_ctor_set(v___x_989_, 2, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = l_Lean_Level_ofNat(v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_1008_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_1009_ = l_Lean_mkConst(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_1012_ = l_Lean_mkConst(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_1019_ = l_Lean_mkConst(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_1026_, lean_object* v_e_1027_, lean_object* v_axiomDeclRange_x3f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; uint8_t v___x_1149_; 
v___x_1042_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_1027_, v_a_1030_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v___x_1042_);
v___x_1149_ = l_Lean_Expr_hasFVar(v_a_1043_);
if (v___x_1149_ == 0)
{
v___y_1128_ = v_a_1029_;
v___y_1129_ = v_a_1030_;
v___y_1130_ = v_a_1031_;
v___y_1131_ = v_a_1032_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v___x_1150_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1151_ = l_Lean_MessageData_ofName(v_tacticName_1026_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_indentExpr(v_a_1043_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1156_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
v___jp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(v___y_1036_, v___x_1037_);
v___x_1039_ = l_Lean_mkConst(v___y_1035_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
v___jp_1044_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_params_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1124_; 
v___x_1049_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1043_);
v___x_1050_ = l_Lean_collectLevelParams(v___x_1049_, v_a_1043_);
v_params_1051_ = lean_ctor_get(v___x_1050_, 2);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; lean_object* v_unused_1126_; 
v_unused_1125_ = lean_ctor_get(v___x_1050_, 1);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1126_);
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1124_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_params_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1124_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v_env_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_array_to_list(v_params_1051_);
v___x_1057_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_1026_);
v___x_1058_ = l_Lean_Name_append(v___x_1057_, v_tacticName_1026_);
v___x_1059_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1058_);
v___x_1060_ = l_Lean_Name_append(v___x_1058_, v___x_1059_);
lean_inc(v_a_1043_);
lean_inc(v___x_1056_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1061_, 0, v_tacticName_1026_);
lean_closure_set(v___f_1061_, 1, v___x_1060_);
lean_closure_set(v___f_1061_, 2, v___x_1056_);
lean_closure_set(v___f_1061_, 3, v___x_1055_);
lean_closure_set(v___f_1061_, 4, v_a_1043_);
v___x_1062_ = lean_st_ref_get(v___y_1048_);
v_env_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_ref(v_env_1063_);
lean_dec(v___x_1062_);
v___x_1064_ = l_Lean_Environment_unlockAsync(v_env_1063_);
v___x_1065_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v___x_1064_, v___f_1061_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1115_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1115_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1115_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_unbox(v_a_1066_);
lean_dec(v_a_1066_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_dec(v___x_1058_);
lean_dec(v___x_1056_);
lean_del_object(v___x_1053_);
lean_dec(v_a_1043_);
v___x_1071_ = lean_box(1);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1071_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1068_);
v___x_1075_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1076_ = l_Lean_Name_append(v___x_1058_, v___x_1075_);
v___x_1077_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1076_, v___y_1048_);
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1114_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1114_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1082_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1083_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1084_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1085_ = l_Lean_mkApp3(v___x_1082_, v___x_1083_, v_a_1043_, v___x_1084_);
lean_inc(v___x_1056_);
lean_inc(v_a_1078_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 2, v___x_1085_);
lean_ctor_set(v___x_1053_, 1, v___x_1056_);
lean_ctor_set(v___x_1053_, 0, v_a_1078_);
v___x_1087_ = v___x_1053_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1078_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = 0;
v___x_1089_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*1, v___x_1088_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1089_);
v___x_1091_ = v___x_1080_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_addDecl(v___x_1091_, v___x_1088_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_dec_ref_known(v___x_1092_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1028_) == 1)
{
lean_object* v_val_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_val_1093_ = lean_ctor_get(v_axiomDeclRange_x3f_1028_, 0);
v___x_1094_ = lean_box(0);
lean_inc(v_a_1078_);
v___x_1095_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_a_1078_, v_val_1093_, v___x_1094_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref_known(v___x_1095_, 1);
v___y_1035_ = v_a_1078_;
v___y_1036_ = v___x_1056_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_a_1078_);
lean_dec(v___x_1056_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
v___y_1035_ = v_a_1078_;
v___y_1036_ = v___x_1056_;
goto v___jp_1034_;
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_a_1078_);
lean_dec(v___x_1056_);
v_a_1104_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1092_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1092_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
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
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v___x_1058_);
lean_dec(v___x_1056_);
lean_del_object(v___x_1053_);
lean_dec(v_a_1043_);
v_a_1116_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1065_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1065_);
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
v___jp_1127_:
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Lean_Expr_hasMVar(v_a_1043_);
if (v___x_1132_ == 0)
{
v___y_1045_ = v___y_1128_;
v___y_1046_ = v___y_1129_;
v___y_1047_ = v___y_1130_;
v___y_1048_ = v___y_1131_;
goto v___jp_1044_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v___x_1133_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1134_ = l_Lean_MessageData_ofName(v_tacticName_1026_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_indentExpr(v_a_1043_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1139_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1166_, lean_object* v_e_1167_, lean_object* v_axiomDeclRange_x3f_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1166_, v_e_1167_, v_axiomDeclRange_x3f_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_axiomDeclRange_x3f_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1189_, lean_object* v_constName_1190_, uint8_t v_checkMeta_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1190_, v_checkMeta_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_constName_1199_, lean_object* v_checkMeta_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_checkMeta_boxed_1206_; lean_object* v_res_1207_; 
v_checkMeta_boxed_1206_ = lean_unbox(v_checkMeta_1200_);
v_res_1207_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1198_, v_constName_1199_, v_checkMeta_boxed_1206_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1216_, v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(lean_object* v_env_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_1224_, v___y_1226_, v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___boxed(lean_object* v_env_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(v_env_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_00_u03b1_1238_, lean_object* v_env_1239_, lean_object* v_x_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_1239_, v_x_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_env_1248_, lean_object* v_x_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(v_00_u03b1_1247_, v_env_1248_, v_x_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(lean_object* v_stx_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_1256_, v___y_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___boxed(lean_object* v_stx_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(v_stx_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v_stx_1263_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(lean_object* v_declName_1270_, lean_object* v_declRanges_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_1270_, v_declRanges_1271_, v___y_1273_, v___y_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___boxed(lean_object* v_declName_1278_, lean_object* v_declRanges_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(v_declName_1278_, v_declRanges_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1286_, lean_object* v_x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_x_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1294_, v_x_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1301_;
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

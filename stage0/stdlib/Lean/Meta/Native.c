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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_opts_238_, lean_object* v_opt_239_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4___boxed(lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v_opts_246_, v_opt_247_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(lean_object* v_o_299_, lean_object* v_k_300_, uint8_t v_v_301_){
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
v___x_309_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8___boxed(lean_object* v_o_318_, lean_object* v_k_319_, lean_object* v_v_320_){
_start:
{
uint8_t v_v_boxed_321_; lean_object* v_res_322_; 
v_v_boxed_321_ = lean_unbox(v_v_320_);
v_res_322_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(v_o_318_, v_k_319_, v_v_boxed_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_opts_323_, lean_object* v_opt_324_, uint8_t v_val_325_){
_start:
{
lean_object* v_name_326_; lean_object* v___x_327_; 
v_name_326_ = lean_ctor_get(v_opt_324_, 0);
lean_inc(v_name_326_);
lean_dec_ref(v_opt_324_);
v___x_327_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5_spec__8(v_opts_323_, v_name_326_, v_val_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_opts_328_, lean_object* v_opt_329_, lean_object* v_val_330_){
_start:
{
uint8_t v_val_boxed_331_; lean_object* v_res_332_; 
v_val_boxed_331_ = lean_unbox(v_val_330_);
v_res_332_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v_opts_328_, v_opt_329_, v_val_boxed_331_);
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
lean_object* v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___x_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_774_; 
v___x_447_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_426_, v___y_433_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_774_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_774_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_774_;
goto v_resetjp_449_;
}
v___jp_435_:
{
if (v___y_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v___y_436_);
v___x_439_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_440_ = l_Lean_MessageData_ofName(v_tacticName_425_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_Exception_toMessageData(v___y_437_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_445_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec_ref(v___y_432_);
return v___x_446_;
}
else
{
lean_dec_ref(v___y_437_);
lean_dec_ref(v___y_432_);
lean_dec(v_tacticName_425_);
return v___y_436_;
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
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_773_;
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
v___y_436_ = v___x_455_;
v___y_437_ = v_a_456_;
v___y_438_ = v___x_458_;
goto v___jp_435_;
}
else
{
v___y_436_ = v___x_455_;
v___y_437_ = v_a_456_;
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
lean_dec_ref(v___y_469_);
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
v___x_476_ = l_Lean_Exception_toMessageData(v___y_468_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_477_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
v___y_453_ = v___x_478_;
goto v___jp_452_;
}
else
{
lean_dec_ref(v___y_468_);
v___y_453_ = v___y_469_;
goto v___jp_452_;
}
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v_env_488_; lean_object* v_nextMacroScope_489_; lean_object* v_ngen_490_; lean_object* v_auxDeclNGen_491_; lean_object* v_traceState_492_; lean_object* v_recordedDeps_493_; lean_object* v_messages_494_; lean_object* v_infoState_495_; lean_object* v_snapshotTasks_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_771_; 
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
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_487_, 5);
lean_dec(v_unused_772_);
v___x_498_ = v___x_487_;
v_isShared_499_ = v_isSharedCheck_771_;
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
v_isShared_499_ = v_isSharedCheck_771_;
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
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_nextMacroScope_489_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_ngen_490_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_auxDeclNGen_491_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_traceState_492_);
lean_ctor_set(v_reuseFailAlloc_770_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_770_, 6, v_recordedDeps_493_);
lean_ctor_set(v_reuseFailAlloc_770_, 7, v_messages_494_);
lean_ctor_set(v_reuseFailAlloc_770_, 8, v_infoState_495_);
lean_ctor_set(v_reuseFailAlloc_770_, 9, v_snapshotTasks_496_);
v___x_503_ = v_reuseFailAlloc_770_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_mctx_506_; lean_object* v_zetaDeltaFVarIds_507_; lean_object* v_postponed_508_; lean_object* v_diag_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_768_; 
v___x_504_ = lean_st_ref_put(v___y_433_, v___x_503_);
v___x_505_ = lean_st_ref_take(v___y_431_);
v_mctx_506_ = lean_ctor_get(v___x_505_, 0);
v_zetaDeltaFVarIds_507_ = lean_ctor_get(v___x_505_, 2);
v_postponed_508_ = lean_ctor_get(v___x_505_, 3);
v_diag_509_ = lean_ctor_get(v___x_505_, 4);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v___x_505_, 1);
lean_dec(v_unused_769_);
v___x_511_ = v___x_505_;
v_isShared_512_ = v_isSharedCheck_768_;
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
v_isShared_512_ = v_isSharedCheck_768_;
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
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_mctx_506_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_zetaDeltaFVarIds_507_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_postponed_508_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_diag_509_);
v___x_515_ = v_reuseFailAlloc_767_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v_toCold_517_; lean_object* v_currRecDepth_518_; lean_object* v_ref_519_; uint8_t v_suppressElabErrors_520_; uint8_t v_isRecordingDeps_521_; lean_object* v_fileName_522_; lean_object* v_fileMap_523_; lean_object* v_options_524_; lean_object* v_currNamespace_525_; lean_object* v_openDecls_526_; lean_object* v_initHeartbeats_527_; lean_object* v_maxHeartbeats_528_; lean_object* v_quotContext_529_; lean_object* v_currMacroScope_530_; lean_object* v_cancelTk_x3f_531_; lean_object* v_inheritedTraceOptions_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_765_; 
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
v_isSharedCheck_765_ = !lean_is_exclusive(v_toCold_517_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_toCold_517_, 3);
lean_dec(v_unused_766_);
v___x_534_ = v_toCold_517_;
v_isShared_535_ = v_isSharedCheck_765_;
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
v_isShared_535_ = v_isSharedCheck_765_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v___x_536_; uint8_t v___x_537_; uint16_t v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_581_; lean_object* v___y_582_; uint16_t v___y_583_; uint8_t v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_621_; lean_object* v___y_622_; uint16_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v___y_666_; uint16_t v___y_667_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; uint16_t v___y_702_; lean_object* v___y_703_; lean_object* v_fileName_704_; lean_object* v_fileMap_705_; lean_object* v_currNamespace_706_; lean_object* v_openDecls_707_; lean_object* v_initHeartbeats_708_; lean_object* v_maxHeartbeats_709_; lean_object* v_quotContext_710_; lean_object* v_currMacroScope_711_; lean_object* v_cancelTk_x3f_712_; lean_object* v_inheritedTraceOptions_713_; lean_object* v_currRecDepth_714_; lean_object* v_ref_715_; uint8_t v_suppressElabErrors_716_; uint8_t v_isRecordingDeps_717_; lean_object* v___y_718_; lean_object* v___y_729_; uint16_t v___y_730_; uint8_t v___y_731_; lean_object* v___y_753_; 
v___x_536_ = 1;
v___x_537_ = 0;
if (v_isRecordingDeps_521_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = l_Lean_Elab_async;
v___x_763_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v_options_524_, v___x_762_, v_isRecordingDeps_521_);
v___y_753_ = v___x_763_;
goto v___jp_752_;
}
else
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_524_);
v___y_753_ = v___x_764_;
goto v___jp_752_;
}
v___jp_538_:
{
lean_object* v_toCold_544_; lean_object* v_currRecDepth_545_; lean_object* v_ref_546_; uint8_t v_suppressElabErrors_547_; uint8_t v_isRecordingDeps_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_579_; 
v_toCold_544_ = lean_ctor_get(v___y_542_, 0);
v_currRecDepth_545_ = lean_ctor_get(v___y_542_, 1);
v_ref_546_ = lean_ctor_get(v___y_542_, 2);
v_suppressElabErrors_547_ = lean_ctor_get_uint8(v___y_542_, sizeof(void*)*3 + 2);
v_isRecordingDeps_548_ = lean_ctor_get_uint8(v___y_542_, sizeof(void*)*3 + 3);
v_isSharedCheck_579_ = !lean_is_exclusive(v___y_542_);
if (v_isSharedCheck_579_ == 0)
{
v___x_550_ = v___y_542_;
v_isShared_551_ = v_isSharedCheck_579_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_ref_546_);
lean_inc(v_currRecDepth_545_);
lean_inc(v_toCold_544_);
lean_dec(v___y_542_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_579_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_fileName_552_; lean_object* v_fileMap_553_; lean_object* v_currNamespace_554_; lean_object* v_openDecls_555_; lean_object* v_initHeartbeats_556_; lean_object* v_maxHeartbeats_557_; lean_object* v_quotContext_558_; lean_object* v_currMacroScope_559_; lean_object* v_cancelTk_x3f_560_; lean_object* v_inheritedTraceOptions_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_576_; 
v_fileName_552_ = lean_ctor_get(v_toCold_544_, 0);
v_fileMap_553_ = lean_ctor_get(v_toCold_544_, 1);
v_currNamespace_554_ = lean_ctor_get(v_toCold_544_, 4);
v_openDecls_555_ = lean_ctor_get(v_toCold_544_, 5);
v_initHeartbeats_556_ = lean_ctor_get(v_toCold_544_, 6);
v_maxHeartbeats_557_ = lean_ctor_get(v_toCold_544_, 7);
v_quotContext_558_ = lean_ctor_get(v_toCold_544_, 8);
v_currMacroScope_559_ = lean_ctor_get(v_toCold_544_, 9);
v_cancelTk_x3f_560_ = lean_ctor_get(v_toCold_544_, 10);
v_inheritedTraceOptions_561_ = lean_ctor_get(v_toCold_544_, 11);
v_isSharedCheck_576_ = !lean_is_exclusive(v_toCold_544_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; 
v_unused_577_ = lean_ctor_get(v_toCold_544_, 3);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_toCold_544_, 2);
lean_dec(v_unused_578_);
v___x_563_ = v_toCold_544_;
v_isShared_564_ = v_isSharedCheck_576_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_inheritedTraceOptions_561_);
lean_inc(v_cancelTk_x3f_560_);
lean_inc(v_currMacroScope_559_);
lean_inc(v_quotContext_558_);
lean_inc(v_maxHeartbeats_557_);
lean_inc(v_initHeartbeats_556_);
lean_inc(v_openDecls_555_);
lean_inc(v_currNamespace_554_);
lean_inc(v_fileMap_553_);
lean_inc(v_fileName_552_);
lean_dec(v_toCold_544_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_576_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_541_, v___y_540_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 3, v___x_565_);
lean_ctor_set(v___x_563_, 2, v___y_541_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_fileName_552_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_fileMap_553_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___y_541_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v_currNamespace_554_);
lean_ctor_set(v_reuseFailAlloc_575_, 5, v_openDecls_555_);
lean_ctor_set(v_reuseFailAlloc_575_, 6, v_initHeartbeats_556_);
lean_ctor_set(v_reuseFailAlloc_575_, 7, v_maxHeartbeats_557_);
lean_ctor_set(v_reuseFailAlloc_575_, 8, v_quotContext_558_);
lean_ctor_set(v_reuseFailAlloc_575_, 9, v_currMacroScope_559_);
lean_ctor_set(v_reuseFailAlloc_575_, 10, v_cancelTk_x3f_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 11, v_inheritedTraceOptions_561_);
v___x_567_ = v_reuseFailAlloc_575_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_567_);
v___x_569_ = v___x_550_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_currRecDepth_545_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_ref_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_574_, sizeof(void*)*3 + 2, v_suppressElabErrors_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_574_, sizeof(void*)*3 + 3, v_isRecordingDeps_548_);
v___x_569_ = v_reuseFailAlloc_574_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
lean_ctor_set_uint16(v___x_569_, sizeof(void*)*3, v___y_539_);
v___x_570_ = l_Lean_addAndCompile(v___x_486_, v___x_536_, v___x_537_, v___x_569_, v___y_543_);
lean_dec_ref(v___x_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
v___y_453_ = v___x_570_;
goto v___jp_452_;
}
else
{
lean_object* v_a_571_; uint8_t v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
v___x_572_ = l_Lean_Exception_isInterrupt(v_a_571_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
lean_inc(v_a_571_);
v___x_573_ = l_Lean_Exception_isRuntime(v_a_571_);
v___y_468_ = v_a_571_;
v___y_469_ = v___x_570_;
v___y_470_ = v___x_573_;
goto v___jp_467_;
}
else
{
v___y_468_ = v_a_571_;
v___y_469_ = v___x_570_;
v___y_470_ = v___x_572_;
goto v___jp_467_;
}
}
}
}
}
}
}
v___jp_580_:
{
lean_object* v___x_587_; lean_object* v_env_588_; lean_object* v_nextMacroScope_589_; lean_object* v_ngen_590_; lean_object* v_auxDeclNGen_591_; lean_object* v_traceState_592_; lean_object* v_recordedDeps_593_; lean_object* v_messages_594_; lean_object* v_infoState_595_; lean_object* v_snapshotTasks_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v___x_587_ = lean_st_ref_take(v___y_585_);
v_env_588_ = lean_ctor_get(v___x_587_, 0);
v_nextMacroScope_589_ = lean_ctor_get(v___x_587_, 1);
v_ngen_590_ = lean_ctor_get(v___x_587_, 2);
v_auxDeclNGen_591_ = lean_ctor_get(v___x_587_, 3);
v_traceState_592_ = lean_ctor_get(v___x_587_, 4);
v_recordedDeps_593_ = lean_ctor_get(v___x_587_, 6);
v_messages_594_ = lean_ctor_get(v___x_587_, 7);
v_infoState_595_ = lean_ctor_get(v___x_587_, 8);
v_snapshotTasks_596_ = lean_ctor_get(v___x_587_, 9);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_587_, 5);
lean_dec(v_unused_606_);
v___x_598_ = v___x_587_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snapshotTasks_596_);
lean_inc(v_infoState_595_);
lean_inc(v_messages_594_);
lean_inc(v_recordedDeps_593_);
lean_inc(v_traceState_592_);
lean_inc(v_auxDeclNGen_591_);
lean_inc(v_ngen_590_);
lean_inc(v_nextMacroScope_589_);
lean_inc(v_env_588_);
lean_dec(v___x_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_Kernel_enableDiag(v_env_588_, v___y_584_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 5, v___x_501_);
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_nextMacroScope_589_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_ngen_590_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_auxDeclNGen_591_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_traceState_592_);
lean_ctor_set(v_reuseFailAlloc_604_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_604_, 6, v_recordedDeps_593_);
lean_ctor_set(v_reuseFailAlloc_604_, 7, v_messages_594_);
lean_ctor_set(v_reuseFailAlloc_604_, 8, v_infoState_595_);
lean_ctor_set(v_reuseFailAlloc_604_, 9, v_snapshotTasks_596_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = lean_st_ref_put(v___y_585_, v___x_602_);
v___y_539_ = v___y_583_;
v___y_540_ = v___y_582_;
v___y_541_ = v___y_586_;
v___y_542_ = v___y_581_;
v___y_543_ = v___y_585_;
goto v___jp_538_;
}
}
}
v___jp_607_:
{
uint16_t v___x_612_; lean_object* v___x_613_; lean_object* v_env_614_; uint8_t v___x_615_; uint16_t v___x_616_; uint16_t v___x_617_; uint16_t v___x_618_; uint8_t v___x_619_; 
v___x_612_ = l_Lean_OptionFlags_ofOptions(v___y_611_);
v___x_613_ = lean_st_ref_get(v___y_610_);
v_env_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_613_);
v___x_615_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_614_);
lean_dec_ref(v_env_614_);
v___x_616_ = 512;
v___x_617_ = lean_uint16_land(v___x_612_, v___x_616_);
v___x_618_ = 0;
v___x_619_ = lean_uint16_dec_eq(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
if (v___x_615_ == 0)
{
v___y_581_ = v___y_608_;
v___y_582_ = v___y_609_;
v___y_583_ = v___x_612_;
v___y_584_ = v___x_536_;
v___y_585_ = v___y_610_;
v___y_586_ = v___y_611_;
goto v___jp_580_;
}
else
{
v___y_539_ = v___x_612_;
v___y_540_ = v___y_609_;
v___y_541_ = v___y_611_;
v___y_542_ = v___y_608_;
v___y_543_ = v___y_610_;
goto v___jp_538_;
}
}
else
{
if (v___x_615_ == 0)
{
v___y_539_ = v___x_612_;
v___y_540_ = v___y_609_;
v___y_541_ = v___y_611_;
v___y_542_ = v___y_608_;
v___y_543_ = v___y_610_;
goto v___jp_538_;
}
else
{
v___y_581_ = v___y_608_;
v___y_582_ = v___y_609_;
v___y_583_ = v___x_612_;
v___y_584_ = v___x_537_;
v___y_585_ = v___y_610_;
v___y_586_ = v___y_611_;
goto v___jp_580_;
}
}
}
v___jp_620_:
{
lean_object* v_toCold_626_; lean_object* v_currRecDepth_627_; lean_object* v_ref_628_; uint8_t v_suppressElabErrors_629_; uint8_t v_isRecordingDeps_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_660_; 
v_toCold_626_ = lean_ctor_get(v___y_624_, 0);
v_currRecDepth_627_ = lean_ctor_get(v___y_624_, 1);
v_ref_628_ = lean_ctor_get(v___y_624_, 2);
v_suppressElabErrors_629_ = lean_ctor_get_uint8(v___y_624_, sizeof(void*)*3 + 2);
v_isRecordingDeps_630_ = lean_ctor_get_uint8(v___y_624_, sizeof(void*)*3 + 3);
v_isSharedCheck_660_ = !lean_is_exclusive(v___y_624_);
if (v_isSharedCheck_660_ == 0)
{
v___x_632_ = v___y_624_;
v_isShared_633_ = v_isSharedCheck_660_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_ref_628_);
lean_inc(v_currRecDepth_627_);
lean_inc(v_toCold_626_);
lean_dec(v___y_624_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_660_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_fileName_634_; lean_object* v_fileMap_635_; lean_object* v_currNamespace_636_; lean_object* v_openDecls_637_; lean_object* v_initHeartbeats_638_; lean_object* v_maxHeartbeats_639_; lean_object* v_quotContext_640_; lean_object* v_currMacroScope_641_; lean_object* v_cancelTk_x3f_642_; lean_object* v_inheritedTraceOptions_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_657_; 
v_fileName_634_ = lean_ctor_get(v_toCold_626_, 0);
v_fileMap_635_ = lean_ctor_get(v_toCold_626_, 1);
v_currNamespace_636_ = lean_ctor_get(v_toCold_626_, 4);
v_openDecls_637_ = lean_ctor_get(v_toCold_626_, 5);
v_initHeartbeats_638_ = lean_ctor_get(v_toCold_626_, 6);
v_maxHeartbeats_639_ = lean_ctor_get(v_toCold_626_, 7);
v_quotContext_640_ = lean_ctor_get(v_toCold_626_, 8);
v_currMacroScope_641_ = lean_ctor_get(v_toCold_626_, 9);
v_cancelTk_x3f_642_ = lean_ctor_get(v_toCold_626_, 10);
v_inheritedTraceOptions_643_ = lean_ctor_get(v_toCold_626_, 11);
v_isSharedCheck_657_ = !lean_is_exclusive(v_toCold_626_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; 
v_unused_658_ = lean_ctor_get(v_toCold_626_, 3);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_toCold_626_, 2);
lean_dec(v_unused_659_);
v___x_645_ = v_toCold_626_;
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_inheritedTraceOptions_643_);
lean_inc(v_cancelTk_x3f_642_);
lean_inc(v_currMacroScope_641_);
lean_inc(v_quotContext_640_);
lean_inc(v_maxHeartbeats_639_);
lean_inc(v_initHeartbeats_638_);
lean_inc(v_openDecls_637_);
lean_inc(v_currNamespace_636_);
lean_inc(v_fileMap_635_);
lean_inc(v_fileName_634_);
lean_dec(v_toCold_626_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_621_, v___y_622_);
lean_inc_ref(v___y_621_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 3, v___x_647_);
lean_ctor_set(v___x_645_, 2, v___y_621_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_fileName_634_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_fileMap_635_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v___y_621_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_currNamespace_636_);
lean_ctor_set(v_reuseFailAlloc_656_, 5, v_openDecls_637_);
lean_ctor_set(v_reuseFailAlloc_656_, 6, v_initHeartbeats_638_);
lean_ctor_set(v_reuseFailAlloc_656_, 7, v_maxHeartbeats_639_);
lean_ctor_set(v_reuseFailAlloc_656_, 8, v_quotContext_640_);
lean_ctor_set(v_reuseFailAlloc_656_, 9, v_currMacroScope_641_);
lean_ctor_set(v_reuseFailAlloc_656_, 10, v_cancelTk_x3f_642_);
lean_ctor_set(v_reuseFailAlloc_656_, 11, v_inheritedTraceOptions_643_);
v___x_649_ = v_reuseFailAlloc_656_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_649_);
v___x_651_ = v___x_632_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_currRecDepth_627_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_ref_628_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*3 + 2, v_suppressElabErrors_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*3 + 3, v_isRecordingDeps_630_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_ctor_set_uint16(v___x_651_, sizeof(void*)*3, v___y_623_);
if (v_isRecordingDeps_630_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_653_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_621_, v___x_652_, v___x_536_);
v___y_608_ = v___x_651_;
v___y_609_ = v___y_622_;
v___y_610_ = v___y_625_;
v___y_611_ = v___x_653_;
goto v___jp_607_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_621_);
v___y_608_ = v___x_651_;
v___y_609_ = v___y_622_;
v___y_610_ = v___y_625_;
v___y_611_ = v___x_654_;
goto v___jp_607_;
}
}
}
}
}
}
v___jp_661_:
{
lean_object* v___x_668_; lean_object* v_env_669_; lean_object* v_nextMacroScope_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_traceState_673_; lean_object* v_recordedDeps_674_; lean_object* v_messages_675_; lean_object* v_infoState_676_; lean_object* v_snapshotTasks_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_686_; 
v___x_668_ = lean_st_ref_take(v___y_663_);
v_env_669_ = lean_ctor_get(v___x_668_, 0);
v_nextMacroScope_670_ = lean_ctor_get(v___x_668_, 1);
v_ngen_671_ = lean_ctor_get(v___x_668_, 2);
v_auxDeclNGen_672_ = lean_ctor_get(v___x_668_, 3);
v_traceState_673_ = lean_ctor_get(v___x_668_, 4);
v_recordedDeps_674_ = lean_ctor_get(v___x_668_, 6);
v_messages_675_ = lean_ctor_get(v___x_668_, 7);
v_infoState_676_ = lean_ctor_get(v___x_668_, 8);
v_snapshotTasks_677_ = lean_ctor_get(v___x_668_, 9);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_668_, 5);
lean_dec(v_unused_687_);
v___x_679_ = v___x_668_;
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snapshotTasks_677_);
lean_inc(v_infoState_676_);
lean_inc(v_messages_675_);
lean_inc(v_recordedDeps_674_);
lean_inc(v_traceState_673_);
lean_inc(v_auxDeclNGen_672_);
lean_inc(v_ngen_671_);
lean_inc(v_nextMacroScope_670_);
lean_inc(v_env_669_);
lean_dec(v___x_668_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = l_Lean_Kernel_enableDiag(v_env_669_, v___y_665_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 5, v___x_501_);
lean_ctor_set(v___x_679_, 0, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_nextMacroScope_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_ngen_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_auxDeclNGen_672_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_traceState_673_);
lean_ctor_set(v_reuseFailAlloc_685_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_685_, 6, v_recordedDeps_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 7, v_messages_675_);
lean_ctor_set(v_reuseFailAlloc_685_, 8, v_infoState_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 9, v_snapshotTasks_677_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; 
v___x_684_ = lean_st_ref_put(v___y_663_, v___x_683_);
v___y_621_ = v___y_662_;
v___y_622_ = v___y_664_;
v___y_623_ = v___y_667_;
v___y_624_ = v___y_666_;
v___y_625_ = v___y_663_;
goto v___jp_620_;
}
}
}
v___jp_688_:
{
uint16_t v___x_693_; lean_object* v___x_694_; lean_object* v_env_695_; uint8_t v___x_696_; uint16_t v___x_697_; uint16_t v___x_698_; uint16_t v___x_699_; uint8_t v___x_700_; 
v___x_693_ = l_Lean_OptionFlags_ofOptions(v___y_692_);
v___x_694_ = lean_st_ref_get(v___y_689_);
v_env_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref(v_env_695_);
lean_dec(v___x_694_);
v___x_696_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_695_);
lean_dec_ref(v_env_695_);
v___x_697_ = 512;
v___x_698_ = lean_uint16_land(v___x_693_, v___x_697_);
v___x_699_ = 0;
v___x_700_ = lean_uint16_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
if (v___x_696_ == 0)
{
v___y_662_ = v___y_692_;
v___y_663_ = v___y_689_;
v___y_664_ = v___y_690_;
v___y_665_ = v___x_536_;
v___y_666_ = v___y_691_;
v___y_667_ = v___x_693_;
goto v___jp_661_;
}
else
{
v___y_621_ = v___y_692_;
v___y_622_ = v___y_690_;
v___y_623_ = v___x_693_;
v___y_624_ = v___y_691_;
v___y_625_ = v___y_689_;
goto v___jp_620_;
}
}
else
{
if (v___x_696_ == 0)
{
v___y_621_ = v___y_692_;
v___y_622_ = v___y_690_;
v___y_623_ = v___x_693_;
v___y_624_ = v___y_691_;
v___y_625_ = v___y_689_;
goto v___jp_620_;
}
else
{
v___y_662_ = v___y_692_;
v___y_663_ = v___y_689_;
v___y_664_ = v___y_690_;
v___y_665_ = v___x_537_;
v___y_666_ = v___y_691_;
v___y_667_ = v___x_693_;
goto v___jp_661_;
}
}
}
v___jp_701_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_719_ = l_Lean_maxRecDepth;
v___x_720_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__4(v___y_703_, v___x_719_);
lean_inc_ref(v___y_703_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 11, v_inheritedTraceOptions_713_);
lean_ctor_set(v___x_534_, 10, v_cancelTk_x3f_712_);
lean_ctor_set(v___x_534_, 9, v_currMacroScope_711_);
lean_ctor_set(v___x_534_, 8, v_quotContext_710_);
lean_ctor_set(v___x_534_, 7, v_maxHeartbeats_709_);
lean_ctor_set(v___x_534_, 6, v_initHeartbeats_708_);
lean_ctor_set(v___x_534_, 5, v_openDecls_707_);
lean_ctor_set(v___x_534_, 4, v_currNamespace_706_);
lean_ctor_set(v___x_534_, 3, v___x_720_);
lean_ctor_set(v___x_534_, 2, v___y_703_);
lean_ctor_set(v___x_534_, 1, v_fileMap_705_);
lean_ctor_set(v___x_534_, 0, v_fileName_704_);
v___x_722_ = v___x_534_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_fileName_704_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_fileMap_705_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v___y_703_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_currNamespace_706_);
lean_ctor_set(v_reuseFailAlloc_727_, 5, v_openDecls_707_);
lean_ctor_set(v_reuseFailAlloc_727_, 6, v_initHeartbeats_708_);
lean_ctor_set(v_reuseFailAlloc_727_, 7, v_maxHeartbeats_709_);
lean_ctor_set(v_reuseFailAlloc_727_, 8, v_quotContext_710_);
lean_ctor_set(v_reuseFailAlloc_727_, 9, v_currMacroScope_711_);
lean_ctor_set(v_reuseFailAlloc_727_, 10, v_cancelTk_x3f_712_);
lean_ctor_set(v_reuseFailAlloc_727_, 11, v_inheritedTraceOptions_713_);
v___x_722_ = v_reuseFailAlloc_727_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_currRecDepth_714_);
lean_ctor_set(v___x_723_, 2, v_ref_715_);
lean_ctor_set_uint16(v___x_723_, sizeof(void*)*3, v___y_702_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*3 + 2, v_suppressElabErrors_716_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*3 + 3, v_isRecordingDeps_717_);
if (v_isRecordingDeps_717_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_725_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_703_, v___x_724_, v_isRecordingDeps_717_);
v___y_689_ = v___y_718_;
v___y_690_ = v___x_719_;
v___y_691_ = v___x_723_;
v___y_692_ = v___x_725_;
goto v___jp_688_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_703_);
v___y_689_ = v___y_718_;
v___y_690_ = v___x_719_;
v___y_691_ = v___x_723_;
v___y_692_ = v___x_726_;
goto v___jp_688_;
}
}
}
v___jp_728_:
{
lean_object* v___x_732_; lean_object* v_env_733_; lean_object* v_nextMacroScope_734_; lean_object* v_ngen_735_; lean_object* v_auxDeclNGen_736_; lean_object* v_traceState_737_; lean_object* v_recordedDeps_738_; lean_object* v_messages_739_; lean_object* v_infoState_740_; lean_object* v_snapshotTasks_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_750_; 
v___x_732_ = lean_st_ref_take(v___y_433_);
v_env_733_ = lean_ctor_get(v___x_732_, 0);
v_nextMacroScope_734_ = lean_ctor_get(v___x_732_, 1);
v_ngen_735_ = lean_ctor_get(v___x_732_, 2);
v_auxDeclNGen_736_ = lean_ctor_get(v___x_732_, 3);
v_traceState_737_ = lean_ctor_get(v___x_732_, 4);
v_recordedDeps_738_ = lean_ctor_get(v___x_732_, 6);
v_messages_739_ = lean_ctor_get(v___x_732_, 7);
v_infoState_740_ = lean_ctor_get(v___x_732_, 8);
v_snapshotTasks_741_ = lean_ctor_get(v___x_732_, 9);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_732_, 5);
lean_dec(v_unused_751_);
v___x_743_ = v___x_732_;
v_isShared_744_ = v_isSharedCheck_750_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_snapshotTasks_741_);
lean_inc(v_infoState_740_);
lean_inc(v_messages_739_);
lean_inc(v_recordedDeps_738_);
lean_inc(v_traceState_737_);
lean_inc(v_auxDeclNGen_736_);
lean_inc(v_ngen_735_);
lean_inc(v_nextMacroScope_734_);
lean_inc(v_env_733_);
lean_dec(v___x_732_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_750_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = l_Lean_Kernel_enableDiag(v_env_733_, v___y_731_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 5, v___x_501_);
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_nextMacroScope_734_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_ngen_735_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_auxDeclNGen_736_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_traceState_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_749_, 6, v_recordedDeps_738_);
lean_ctor_set(v_reuseFailAlloc_749_, 7, v_messages_739_);
lean_ctor_set(v_reuseFailAlloc_749_, 8, v_infoState_740_);
lean_ctor_set(v_reuseFailAlloc_749_, 9, v_snapshotTasks_741_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_st_ref_put(v___y_433_, v___x_747_);
lean_inc(v_ref_519_);
lean_inc(v_currRecDepth_518_);
v___y_702_ = v___y_730_;
v___y_703_ = v___y_729_;
v_fileName_704_ = v_fileName_522_;
v_fileMap_705_ = v_fileMap_523_;
v_currNamespace_706_ = v_currNamespace_525_;
v_openDecls_707_ = v_openDecls_526_;
v_initHeartbeats_708_ = v_initHeartbeats_527_;
v_maxHeartbeats_709_ = v_maxHeartbeats_528_;
v_quotContext_710_ = v_quotContext_529_;
v_currMacroScope_711_ = v_currMacroScope_530_;
v_cancelTk_x3f_712_ = v_cancelTk_x3f_531_;
v_inheritedTraceOptions_713_ = v_inheritedTraceOptions_532_;
v_currRecDepth_714_ = v_currRecDepth_518_;
v_ref_715_ = v_ref_519_;
v_suppressElabErrors_716_ = v_suppressElabErrors_520_;
v_isRecordingDeps_717_ = v_isRecordingDeps_521_;
v___y_718_ = v___y_433_;
goto v___jp_701_;
}
}
}
v___jp_752_:
{
uint16_t v___x_754_; lean_object* v___x_755_; lean_object* v_env_756_; uint8_t v___x_757_; uint16_t v___x_758_; uint16_t v___x_759_; uint16_t v___x_760_; uint8_t v___x_761_; 
v___x_754_ = l_Lean_OptionFlags_ofOptions(v___y_753_);
v___x_755_ = lean_st_ref_get(v___y_433_);
v_env_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc_ref(v_env_756_);
lean_dec(v___x_755_);
v___x_757_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_756_);
lean_dec_ref(v_env_756_);
v___x_758_ = 512;
v___x_759_ = lean_uint16_land(v___x_754_, v___x_758_);
v___x_760_ = 0;
v___x_761_ = lean_uint16_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
if (v___x_757_ == 0)
{
v___y_729_ = v___y_753_;
v___y_730_ = v___x_754_;
v___y_731_ = v___x_536_;
goto v___jp_728_;
}
else
{
lean_inc(v_ref_519_);
lean_inc(v_currRecDepth_518_);
v___y_702_ = v___x_754_;
v___y_703_ = v___y_753_;
v_fileName_704_ = v_fileName_522_;
v_fileMap_705_ = v_fileMap_523_;
v_currNamespace_706_ = v_currNamespace_525_;
v_openDecls_707_ = v_openDecls_526_;
v_initHeartbeats_708_ = v_initHeartbeats_527_;
v_maxHeartbeats_709_ = v_maxHeartbeats_528_;
v_quotContext_710_ = v_quotContext_529_;
v_currMacroScope_711_ = v_currMacroScope_530_;
v_cancelTk_x3f_712_ = v_cancelTk_x3f_531_;
v_inheritedTraceOptions_713_ = v_inheritedTraceOptions_532_;
v_currRecDepth_714_ = v_currRecDepth_518_;
v_ref_715_ = v_ref_519_;
v_suppressElabErrors_716_ = v_suppressElabErrors_520_;
v_isRecordingDeps_717_ = v_isRecordingDeps_521_;
v___y_718_ = v___y_433_;
goto v___jp_701_;
}
}
else
{
if (v___x_757_ == 0)
{
lean_inc(v_ref_519_);
lean_inc(v_currRecDepth_518_);
v___y_702_ = v___x_754_;
v___y_703_ = v___y_753_;
v_fileName_704_ = v_fileName_522_;
v_fileMap_705_ = v_fileMap_523_;
v_currNamespace_706_ = v_currNamespace_525_;
v_openDecls_707_ = v_openDecls_526_;
v_initHeartbeats_708_ = v_initHeartbeats_527_;
v_maxHeartbeats_709_ = v_maxHeartbeats_528_;
v_quotContext_710_ = v_quotContext_529_;
v_currMacroScope_711_ = v_currMacroScope_530_;
v_cancelTk_x3f_712_ = v_cancelTk_x3f_531_;
v_inheritedTraceOptions_713_ = v_inheritedTraceOptions_532_;
v_currRecDepth_714_ = v_currRecDepth_518_;
v_ref_715_ = v_ref_519_;
v_suppressElabErrors_716_ = v_suppressElabErrors_520_;
v_isRecordingDeps_717_ = v_isRecordingDeps_521_;
v___y_718_ = v___y_433_;
goto v___jp_701_;
}
else
{
v___y_729_ = v___y_753_;
v___y_730_ = v___x_754_;
v___y_731_ = v___x_537_;
goto v___jp_728_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v_tacticName_775_, lean_object* v___x_776_, lean_object* v___x_777_, lean_object* v___x_778_, lean_object* v_a_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Meta_nativeEqTrue___lam__0(v_tacticName_775_, v___x_776_, v___x_777_, v___x_778_, v_a_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(lean_object* v_env_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_nextMacroScope_791_; lean_object* v_ngen_792_; lean_object* v_auxDeclNGen_793_; lean_object* v_traceState_794_; lean_object* v_recordedDeps_795_; lean_object* v_messages_796_; lean_object* v_infoState_797_; lean_object* v_snapshotTasks_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_824_; 
v___x_790_ = lean_st_ref_take(v___y_788_);
v_nextMacroScope_791_ = lean_ctor_get(v___x_790_, 1);
v_ngen_792_ = lean_ctor_get(v___x_790_, 2);
v_auxDeclNGen_793_ = lean_ctor_get(v___x_790_, 3);
v_traceState_794_ = lean_ctor_get(v___x_790_, 4);
v_recordedDeps_795_ = lean_ctor_get(v___x_790_, 6);
v_messages_796_ = lean_ctor_get(v___x_790_, 7);
v_infoState_797_ = lean_ctor_get(v___x_790_, 8);
v_snapshotTasks_798_ = lean_ctor_get(v___x_790_, 9);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; lean_object* v_unused_826_; 
v_unused_825_ = lean_ctor_get(v___x_790_, 5);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v___x_790_, 0);
lean_dec(v_unused_826_);
v___x_800_ = v___x_790_;
v_isShared_801_ = v_isSharedCheck_824_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snapshotTasks_798_);
lean_inc(v_infoState_797_);
lean_inc(v_messages_796_);
lean_inc(v_recordedDeps_795_);
lean_inc(v_traceState_794_);
lean_inc(v_auxDeclNGen_793_);
lean_inc(v_ngen_792_);
lean_inc(v_nextMacroScope_791_);
lean_dec(v___x_790_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_824_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 5, v___x_802_);
lean_ctor_set(v___x_800_, 0, v_env_786_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_env_786_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_nextMacroScope_791_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_ngen_792_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_auxDeclNGen_793_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_traceState_794_);
lean_ctor_set(v_reuseFailAlloc_823_, 5, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_823_, 6, v_recordedDeps_795_);
lean_ctor_set(v_reuseFailAlloc_823_, 7, v_messages_796_);
lean_ctor_set(v_reuseFailAlloc_823_, 8, v_infoState_797_);
lean_ctor_set(v_reuseFailAlloc_823_, 9, v_snapshotTasks_798_);
v___x_804_ = v_reuseFailAlloc_823_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_mctx_807_; lean_object* v_zetaDeltaFVarIds_808_; lean_object* v_postponed_809_; lean_object* v_diag_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_821_; 
v___x_805_ = lean_st_ref_put(v___y_788_, v___x_804_);
v___x_806_ = lean_st_ref_take(v___y_787_);
v_mctx_807_ = lean_ctor_get(v___x_806_, 0);
v_zetaDeltaFVarIds_808_ = lean_ctor_get(v___x_806_, 2);
v_postponed_809_ = lean_ctor_get(v___x_806_, 3);
v_diag_810_ = lean_ctor_get(v___x_806_, 4);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_806_, 1);
lean_dec(v_unused_822_);
v___x_812_ = v___x_806_;
v_isShared_813_ = v_isSharedCheck_821_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_diag_810_);
lean_inc(v_postponed_809_);
lean_inc(v_zetaDeltaFVarIds_808_);
lean_inc(v_mctx_807_);
lean_dec(v___x_806_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_821_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_814_ = lean_box(0);
v___x_815_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_815_);
v___x_817_ = v___x_812_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_mctx_807_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_zetaDeltaFVarIds_808_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_postponed_809_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_diag_810_);
v___x_817_ = v_reuseFailAlloc_820_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_st_ref_put(v___y_787_, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_814_);
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg___boxed(lean_object* v_env_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(lean_object* v_env_832_, lean_object* v_x_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v_env_840_; lean_object* v_a_842_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_839_ = lean_st_ref_get(v___y_837_);
v_env_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc_ref(v_env_840_);
lean_dec(v___x_839_);
v___x_852_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_832_, v___y_835_, v___y_837_);
lean_dec_ref(v___x_852_);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
v___x_853_ = lean_apply_5(v_x_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, lean_box(0));
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_840_, v___y_835_, v___y_837_);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v___x_855_, 0);
lean_dec(v_unused_863_);
v___x_857_ = v___x_855_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_dec(v___x_855_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v_a_854_);
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_854_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v_a_864_; 
v_a_864_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_853_, 1);
v_a_842_ = v_a_864_;
goto v___jp_841_;
}
v___jp_841_:
{
lean_object* v___x_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v___x_843_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_840_, v___y_835_, v___y_837_);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_843_, 0);
lean_dec(v_unused_851_);
v___x_845_ = v___x_843_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_dec(v___x_843_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 1);
lean_ctor_set(v___x_845_, 0, v_a_842_);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_842_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg___boxed(lean_object* v_env_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_865_, v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(lean_object* v_stx_873_, lean_object* v___y_874_){
_start:
{
uint8_t v___x_876_; lean_object* v___x_877_; 
v___x_876_ = 0;
v___x_877_ = l_Lean_Syntax_getRange_x3f(v_stx_873_, v___x_876_);
if (lean_obj_tag(v___x_877_) == 1)
{
lean_object* v_toCold_878_; lean_object* v_val_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_toCold_878_ = lean_ctor_get(v___y_874_, 0);
v_val_879_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v___x_877_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_val_879_);
lean_dec(v___x_877_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_fileMap_883_; lean_object* v_start_884_; lean_object* v_stop_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v_fileMap_883_ = lean_ctor_get(v_toCold_878_, 1);
v_start_884_ = lean_ctor_get(v_val_879_, 0);
lean_inc(v_start_884_);
v_stop_885_ = lean_ctor_get(v_val_879_, 1);
lean_inc(v_stop_885_);
lean_dec(v_val_879_);
lean_inc_ref(v_fileMap_883_);
v___x_886_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_883_, v_start_884_, v_stop_885_);
lean_dec(v_stop_885_);
lean_dec(v_start_884_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_886_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_890_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v___x_877_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg___boxed(lean_object* v_stx_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_894_, v___y_895_);
lean_dec_ref(v___y_895_);
lean_dec(v_stx_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(lean_object* v_declName_898_, lean_object* v_declRanges_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Name_isAnonymous(v_declName_898_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v_env_905_; lean_object* v_nextMacroScope_906_; lean_object* v_ngen_907_; lean_object* v_auxDeclNGen_908_; lean_object* v_traceState_909_; lean_object* v_recordedDeps_910_; lean_object* v_messages_911_; lean_object* v_infoState_912_; lean_object* v_snapshotTasks_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_941_; 
v___x_904_ = lean_st_ref_take(v___y_901_);
v_env_905_ = lean_ctor_get(v___x_904_, 0);
v_nextMacroScope_906_ = lean_ctor_get(v___x_904_, 1);
v_ngen_907_ = lean_ctor_get(v___x_904_, 2);
v_auxDeclNGen_908_ = lean_ctor_get(v___x_904_, 3);
v_traceState_909_ = lean_ctor_get(v___x_904_, 4);
v_recordedDeps_910_ = lean_ctor_get(v___x_904_, 6);
v_messages_911_ = lean_ctor_get(v___x_904_, 7);
v_infoState_912_ = lean_ctor_get(v___x_904_, 8);
v_snapshotTasks_913_ = lean_ctor_get(v___x_904_, 9);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_904_, 5);
lean_dec(v_unused_942_);
v___x_915_ = v___x_904_;
v_isShared_916_ = v_isSharedCheck_941_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snapshotTasks_913_);
lean_inc(v_infoState_912_);
lean_inc(v_messages_911_);
lean_inc(v_recordedDeps_910_);
lean_inc(v_traceState_909_);
lean_inc(v_auxDeclNGen_908_);
lean_inc(v_ngen_907_);
lean_inc(v_nextMacroScope_906_);
lean_inc(v_env_905_);
lean_dec(v___x_904_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_941_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_917_ = l_Lean_declRangeExt;
v___x_918_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_917_, v_env_905_, v_declName_898_, v_declRanges_899_);
v___x_919_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__11, &l_Lean_Meta_nativeEqTrue___lam__0___closed__11_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__11);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 5, v___x_919_);
lean_ctor_set(v___x_915_, 0, v___x_918_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_nextMacroScope_906_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_ngen_907_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_auxDeclNGen_908_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_traceState_909_);
lean_ctor_set(v_reuseFailAlloc_940_, 5, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_940_, 6, v_recordedDeps_910_);
lean_ctor_set(v_reuseFailAlloc_940_, 7, v_messages_911_);
lean_ctor_set(v_reuseFailAlloc_940_, 8, v_infoState_912_);
lean_ctor_set(v_reuseFailAlloc_940_, 9, v_snapshotTasks_913_);
v___x_921_ = v_reuseFailAlloc_940_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_mctx_924_; lean_object* v_zetaDeltaFVarIds_925_; lean_object* v_postponed_926_; lean_object* v_diag_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_938_; 
v___x_922_ = lean_st_ref_put(v___y_901_, v___x_921_);
v___x_923_ = lean_st_ref_take(v___y_900_);
v_mctx_924_ = lean_ctor_get(v___x_923_, 0);
v_zetaDeltaFVarIds_925_ = lean_ctor_get(v___x_923_, 2);
v_postponed_926_ = lean_ctor_get(v___x_923_, 3);
v_diag_927_ = lean_ctor_get(v___x_923_, 4);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_923_, 1);
lean_dec(v_unused_939_);
v___x_929_ = v___x_923_;
v_isShared_930_ = v_isSharedCheck_938_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_diag_927_);
lean_inc(v_postponed_926_);
lean_inc(v_zetaDeltaFVarIds_925_);
lean_inc(v_mctx_924_);
lean_dec(v___x_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_938_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = lean_box(0);
v___x_932_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_mctx_924_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_zetaDeltaFVarIds_925_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_postponed_926_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_diag_927_);
v___x_934_ = v_reuseFailAlloc_937_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_st_ref_put(v___y_900_, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_931_);
return v___x_936_;
}
}
}
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec_ref(v_declRanges_899_);
lean_dec(v_declName_898_);
v___x_943_ = lean_box(0);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg___boxed(lean_object* v_declName_945_, lean_object* v_declRanges_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_945_, v_declRanges_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_declName_951_, lean_object* v_rangeStx_952_, lean_object* v_selectionRangeStx_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_976_; 
v___x_959_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_rangeStx_952_, v___y_956_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_976_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_976_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_976_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
if (lean_obj_tag(v_a_960_) == 1)
{
lean_object* v_val_964_; lean_object* v_a_966_; lean_object* v___x_969_; lean_object* v_a_970_; 
lean_del_object(v___x_962_);
v_val_964_ = lean_ctor_get(v_a_960_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v_a_960_, 1);
v___x_969_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_selectionRangeStx_953_, v___y_956_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
if (lean_obj_tag(v_a_970_) == 0)
{
lean_inc(v_val_964_);
v_a_966_ = v_val_964_;
goto v___jp_965_;
}
else
{
lean_object* v_val_971_; 
v_val_971_ = lean_ctor_get(v_a_970_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v_a_970_, 1);
v_a_966_ = v_val_971_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_val_964_);
lean_ctor_set(v___x_967_, 1, v_a_966_);
v___x_968_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_951_, v___x_967_, v___y_955_, v___y_957_);
return v___x_968_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec(v_a_960_);
lean_dec(v_declName_951_);
v___x_972_ = lean_box(0);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_972_);
v___x_974_ = v___x_962_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8___boxed(lean_object* v_declName_977_, lean_object* v_rangeStx_978_, lean_object* v_selectionRangeStx_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_declName_977_, v_rangeStx_978_, v_selectionRangeStx_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v_selectionRangeStx_979_);
lean_dec(v_rangeStx_978_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
if (lean_obj_tag(v_a_986_) == 0)
{
lean_object* v___x_988_; 
v___x_988_ = l_List_reverse___redArg(v_a_987_);
return v___x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_tail_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_999_; 
v_head_989_ = lean_ctor_get(v_a_986_, 0);
v_tail_990_ = lean_ctor_get(v_a_986_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_a_986_);
if (v_isSharedCheck_999_ == 0)
{
v___x_992_ = v_a_986_;
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_tail_990_);
lean_inc(v_head_989_);
lean_dec(v_a_986_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = l_Lean_mkLevelParam(v_head_989_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v_a_987_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_a_987_);
v___x_996_ = v_reuseFailAlloc_998_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
v_a_986_ = v_tail_990_;
v_a_987_ = v___x_996_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_unsigned_to_nat(16u);
v___x_1002_ = lean_mk_array(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_1009_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_ctor_set(v___x_1010_, 2, v___x_1008_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = l_Lean_Level_ofNat(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_1029_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_1030_ = l_Lean_mkConst(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_box(0);
v___x_1032_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__7));
v___x_1033_ = l_Lean_mkConst(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_1040_ = l_Lean_mkConst(v___x_1039_, v___x_1038_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_1047_, lean_object* v_e_1048_, lean_object* v_axiomDeclRange_x3f_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___x_1170_; 
v___x_1063_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_1048_, v_a_1051_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v___x_1063_);
v___x_1170_ = l_Lean_Expr_hasFVar(v_a_1064_);
if (v___x_1170_ == 0)
{
v___y_1149_ = v_a_1050_;
v___y_1150_ = v_a_1051_;
v___y_1151_ = v_a_1052_;
v___y_1152_ = v_a_1053_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v___x_1171_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1172_ = l_Lean_MessageData_ofName(v_tacticName_1047_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_indentExpr(v_a_1064_);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1177_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
v___jp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__7(v___y_1057_, v___x_1058_);
v___x_1060_ = l_Lean_mkConst(v___y_1056_, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
v___jp_1065_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_params_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1145_; 
v___x_1070_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1064_);
v___x_1071_ = l_Lean_collectLevelParams(v___x_1070_, v_a_1064_);
v_params_1072_ = lean_ctor_get(v___x_1071_, 2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1146_ = lean_ctor_get(v___x_1071_, 1);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v___x_1071_, 0);
lean_dec(v_unused_1147_);
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1145_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_params_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1145_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v_env_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_array_to_list(v_params_1072_);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_1047_);
v___x_1079_ = l_Lean_Name_append(v___x_1078_, v_tacticName_1047_);
v___x_1080_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1079_);
v___x_1081_ = l_Lean_Name_append(v___x_1079_, v___x_1080_);
lean_inc(v_a_1064_);
lean_inc(v___x_1077_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1082_, 0, v_tacticName_1047_);
lean_closure_set(v___f_1082_, 1, v___x_1081_);
lean_closure_set(v___f_1082_, 2, v___x_1077_);
lean_closure_set(v___f_1082_, 3, v___x_1076_);
lean_closure_set(v___f_1082_, 4, v_a_1064_);
v___x_1083_ = lean_st_ref_get(v___y_1069_);
v_env_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_env_1084_);
lean_dec(v___x_1083_);
v___x_1085_ = l_Lean_Environment_unlockAsync(v_env_1084_);
v___x_1086_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v___x_1085_, v___f_1082_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1136_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1136_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1136_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_unbox(v_a_1087_);
lean_dec(v_a_1087_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_dec(v___x_1079_);
lean_dec(v___x_1077_);
lean_del_object(v___x_1074_);
lean_dec(v_a_1064_);
v___x_1092_ = lean_box(1);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1135_; 
lean_del_object(v___x_1089_);
v___x_1096_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1097_ = l_Lean_Name_append(v___x_1079_, v___x_1096_);
v___x_1098_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1097_, v___y_1069_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1135_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1135_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1103_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1104_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1105_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1106_ = l_Lean_mkApp3(v___x_1103_, v___x_1104_, v_a_1064_, v___x_1105_);
lean_inc(v___x_1077_);
lean_inc(v_a_1099_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v___x_1106_);
lean_ctor_set(v___x_1074_, 1, v___x_1077_);
lean_ctor_set(v___x_1074_, 0, v_a_1099_);
v___x_1108_ = v___x_1074_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1099_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1109_ = 0;
v___x_1110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*1, v___x_1109_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1110_);
v___x_1112_ = v___x_1101_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_addDecl(v___x_1112_, v___x_1109_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1049_) == 1)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_val_1114_ = lean_ctor_get(v_axiomDeclRange_x3f_1049_, 0);
v___x_1115_ = lean_box(0);
lean_inc(v_a_1099_);
v___x_1116_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8(v_a_1099_, v_val_1114_, v___x_1115_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_dec_ref_known(v___x_1116_, 1);
v___y_1056_ = v_a_1099_;
v___y_1057_ = v___x_1077_;
goto v___jp_1055_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_a_1099_);
lean_dec(v___x_1077_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
v___y_1056_ = v_a_1099_;
v___y_1057_ = v___x_1077_;
goto v___jp_1055_;
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_a_1099_);
lean_dec(v___x_1077_);
v_a_1125_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1113_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1113_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
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
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v___x_1079_);
lean_dec(v___x_1077_);
lean_del_object(v___x_1074_);
lean_dec(v_a_1064_);
v_a_1137_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1086_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1086_);
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
v___jp_1148_:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Lean_Expr_hasMVar(v_a_1064_);
if (v___x_1153_ == 0)
{
v___y_1066_ = v___y_1149_;
v___y_1067_ = v___y_1150_;
v___y_1068_ = v___y_1151_;
v___y_1069_ = v___y_1152_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v___x_1154_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1155_ = l_Lean_MessageData_ofName(v_tacticName_1047_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_indentExpr(v_a_1064_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1160_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1187_, lean_object* v_e_1188_, lean_object* v_axiomDeclRange_x3f_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1187_, v_e_1188_, v_axiomDeclRange_x3f_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_axiomDeclRange_x3f_1189_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1210_, lean_object* v_constName_1211_, uint8_t v_checkMeta_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1211_, v_checkMeta_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_constName_1220_, lean_object* v_checkMeta_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_checkMeta_boxed_1227_; lean_object* v_res_1228_; 
v_checkMeta_boxed_1227_ = lean_unbox(v_checkMeta_1221_);
v_res_1228_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1219_, v_constName_1220_, v_checkMeta_boxed_1227_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1229_, lean_object* v_msg_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1237_, v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(lean_object* v_env_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___redArg(v_env_1245_, v___y_1247_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___boxed(lean_object* v_env_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(v_env_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_00_u03b1_1259_, lean_object* v_env_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___redArg(v_env_1260_, v_x_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object* v_00_u03b1_1268_, lean_object* v_env_1269_, lean_object* v_x_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__6(v_00_u03b1_1268_, v_env_1269_, v_x_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(lean_object* v_stx_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___redArg(v_stx_1277_, v___y_1280_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13___boxed(lean_object* v_stx_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__13(v_stx_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v_stx_1284_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(lean_object* v_declName_1291_, lean_object* v_declRanges_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___redArg(v_declName_1291_, v_declRanges_1292_, v___y_1294_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14___boxed(lean_object* v_declName_1299_, lean_object* v_declRanges_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__8_spec__14(v_declName_1299_, v_declRanges_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1315_, v_x_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1322_;
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

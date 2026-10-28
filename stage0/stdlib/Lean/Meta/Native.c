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
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_declRangeExt;
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(lean_object* v_opts_237_, lean_object* v_opt_238_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5___boxed(lean_object* v_opts_245_, lean_object* v_opt_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v_opts_245_, v_opt_246_);
lean_dec_ref(v_opt_246_);
lean_dec_ref(v_opts_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(lean_object* v_o_251_, lean_object* v_k_252_, uint8_t v_v_253_){
_start:
{
lean_object* v_map_254_; uint8_t v_hasTrace_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_269_; 
v_map_254_ = lean_ctor_get(v_o_251_, 0);
v_hasTrace_255_ = lean_ctor_get_uint8(v_o_251_, sizeof(void*)*1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_o_251_);
if (v_isSharedCheck_269_ == 0)
{
v___x_257_ = v_o_251_;
v_isShared_258_ = v_isSharedCheck_269_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_map_254_);
lean_dec(v_o_251_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_269_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_259_, 0, v_v_253_);
lean_inc(v_k_252_);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_252_, v___x_259_, v_map_254_);
if (v_hasTrace_255_ == 0)
{
lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_264_; 
v___x_261_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___closed__1));
v___x_262_ = l_Lean_Name_isPrefixOf(v___x_261_, v_k_252_);
lean_dec(v_k_252_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_260_);
v___x_264_ = v___x_257_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_260_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*1, v___x_262_);
return v___x_264_;
}
}
else
{
lean_object* v___x_267_; 
lean_dec(v_k_252_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_260_);
v___x_267_ = v___x_257_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_260_);
lean_ctor_set_uint8(v_reuseFailAlloc_268_, sizeof(void*)*1, v_hasTrace_255_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10___boxed(lean_object* v_o_270_, lean_object* v_k_271_, lean_object* v_v_272_){
_start:
{
uint8_t v_v_boxed_273_; lean_object* v_res_274_; 
v_v_boxed_273_ = lean_unbox(v_v_272_);
v_res_274_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(v_o_270_, v_k_271_, v_v_boxed_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6(lean_object* v_opts_275_, lean_object* v_opt_276_, uint8_t v_val_277_){
_start:
{
lean_object* v_name_278_; lean_object* v___x_279_; 
v_name_278_ = lean_ctor_get(v_opt_276_, 0);
lean_inc(v_name_278_);
lean_dec_ref(v_opt_276_);
v___x_279_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6_spec__10(v_opts_275_, v_name_278_, v_val_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6___boxed(lean_object* v_opts_280_, lean_object* v_opt_281_, lean_object* v_val_282_){
_start:
{
uint8_t v_val_boxed_283_; lean_object* v_res_284_; 
v_val_boxed_283_ = lean_unbox(v_val_282_);
v_res_284_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6(v_opts_280_, v_opt_281_, v_val_boxed_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(lean_object* v_msgData_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v_env_292_; uint8_t v___x_293_; lean_object* v_env_294_; lean_object* v___x_295_; lean_object* v_toCold_296_; lean_object* v_mctx_297_; lean_object* v_lctx_298_; lean_object* v_options_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_291_ = lean_st_ref_get(v___y_289_);
v_env_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_env_292_);
lean_dec(v___x_291_);
v___x_293_ = 0;
v_env_294_ = l_Lean_Environment_setRecordingDeps(v_env_292_, v___x_293_);
v___x_295_ = lean_st_ref_get(v___y_287_);
v_toCold_296_ = lean_ctor_get(v___y_288_, 0);
v_mctx_297_ = lean_ctor_get(v___x_295_, 0);
lean_inc_ref(v_mctx_297_);
lean_dec(v___x_295_);
v_lctx_298_ = lean_ctor_get(v___y_286_, 2);
v_options_299_ = lean_ctor_get(v_toCold_296_, 2);
lean_inc_ref(v_options_299_);
lean_inc_ref(v_lctx_298_);
v___x_300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_300_, 0, v_env_294_);
lean_ctor_set(v___x_300_, 1, v_mctx_297_);
lean_ctor_set(v___x_300_, 2, v_lctx_298_);
lean_ctor_set(v___x_300_, 3, v_options_299_);
v___x_301_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_msgData_285_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5___boxed(lean_object* v_msgData_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msgData_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_ref_316_; lean_object* v___x_317_; lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
v_ref_316_ = lean_ctor_get(v___y_313_, 2);
v___x_317_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3_spec__5(v_msg_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc(v_ref_316_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_ref_316_);
lean_ctor_set(v___x_322_, 1, v_a_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 1);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg___boxed(lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_334_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg(){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__1);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___boxed(lean_object* v___dummy_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg();
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_box(0);
v___x_342_ = l_Lean_Elab_abortCommandExceptionId;
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___closed__0);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg___boxed(lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(lean_object* v_x_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_a_355_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v_x_349_, 1);
v___x_356_ = l_Lean_stringToMessageData(v_a_355_);
v___x_357_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_356_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v___x_357_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v_x_349_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_349_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v_x_349_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v_x_349_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 0);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg___boxed(lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(lean_object* v_constName_373_, uint8_t v_checkMeta_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; lean_object* v_env_381_; uint8_t v___x_382_; 
v___x_380_ = lean_st_ref_get(v___y_378_);
v_env_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_381_);
lean_dec(v___x_380_);
lean_inc(v_constName_373_);
v___x_382_ = lean_has_compile_error(v_env_381_, v_constName_373_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v_env_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_383_ = lean_st_ref_get(v___y_378_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
v___x_385_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_377_);
v___x_386_ = l_Lean_Environment_evalConst___redArg(v_env_384_, v___x_385_, v_constName_373_, v_checkMeta_374_);
lean_dec(v_constName_373_);
lean_dec_ref(v___x_385_);
lean_dec_ref(v_env_384_);
v___x_387_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_386_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_389_; lean_object* v_env_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref_known(v___x_388_, 1);
v___x_389_ = lean_st_ref_get(v___y_378_);
v_env_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_env_390_);
lean_dec(v___x_389_);
v___x_391_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_377_);
v___x_392_ = l_Lean_Environment_evalConst___redArg(v_env_390_, v___x_391_, v_constName_373_, v_checkMeta_374_);
lean_dec(v_constName_373_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v_env_390_);
v___x_393_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v___x_392_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
return v___x_393_;
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_constName_373_);
v_a_394_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_388_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_388_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg___boxed(lean_object* v_constName_402_, lean_object* v_checkMeta_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
uint8_t v_checkMeta_boxed_409_; lean_object* v_res_410_; 
v_checkMeta_boxed_409_ = lean_unbox(v_checkMeta_403_);
v_res_410_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_402_, v_checkMeta_boxed_409_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__0));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__2));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_box(0);
v___x_421_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__5));
v___x_422_ = l_Lean_mkConst(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg___closed__0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__7, &l_Lean_Meta_nativeEqTrue___lam__0___closed__7_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__7);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7___redArg();
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__7, &l_Lean_Meta_nativeEqTrue___lam__0___closed__7_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__7);
v___x_429_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
v___x_430_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_428_);
lean_ctor_set(v___x_430_, 3, v___x_428_);
lean_ctor_set(v___x_430_, 4, v___x_428_);
lean_ctor_set(v___x_430_, 5, v___x_428_);
lean_ctor_set(v___x_430_, 6, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__11));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0(lean_object* v___x_434_, lean_object* v_tacticName_435_, lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v_a_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_788_; 
v___x_444_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_434_, v___y_442_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_788_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_788_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_788_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_463_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__6, &l_Lean_Meta_nativeEqTrue___lam__0___closed__6_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__6);
lean_inc_n(v_a_445_, 2);
v___x_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_464_, 0, v_a_445_);
lean_ctor_set(v___x_464_, 1, v___x_436_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
v___x_465_ = lean_box(1);
v___x_466_ = 1;
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v_a_445_);
lean_ctor_set(v___x_467_, 1, v___x_437_);
v___x_468_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_468_, 0, v___x_464_);
lean_ctor_set(v___x_468_, 1, v_a_438_);
lean_ctor_set(v___x_468_, 2, v___x_465_);
lean_ctor_set(v___x_468_, 3, v___x_467_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*4, v___x_466_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 0, v___x_468_);
v___x_470_ = v___x_447_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_787_;
goto v_reusejp_469_;
}
v___jp_449_:
{
uint8_t v___x_450_; lean_object* v___x_451_; 
v___x_450_ = 1;
v___x_451_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_a_445_, v___x_450_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_dec_ref(v___y_441_);
lean_dec(v_tacticName_435_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; uint8_t v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v___x_453_ = l_Lean_Exception_isInterrupt(v_a_452_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
lean_inc(v_a_452_);
v___x_454_ = l_Lean_Exception_isRuntime(v_a_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_455_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_456_ = l_Lean_MessageData_ofName(v_tacticName_435_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__3, &l_Lean_Meta_nativeEqTrue___lam__0___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__3);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_Exception_toMessageData(v_a_452_);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_461_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v___y_441_);
return v___x_462_;
}
else
{
lean_dec_ref(v___y_441_);
lean_dec(v_tacticName_435_);
return v___x_451_;
}
}
else
{
lean_dec_ref(v___y_441_);
lean_dec(v_tacticName_435_);
return v___x_451_;
}
}
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v_env_472_; lean_object* v_nextMacroScope_473_; lean_object* v_ngen_474_; lean_object* v_auxDeclNGen_475_; lean_object* v_traceState_476_; lean_object* v_recordedDeps_477_; lean_object* v_messages_478_; lean_object* v_infoState_479_; lean_object* v_snapshotTasks_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_785_; 
v___x_471_ = lean_st_ref_take(v___y_442_);
v_env_472_ = lean_ctor_get(v___x_471_, 0);
v_nextMacroScope_473_ = lean_ctor_get(v___x_471_, 1);
v_ngen_474_ = lean_ctor_get(v___x_471_, 2);
v_auxDeclNGen_475_ = lean_ctor_get(v___x_471_, 3);
v_traceState_476_ = lean_ctor_get(v___x_471_, 4);
v_recordedDeps_477_ = lean_ctor_get(v___x_471_, 6);
v_messages_478_ = lean_ctor_get(v___x_471_, 7);
v_infoState_479_ = lean_ctor_get(v___x_471_, 8);
v_snapshotTasks_480_ = lean_ctor_get(v___x_471_, 9);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_471_, 5);
lean_dec(v_unused_786_);
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_785_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snapshotTasks_480_);
lean_inc(v_infoState_479_);
lean_inc(v_messages_478_);
lean_inc(v_recordedDeps_477_);
lean_inc(v_traceState_476_);
lean_inc(v_auxDeclNGen_475_);
lean_inc(v_ngen_474_);
lean_inc(v_nextMacroScope_473_);
lean_inc(v_env_472_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_785_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
lean_inc(v_a_445_);
v___x_484_ = l_Lean_markMeta(v_env_472_, v_a_445_);
v___x_485_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 5, v___x_485_);
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_nextMacroScope_473_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_ngen_474_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_auxDeclNGen_475_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_traceState_476_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_recordedDeps_477_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_messages_478_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_infoState_479_);
lean_ctor_set(v_reuseFailAlloc_784_, 9, v_snapshotTasks_480_);
v___x_487_ = v_reuseFailAlloc_784_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_mctx_490_; lean_object* v_zetaDeltaFVarIds_491_; lean_object* v_postponed_492_; lean_object* v_diag_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_782_; 
v___x_488_ = lean_st_ref_put(v___y_442_, v___x_487_);
v___x_489_ = lean_st_ref_take(v___y_440_);
v_mctx_490_ = lean_ctor_get(v___x_489_, 0);
v_zetaDeltaFVarIds_491_ = lean_ctor_get(v___x_489_, 2);
v_postponed_492_ = lean_ctor_get(v___x_489_, 3);
v_diag_493_ = lean_ctor_get(v___x_489_, 4);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_489_, 1);
lean_dec(v_unused_783_);
v___x_495_ = v___x_489_;
v_isShared_496_ = v_isSharedCheck_782_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_diag_493_);
lean_inc(v_postponed_492_);
lean_inc(v_zetaDeltaFVarIds_491_);
lean_inc(v_mctx_490_);
lean_dec(v___x_489_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_782_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_mctx_490_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_zetaDeltaFVarIds_491_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_postponed_492_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_diag_493_);
v___x_499_ = v_reuseFailAlloc_781_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v_toCold_501_; lean_object* v_currRecDepth_502_; lean_object* v_ref_503_; uint8_t v_suppressElabErrors_504_; uint8_t v_checkDeprecated_505_; uint8_t v_isRecordingDeps_506_; lean_object* v_fileName_507_; lean_object* v_fileMap_508_; lean_object* v_options_509_; lean_object* v_currNamespace_510_; lean_object* v_openDecls_511_; lean_object* v_initHeartbeats_512_; lean_object* v_maxHeartbeats_513_; lean_object* v_quotContext_514_; lean_object* v_currMacroScope_515_; lean_object* v_cancelTk_x3f_516_; lean_object* v_inheritedTraceOptions_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_779_; 
v___x_500_ = lean_st_ref_put(v___y_440_, v___x_499_);
v_toCold_501_ = lean_ctor_get(v___y_441_, 0);
lean_inc_ref(v_toCold_501_);
v_currRecDepth_502_ = lean_ctor_get(v___y_441_, 1);
v_ref_503_ = lean_ctor_get(v___y_441_, 2);
v_suppressElabErrors_504_ = lean_ctor_get_uint8(v___y_441_, sizeof(void*)*3 + 2);
v_checkDeprecated_505_ = lean_ctor_get_uint8(v___y_441_, sizeof(void*)*3 + 3);
v_isRecordingDeps_506_ = lean_ctor_get_uint8(v___y_441_, sizeof(void*)*3 + 4);
v_fileName_507_ = lean_ctor_get(v_toCold_501_, 0);
v_fileMap_508_ = lean_ctor_get(v_toCold_501_, 1);
v_options_509_ = lean_ctor_get(v_toCold_501_, 2);
v_currNamespace_510_ = lean_ctor_get(v_toCold_501_, 4);
v_openDecls_511_ = lean_ctor_get(v_toCold_501_, 5);
v_initHeartbeats_512_ = lean_ctor_get(v_toCold_501_, 6);
v_maxHeartbeats_513_ = lean_ctor_get(v_toCold_501_, 7);
v_quotContext_514_ = lean_ctor_get(v_toCold_501_, 8);
v_currMacroScope_515_ = lean_ctor_get(v_toCold_501_, 9);
v_cancelTk_x3f_516_ = lean_ctor_get(v_toCold_501_, 10);
v_inheritedTraceOptions_517_ = lean_ctor_get(v_toCold_501_, 11);
v_isSharedCheck_779_ = !lean_is_exclusive(v_toCold_501_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v_toCold_501_, 3);
lean_dec(v_unused_780_);
v___x_519_ = v_toCold_501_;
v_isShared_520_ = v_isSharedCheck_779_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_inheritedTraceOptions_517_);
lean_inc(v_cancelTk_x3f_516_);
lean_inc(v_currMacroScope_515_);
lean_inc(v_quotContext_514_);
lean_inc(v_maxHeartbeats_513_);
lean_inc(v_initHeartbeats_512_);
lean_inc(v_openDecls_511_);
lean_inc(v_currNamespace_510_);
lean_inc(v_options_509_);
lean_inc(v_fileMap_508_);
lean_inc(v_fileName_507_);
lean_dec(v_toCold_501_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_779_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___x_521_; uint8_t v___x_522_; lean_object* v___y_524_; lean_object* v___y_525_; uint16_t v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; uint8_t v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; uint16_t v___y_598_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_633_; uint16_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; uint8_t v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; uint16_t v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint16_t v___y_715_; lean_object* v___y_716_; lean_object* v_fileName_717_; lean_object* v_fileMap_718_; lean_object* v_currNamespace_719_; lean_object* v_openDecls_720_; lean_object* v_initHeartbeats_721_; lean_object* v_maxHeartbeats_722_; lean_object* v_quotContext_723_; lean_object* v_currMacroScope_724_; lean_object* v_cancelTk_x3f_725_; lean_object* v_inheritedTraceOptions_726_; lean_object* v_currRecDepth_727_; lean_object* v_ref_728_; uint8_t v_suppressElabErrors_729_; uint8_t v_checkDeprecated_730_; uint8_t v_isRecordingDeps_731_; lean_object* v___y_732_; uint16_t v___y_743_; lean_object* v___y_744_; uint8_t v___y_745_; lean_object* v___y_767_; 
v___x_521_ = 1;
v___x_522_ = 0;
if (v_isRecordingDeps_506_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = l_Lean_Elab_async;
v___x_777_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6(v_options_509_, v___x_776_, v_isRecordingDeps_506_);
v___y_767_ = v___x_777_;
goto v___jp_766_;
}
else
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_509_);
v___y_767_ = v___x_778_;
goto v___jp_766_;
}
v___jp_523_:
{
lean_object* v_toCold_529_; lean_object* v_currRecDepth_530_; lean_object* v_ref_531_; uint8_t v_suppressElabErrors_532_; uint8_t v_checkDeprecated_533_; uint8_t v_isRecordingDeps_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_591_; 
v_toCold_529_ = lean_ctor_get(v___y_527_, 0);
v_currRecDepth_530_ = lean_ctor_get(v___y_527_, 1);
v_ref_531_ = lean_ctor_get(v___y_527_, 2);
v_suppressElabErrors_532_ = lean_ctor_get_uint8(v___y_527_, sizeof(void*)*3 + 2);
v_checkDeprecated_533_ = lean_ctor_get_uint8(v___y_527_, sizeof(void*)*3 + 3);
v_isRecordingDeps_534_ = lean_ctor_get_uint8(v___y_527_, sizeof(void*)*3 + 4);
v_isSharedCheck_591_ = !lean_is_exclusive(v___y_527_);
if (v_isSharedCheck_591_ == 0)
{
v___x_536_ = v___y_527_;
v_isShared_537_ = v_isSharedCheck_591_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_ref_531_);
lean_inc(v_currRecDepth_530_);
lean_inc(v_toCold_529_);
lean_dec(v___y_527_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_591_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_fileName_538_; lean_object* v_fileMap_539_; lean_object* v_currNamespace_540_; lean_object* v_openDecls_541_; lean_object* v_initHeartbeats_542_; lean_object* v_maxHeartbeats_543_; lean_object* v_quotContext_544_; lean_object* v_currMacroScope_545_; lean_object* v_cancelTk_x3f_546_; lean_object* v_inheritedTraceOptions_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_588_; 
v_fileName_538_ = lean_ctor_get(v_toCold_529_, 0);
v_fileMap_539_ = lean_ctor_get(v_toCold_529_, 1);
v_currNamespace_540_ = lean_ctor_get(v_toCold_529_, 4);
v_openDecls_541_ = lean_ctor_get(v_toCold_529_, 5);
v_initHeartbeats_542_ = lean_ctor_get(v_toCold_529_, 6);
v_maxHeartbeats_543_ = lean_ctor_get(v_toCold_529_, 7);
v_quotContext_544_ = lean_ctor_get(v_toCold_529_, 8);
v_currMacroScope_545_ = lean_ctor_get(v_toCold_529_, 9);
v_cancelTk_x3f_546_ = lean_ctor_get(v_toCold_529_, 10);
v_inheritedTraceOptions_547_ = lean_ctor_get(v_toCold_529_, 11);
v_isSharedCheck_588_ = !lean_is_exclusive(v_toCold_529_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; 
v_unused_589_ = lean_ctor_get(v_toCold_529_, 3);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_toCold_529_, 2);
lean_dec(v_unused_590_);
v___x_549_ = v_toCold_529_;
v_isShared_550_ = v_isSharedCheck_588_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_inheritedTraceOptions_547_);
lean_inc(v_cancelTk_x3f_546_);
lean_inc(v_currMacroScope_545_);
lean_inc(v_quotContext_544_);
lean_inc(v_maxHeartbeats_543_);
lean_inc(v_initHeartbeats_542_);
lean_inc(v_openDecls_541_);
lean_inc(v_currNamespace_540_);
lean_inc(v_fileMap_539_);
lean_inc(v_fileName_538_);
lean_dec(v_toCold_529_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_588_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_525_, v___y_524_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 3, v___x_551_);
lean_ctor_set(v___x_549_, 2, v___y_525_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_fileName_538_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_fileMap_539_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v___y_525_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_currNamespace_540_);
lean_ctor_set(v_reuseFailAlloc_587_, 5, v_openDecls_541_);
lean_ctor_set(v_reuseFailAlloc_587_, 6, v_initHeartbeats_542_);
lean_ctor_set(v_reuseFailAlloc_587_, 7, v_maxHeartbeats_543_);
lean_ctor_set(v_reuseFailAlloc_587_, 8, v_quotContext_544_);
lean_ctor_set(v_reuseFailAlloc_587_, 9, v_currMacroScope_545_);
lean_ctor_set(v_reuseFailAlloc_587_, 10, v_cancelTk_x3f_546_);
lean_ctor_set(v_reuseFailAlloc_587_, 11, v_inheritedTraceOptions_547_);
v___x_553_ = v_reuseFailAlloc_587_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_553_);
v___x_555_ = v___x_536_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_currRecDepth_530_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_ref_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_586_, sizeof(void*)*3 + 2, v_suppressElabErrors_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_586_, sizeof(void*)*3 + 3, v_checkDeprecated_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_586_, sizeof(void*)*3 + 4, v_isRecordingDeps_534_);
v___x_555_ = v_reuseFailAlloc_586_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
lean_ctor_set_uint16(v___x_555_, sizeof(void*)*3, v___y_526_);
v___x_556_ = l_Lean_addAndCompile(v___x_470_, v___x_521_, v___x_522_, v___x_555_, v___y_528_);
lean_dec_ref(v___x_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_dec_ref_known(v___x_556_, 1);
goto v___jp_449_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_a_445_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_585_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_585_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_585_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v___x_561_; 
v___x_561_ = l_Lean_Exception_isInterrupt(v_a_557_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; 
lean_inc(v_a_557_);
v___x_562_ = l_Lean_Exception_isRuntime(v_a_557_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_559_);
v___x_563_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_564_ = l_Lean_MessageData_ofName(v_tacticName_435_);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__12, &l_Lean_Meta_nativeEqTrue___lam__0___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__12);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_Exception_toMessageData(v_a_557_);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_569_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v___y_441_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v___x_580_; 
lean_dec_ref(v___y_441_);
lean_dec(v_tacticName_435_);
if (v_isShared_560_ == 0)
{
v___x_580_ = v___x_559_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_557_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_object* v___x_583_; 
lean_dec_ref(v___y_441_);
lean_dec(v_tacticName_435_);
if (v_isShared_560_ == 0)
{
v___x_583_ = v___x_559_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_557_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
}
}
}
v___jp_592_:
{
lean_object* v___x_599_; lean_object* v_env_600_; lean_object* v_nextMacroScope_601_; lean_object* v_ngen_602_; lean_object* v_auxDeclNGen_603_; lean_object* v_traceState_604_; lean_object* v_recordedDeps_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_617_; 
v___x_599_ = lean_st_ref_take(v___y_597_);
v_env_600_ = lean_ctor_get(v___x_599_, 0);
v_nextMacroScope_601_ = lean_ctor_get(v___x_599_, 1);
v_ngen_602_ = lean_ctor_get(v___x_599_, 2);
v_auxDeclNGen_603_ = lean_ctor_get(v___x_599_, 3);
v_traceState_604_ = lean_ctor_get(v___x_599_, 4);
v_recordedDeps_605_ = lean_ctor_get(v___x_599_, 6);
v_messages_606_ = lean_ctor_get(v___x_599_, 7);
v_infoState_607_ = lean_ctor_get(v___x_599_, 8);
v_snapshotTasks_608_ = lean_ctor_get(v___x_599_, 9);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_599_, 5);
lean_dec(v_unused_618_);
v___x_610_ = v___x_599_;
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_recordedDeps_605_);
lean_inc(v_traceState_604_);
lean_inc(v_auxDeclNGen_603_);
lean_inc(v_ngen_602_);
lean_inc(v_nextMacroScope_601_);
lean_inc(v_env_600_);
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = l_Lean_Kernel_enableDiag(v_env_600_, v___y_593_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 5, v___x_485_);
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_nextMacroScope_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_ngen_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_auxDeclNGen_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_traceState_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_recordedDeps_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 9, v_snapshotTasks_608_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_st_ref_put(v___y_597_, v___x_614_);
v___y_524_ = v___y_595_;
v___y_525_ = v___y_596_;
v___y_526_ = v___y_598_;
v___y_527_ = v___y_594_;
v___y_528_ = v___y_597_;
goto v___jp_523_;
}
}
}
v___jp_619_:
{
uint16_t v___x_624_; lean_object* v___x_625_; lean_object* v_env_626_; uint8_t v___x_627_; uint16_t v___x_628_; uint16_t v___x_629_; uint16_t v___x_630_; uint8_t v___x_631_; 
v___x_624_ = l_Lean_OptionFlags_ofOptions(v___y_623_);
v___x_625_ = lean_st_ref_get(v___y_622_);
v_env_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc_ref(v_env_626_);
lean_dec(v___x_625_);
v___x_627_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_626_);
lean_dec_ref(v_env_626_);
v___x_628_ = 512;
v___x_629_ = lean_uint16_land(v___x_624_, v___x_628_);
v___x_630_ = 0;
v___x_631_ = lean_uint16_dec_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
if (v___x_627_ == 0)
{
v___y_593_ = v___x_521_;
v___y_594_ = v___y_620_;
v___y_595_ = v___y_621_;
v___y_596_ = v___y_623_;
v___y_597_ = v___y_622_;
v___y_598_ = v___x_624_;
goto v___jp_592_;
}
else
{
v___y_524_ = v___y_621_;
v___y_525_ = v___y_623_;
v___y_526_ = v___x_624_;
v___y_527_ = v___y_620_;
v___y_528_ = v___y_622_;
goto v___jp_523_;
}
}
else
{
if (v___x_627_ == 0)
{
v___y_524_ = v___y_621_;
v___y_525_ = v___y_623_;
v___y_526_ = v___x_624_;
v___y_527_ = v___y_620_;
v___y_528_ = v___y_622_;
goto v___jp_523_;
}
else
{
v___y_593_ = v___x_522_;
v___y_594_ = v___y_620_;
v___y_595_ = v___y_621_;
v___y_596_ = v___y_623_;
v___y_597_ = v___y_622_;
v___y_598_ = v___x_624_;
goto v___jp_592_;
}
}
}
v___jp_632_:
{
lean_object* v_toCold_638_; lean_object* v_currRecDepth_639_; lean_object* v_ref_640_; uint8_t v_suppressElabErrors_641_; uint8_t v_checkDeprecated_642_; uint8_t v_isRecordingDeps_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_673_; 
v_toCold_638_ = lean_ctor_get(v___y_636_, 0);
v_currRecDepth_639_ = lean_ctor_get(v___y_636_, 1);
v_ref_640_ = lean_ctor_get(v___y_636_, 2);
v_suppressElabErrors_641_ = lean_ctor_get_uint8(v___y_636_, sizeof(void*)*3 + 2);
v_checkDeprecated_642_ = lean_ctor_get_uint8(v___y_636_, sizeof(void*)*3 + 3);
v_isRecordingDeps_643_ = lean_ctor_get_uint8(v___y_636_, sizeof(void*)*3 + 4);
v_isSharedCheck_673_ = !lean_is_exclusive(v___y_636_);
if (v_isSharedCheck_673_ == 0)
{
v___x_645_ = v___y_636_;
v_isShared_646_ = v_isSharedCheck_673_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_ref_640_);
lean_inc(v_currRecDepth_639_);
lean_inc(v_toCold_638_);
lean_dec(v___y_636_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_673_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_fileName_647_; lean_object* v_fileMap_648_; lean_object* v_currNamespace_649_; lean_object* v_openDecls_650_; lean_object* v_initHeartbeats_651_; lean_object* v_maxHeartbeats_652_; lean_object* v_quotContext_653_; lean_object* v_currMacroScope_654_; lean_object* v_cancelTk_x3f_655_; lean_object* v_inheritedTraceOptions_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_670_; 
v_fileName_647_ = lean_ctor_get(v_toCold_638_, 0);
v_fileMap_648_ = lean_ctor_get(v_toCold_638_, 1);
v_currNamespace_649_ = lean_ctor_get(v_toCold_638_, 4);
v_openDecls_650_ = lean_ctor_get(v_toCold_638_, 5);
v_initHeartbeats_651_ = lean_ctor_get(v_toCold_638_, 6);
v_maxHeartbeats_652_ = lean_ctor_get(v_toCold_638_, 7);
v_quotContext_653_ = lean_ctor_get(v_toCold_638_, 8);
v_currMacroScope_654_ = lean_ctor_get(v_toCold_638_, 9);
v_cancelTk_x3f_655_ = lean_ctor_get(v_toCold_638_, 10);
v_inheritedTraceOptions_656_ = lean_ctor_get(v_toCold_638_, 11);
v_isSharedCheck_670_ = !lean_is_exclusive(v_toCold_638_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_671_ = lean_ctor_get(v_toCold_638_, 3);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_toCold_638_, 2);
lean_dec(v_unused_672_);
v___x_658_ = v_toCold_638_;
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
lean_dec(v_toCold_638_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_670_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_633_, v___y_635_);
lean_inc_ref(v___y_633_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v___x_660_);
lean_ctor_set(v___x_658_, 2, v___y_633_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fileName_647_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_fileMap_648_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v___y_633_);
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
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_currRecDepth_639_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_ref_640_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 2, v_suppressElabErrors_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 3, v_checkDeprecated_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*3 + 4, v_isRecordingDeps_643_);
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
v___x_666_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_633_, v___x_665_, v___x_521_);
v___y_620_ = v___x_664_;
v___y_621_ = v___y_635_;
v___y_622_ = v___y_637_;
v___y_623_ = v___x_666_;
goto v___jp_619_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_633_);
v___y_620_ = v___x_664_;
v___y_621_ = v___y_635_;
v___y_622_ = v___y_637_;
v___y_623_ = v___x_667_;
goto v___jp_619_;
}
}
}
}
}
}
v___jp_674_:
{
lean_object* v___x_681_; lean_object* v_env_682_; lean_object* v_nextMacroScope_683_; lean_object* v_ngen_684_; lean_object* v_auxDeclNGen_685_; lean_object* v_traceState_686_; lean_object* v_recordedDeps_687_; lean_object* v_messages_688_; lean_object* v_infoState_689_; lean_object* v_snapshotTasks_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_699_; 
v___x_681_ = lean_st_ref_take(v___y_680_);
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
v___x_694_ = l_Lean_Kernel_enableDiag(v_env_682_, v___y_675_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 5, v___x_485_);
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
lean_ctor_set(v_reuseFailAlloc_698_, 5, v___x_485_);
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
v___x_697_ = lean_st_ref_put(v___y_680_, v___x_696_);
v___y_633_ = v___y_676_;
v___y_634_ = v___y_678_;
v___y_635_ = v___y_677_;
v___y_636_ = v___y_679_;
v___y_637_ = v___y_680_;
goto v___jp_632_;
}
}
}
v___jp_701_:
{
uint16_t v___x_706_; lean_object* v___x_707_; lean_object* v_env_708_; uint8_t v___x_709_; uint16_t v___x_710_; uint16_t v___x_711_; uint16_t v___x_712_; uint8_t v___x_713_; 
v___x_706_ = l_Lean_OptionFlags_ofOptions(v___y_705_);
v___x_707_ = lean_st_ref_get(v___y_704_);
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
v___y_675_ = v___x_521_;
v___y_676_ = v___y_705_;
v___y_677_ = v___y_702_;
v___y_678_ = v___x_706_;
v___y_679_ = v___y_703_;
v___y_680_ = v___y_704_;
goto v___jp_674_;
}
else
{
v___y_633_ = v___y_705_;
v___y_634_ = v___x_706_;
v___y_635_ = v___y_702_;
v___y_636_ = v___y_703_;
v___y_637_ = v___y_704_;
goto v___jp_632_;
}
}
else
{
if (v___x_709_ == 0)
{
v___y_633_ = v___y_705_;
v___y_634_ = v___x_706_;
v___y_635_ = v___y_702_;
v___y_636_ = v___y_703_;
v___y_637_ = v___y_704_;
goto v___jp_632_;
}
else
{
v___y_675_ = v___x_522_;
v___y_676_ = v___y_705_;
v___y_677_ = v___y_702_;
v___y_678_ = v___x_706_;
v___y_679_ = v___y_703_;
v___y_680_ = v___y_704_;
goto v___jp_674_;
}
}
}
v___jp_714_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_733_ = l_Lean_maxRecDepth;
v___x_734_ = l_Lean_Option_get___at___00Lean_Meta_nativeEqTrue_spec__5(v___y_716_, v___x_733_);
lean_inc_ref(v___y_716_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 11, v_inheritedTraceOptions_726_);
lean_ctor_set(v___x_519_, 10, v_cancelTk_x3f_725_);
lean_ctor_set(v___x_519_, 9, v_currMacroScope_724_);
lean_ctor_set(v___x_519_, 8, v_quotContext_723_);
lean_ctor_set(v___x_519_, 7, v_maxHeartbeats_722_);
lean_ctor_set(v___x_519_, 6, v_initHeartbeats_721_);
lean_ctor_set(v___x_519_, 5, v_openDecls_720_);
lean_ctor_set(v___x_519_, 4, v_currNamespace_719_);
lean_ctor_set(v___x_519_, 3, v___x_734_);
lean_ctor_set(v___x_519_, 2, v___y_716_);
lean_ctor_set(v___x_519_, 1, v_fileMap_718_);
lean_ctor_set(v___x_519_, 0, v_fileName_717_);
v___x_736_ = v___x_519_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_fileName_717_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_fileMap_718_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v___y_716_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_currNamespace_719_);
lean_ctor_set(v_reuseFailAlloc_741_, 5, v_openDecls_720_);
lean_ctor_set(v_reuseFailAlloc_741_, 6, v_initHeartbeats_721_);
lean_ctor_set(v_reuseFailAlloc_741_, 7, v_maxHeartbeats_722_);
lean_ctor_set(v_reuseFailAlloc_741_, 8, v_quotContext_723_);
lean_ctor_set(v_reuseFailAlloc_741_, 9, v_currMacroScope_724_);
lean_ctor_set(v_reuseFailAlloc_741_, 10, v_cancelTk_x3f_725_);
lean_ctor_set(v_reuseFailAlloc_741_, 11, v_inheritedTraceOptions_726_);
v___x_736_ = v_reuseFailAlloc_741_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v_currRecDepth_727_);
lean_ctor_set(v___x_737_, 2, v_ref_728_);
lean_ctor_set_uint16(v___x_737_, sizeof(void*)*3, v___y_715_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3 + 2, v_suppressElabErrors_729_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3 + 3, v_checkDeprecated_730_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3 + 4, v_isRecordingDeps_731_);
if (v_isRecordingDeps_731_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_739_ = l_Lean_Option_set___at___00Lean_Meta_nativeEqTrue_spec__6(v___y_716_, v___x_738_, v_isRecordingDeps_731_);
v___y_702_ = v___x_733_;
v___y_703_ = v___x_737_;
v___y_704_ = v___y_732_;
v___y_705_ = v___x_739_;
goto v___jp_701_;
}
else
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_716_);
v___y_702_ = v___x_733_;
v___y_703_ = v___x_737_;
v___y_704_ = v___y_732_;
v___y_705_ = v___x_740_;
goto v___jp_701_;
}
}
}
v___jp_742_:
{
lean_object* v___x_746_; lean_object* v_env_747_; lean_object* v_nextMacroScope_748_; lean_object* v_ngen_749_; lean_object* v_auxDeclNGen_750_; lean_object* v_traceState_751_; lean_object* v_recordedDeps_752_; lean_object* v_messages_753_; lean_object* v_infoState_754_; lean_object* v_snapshotTasks_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_764_; 
v___x_746_ = lean_st_ref_take(v___y_442_);
v_env_747_ = lean_ctor_get(v___x_746_, 0);
v_nextMacroScope_748_ = lean_ctor_get(v___x_746_, 1);
v_ngen_749_ = lean_ctor_get(v___x_746_, 2);
v_auxDeclNGen_750_ = lean_ctor_get(v___x_746_, 3);
v_traceState_751_ = lean_ctor_get(v___x_746_, 4);
v_recordedDeps_752_ = lean_ctor_get(v___x_746_, 6);
v_messages_753_ = lean_ctor_get(v___x_746_, 7);
v_infoState_754_ = lean_ctor_get(v___x_746_, 8);
v_snapshotTasks_755_ = lean_ctor_get(v___x_746_, 9);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v___x_746_, 5);
lean_dec(v_unused_765_);
v___x_757_ = v___x_746_;
v_isShared_758_ = v_isSharedCheck_764_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snapshotTasks_755_);
lean_inc(v_infoState_754_);
lean_inc(v_messages_753_);
lean_inc(v_recordedDeps_752_);
lean_inc(v_traceState_751_);
lean_inc(v_auxDeclNGen_750_);
lean_inc(v_ngen_749_);
lean_inc(v_nextMacroScope_748_);
lean_inc(v_env_747_);
lean_dec(v___x_746_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_764_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = l_Lean_Kernel_enableDiag(v_env_747_, v___y_745_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 5, v___x_485_);
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_nextMacroScope_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_ngen_749_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_auxDeclNGen_750_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_traceState_751_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_763_, 6, v_recordedDeps_752_);
lean_ctor_set(v_reuseFailAlloc_763_, 7, v_messages_753_);
lean_ctor_set(v_reuseFailAlloc_763_, 8, v_infoState_754_);
lean_ctor_set(v_reuseFailAlloc_763_, 9, v_snapshotTasks_755_);
v___x_761_ = v_reuseFailAlloc_763_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; 
v___x_762_ = lean_st_ref_put(v___y_442_, v___x_761_);
lean_inc(v_ref_503_);
lean_inc(v_currRecDepth_502_);
v___y_715_ = v___y_743_;
v___y_716_ = v___y_744_;
v_fileName_717_ = v_fileName_507_;
v_fileMap_718_ = v_fileMap_508_;
v_currNamespace_719_ = v_currNamespace_510_;
v_openDecls_720_ = v_openDecls_511_;
v_initHeartbeats_721_ = v_initHeartbeats_512_;
v_maxHeartbeats_722_ = v_maxHeartbeats_513_;
v_quotContext_723_ = v_quotContext_514_;
v_currMacroScope_724_ = v_currMacroScope_515_;
v_cancelTk_x3f_725_ = v_cancelTk_x3f_516_;
v_inheritedTraceOptions_726_ = v_inheritedTraceOptions_517_;
v_currRecDepth_727_ = v_currRecDepth_502_;
v_ref_728_ = v_ref_503_;
v_suppressElabErrors_729_ = v_suppressElabErrors_504_;
v_checkDeprecated_730_ = v_checkDeprecated_505_;
v_isRecordingDeps_731_ = v_isRecordingDeps_506_;
v___y_732_ = v___y_442_;
goto v___jp_714_;
}
}
}
v___jp_766_:
{
uint16_t v___x_768_; lean_object* v___x_769_; lean_object* v_env_770_; uint8_t v___x_771_; uint16_t v___x_772_; uint16_t v___x_773_; uint16_t v___x_774_; uint8_t v___x_775_; 
v___x_768_ = l_Lean_OptionFlags_ofOptions(v___y_767_);
v___x_769_ = lean_st_ref_get(v___y_442_);
v_env_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_ref(v_env_770_);
lean_dec(v___x_769_);
v___x_771_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_770_);
lean_dec_ref(v_env_770_);
v___x_772_ = 512;
v___x_773_ = lean_uint16_land(v___x_768_, v___x_772_);
v___x_774_ = 0;
v___x_775_ = lean_uint16_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
if (v___x_771_ == 0)
{
v___y_743_ = v___x_768_;
v___y_744_ = v___y_767_;
v___y_745_ = v___x_521_;
goto v___jp_742_;
}
else
{
lean_inc(v_ref_503_);
lean_inc(v_currRecDepth_502_);
v___y_715_ = v___x_768_;
v___y_716_ = v___y_767_;
v_fileName_717_ = v_fileName_507_;
v_fileMap_718_ = v_fileMap_508_;
v_currNamespace_719_ = v_currNamespace_510_;
v_openDecls_720_ = v_openDecls_511_;
v_initHeartbeats_721_ = v_initHeartbeats_512_;
v_maxHeartbeats_722_ = v_maxHeartbeats_513_;
v_quotContext_723_ = v_quotContext_514_;
v_currMacroScope_724_ = v_currMacroScope_515_;
v_cancelTk_x3f_725_ = v_cancelTk_x3f_516_;
v_inheritedTraceOptions_726_ = v_inheritedTraceOptions_517_;
v_currRecDepth_727_ = v_currRecDepth_502_;
v_ref_728_ = v_ref_503_;
v_suppressElabErrors_729_ = v_suppressElabErrors_504_;
v_checkDeprecated_730_ = v_checkDeprecated_505_;
v_isRecordingDeps_731_ = v_isRecordingDeps_506_;
v___y_732_ = v___y_442_;
goto v___jp_714_;
}
}
else
{
if (v___x_771_ == 0)
{
lean_inc(v_ref_503_);
lean_inc(v_currRecDepth_502_);
v___y_715_ = v___x_768_;
v___y_716_ = v___y_767_;
v_fileName_717_ = v_fileName_507_;
v_fileMap_718_ = v_fileMap_508_;
v_currNamespace_719_ = v_currNamespace_510_;
v_openDecls_720_ = v_openDecls_511_;
v_initHeartbeats_721_ = v_initHeartbeats_512_;
v_maxHeartbeats_722_ = v_maxHeartbeats_513_;
v_quotContext_723_ = v_quotContext_514_;
v_currMacroScope_724_ = v_currMacroScope_515_;
v_cancelTk_x3f_725_ = v_cancelTk_x3f_516_;
v_inheritedTraceOptions_726_ = v_inheritedTraceOptions_517_;
v_currRecDepth_727_ = v_currRecDepth_502_;
v_ref_728_ = v_ref_503_;
v_suppressElabErrors_729_ = v_suppressElabErrors_504_;
v_checkDeprecated_730_ = v_checkDeprecated_505_;
v_isRecordingDeps_731_ = v_isRecordingDeps_506_;
v___y_732_ = v___y_442_;
goto v___jp_714_;
}
else
{
v___y_743_ = v___x_768_;
v___y_744_ = v___y_767_;
v___y_745_ = v___x_522_;
goto v___jp_742_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___lam__0___boxed(lean_object* v___x_789_, lean_object* v_tacticName_790_, lean_object* v___x_791_, lean_object* v___x_792_, lean_object* v_a_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_nativeEqTrue___lam__0(v___x_789_, v_tacticName_790_, v___x_791_, v___x_792_, v_a_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___redArg(lean_object* v_declName_800_, lean_object* v_declRanges_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = l_Lean_Name_isAnonymous(v_declName_800_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v_env_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_806_ = lean_st_ref_get(v___y_803_);
v_env_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref(v_env_807_);
lean_dec(v___x_806_);
v___x_808_ = l_Lean_declRangeExt;
v___x_809_ = lean_box(1);
lean_inc(v_declName_800_);
v___x_810_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_808_, v_env_807_, v_declName_800_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v_env_812_; lean_object* v_nextMacroScope_813_; lean_object* v_ngen_814_; lean_object* v_auxDeclNGen_815_; lean_object* v_traceState_816_; lean_object* v_recordedDeps_817_; lean_object* v_messages_818_; lean_object* v_infoState_819_; lean_object* v_snapshotTasks_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_847_; 
v___x_811_ = lean_st_ref_take(v___y_803_);
v_env_812_ = lean_ctor_get(v___x_811_, 0);
v_nextMacroScope_813_ = lean_ctor_get(v___x_811_, 1);
v_ngen_814_ = lean_ctor_get(v___x_811_, 2);
v_auxDeclNGen_815_ = lean_ctor_get(v___x_811_, 3);
v_traceState_816_ = lean_ctor_get(v___x_811_, 4);
v_recordedDeps_817_ = lean_ctor_get(v___x_811_, 6);
v_messages_818_ = lean_ctor_get(v___x_811_, 7);
v_infoState_819_ = lean_ctor_get(v___x_811_, 8);
v_snapshotTasks_820_ = lean_ctor_get(v___x_811_, 9);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v___x_811_, 5);
lean_dec(v_unused_848_);
v___x_822_ = v___x_811_;
v_isShared_823_ = v_isSharedCheck_847_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snapshotTasks_820_);
lean_inc(v_infoState_819_);
lean_inc(v_messages_818_);
lean_inc(v_recordedDeps_817_);
lean_inc(v_traceState_816_);
lean_inc(v_auxDeclNGen_815_);
lean_inc(v_ngen_814_);
lean_inc(v_nextMacroScope_813_);
lean_inc(v_env_812_);
lean_dec(v___x_811_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_847_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_824_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_808_, v_env_812_, v_declName_800_, v_declRanges_801_, v___x_810_);
v___x_825_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 5, v___x_825_);
lean_ctor_set(v___x_822_, 0, v___x_824_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_nextMacroScope_813_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_ngen_814_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_auxDeclNGen_815_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_traceState_816_);
lean_ctor_set(v_reuseFailAlloc_846_, 5, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_846_, 6, v_recordedDeps_817_);
lean_ctor_set(v_reuseFailAlloc_846_, 7, v_messages_818_);
lean_ctor_set(v_reuseFailAlloc_846_, 8, v_infoState_819_);
lean_ctor_set(v_reuseFailAlloc_846_, 9, v_snapshotTasks_820_);
v___x_827_ = v_reuseFailAlloc_846_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_mctx_830_; lean_object* v_zetaDeltaFVarIds_831_; lean_object* v_postponed_832_; lean_object* v_diag_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_844_; 
v___x_828_ = lean_st_ref_put(v___y_803_, v___x_827_);
v___x_829_ = lean_st_ref_take(v___y_802_);
v_mctx_830_ = lean_ctor_get(v___x_829_, 0);
v_zetaDeltaFVarIds_831_ = lean_ctor_get(v___x_829_, 2);
v_postponed_832_ = lean_ctor_get(v___x_829_, 3);
v_diag_833_ = lean_ctor_get(v___x_829_, 4);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v___x_829_, 1);
lean_dec(v_unused_845_);
v___x_835_ = v___x_829_;
v_isShared_836_ = v_isSharedCheck_844_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_diag_833_);
lean_inc(v_postponed_832_);
lean_inc(v_zetaDeltaFVarIds_831_);
lean_inc(v_mctx_830_);
lean_dec(v___x_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_844_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = lean_box(0);
v___x_838_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_838_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_mctx_830_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_zetaDeltaFVarIds_831_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_postponed_832_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_diag_833_);
v___x_840_ = v_reuseFailAlloc_843_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_st_ref_put(v___y_802_, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_837_);
return v___x_842_;
}
}
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec_ref(v_declRanges_801_);
lean_dec(v_declName_800_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref(v_declRanges_801_);
lean_dec(v_declName_800_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___redArg___boxed(lean_object* v_declName_853_, lean_object* v_declRanges_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___redArg(v_declName_853_, v_declRanges_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec(v___y_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(lean_object* v_stx_859_, lean_object* v___y_860_){
_start:
{
uint8_t v___x_862_; lean_object* v___x_863_; 
v___x_862_ = 0;
v___x_863_ = l_Lean_Syntax_getRange_x3f(v_stx_859_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 1)
{
lean_object* v_toCold_864_; lean_object* v_val_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_877_; 
v_toCold_864_ = lean_ctor_get(v___y_860_, 0);
v_val_865_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_877_ == 0)
{
v___x_867_ = v___x_863_;
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_val_865_);
lean_dec(v___x_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fileMap_869_; lean_object* v_start_870_; lean_object* v_stop_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v_fileMap_869_ = lean_ctor_get(v_toCold_864_, 1);
v_start_870_ = lean_ctor_get(v_val_865_, 0);
lean_inc(v_start_870_);
v_stop_871_ = lean_ctor_get(v_val_865_, 1);
lean_inc(v_stop_871_);
lean_dec(v_val_865_);
lean_inc_ref(v_fileMap_869_);
v___x_872_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_869_, v_start_870_, v_stop_871_);
lean_dec(v_stop_871_);
lean_dec(v_start_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_872_);
v___x_874_ = v___x_867_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v___x_863_);
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg___boxed(lean_object* v_stx_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_stx_880_, v___y_881_);
lean_dec_ref(v___y_881_);
lean_dec(v_stx_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(lean_object* v_declName_884_, lean_object* v_rangeStx_885_, lean_object* v_selectionRangeStx_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_909_; 
v___x_892_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_rangeStx_885_, v___y_889_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_909_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_909_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_909_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
if (lean_obj_tag(v_a_893_) == 1)
{
lean_object* v_val_897_; lean_object* v_a_899_; lean_object* v___x_902_; lean_object* v_a_903_; 
lean_del_object(v___x_895_);
v_val_897_ = lean_ctor_get(v_a_893_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v_a_893_, 1);
v___x_902_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_selectionRangeStx_886_, v___y_889_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
if (lean_obj_tag(v_a_903_) == 0)
{
lean_inc(v_val_897_);
v_a_899_ = v_val_897_;
goto v___jp_898_;
}
else
{
lean_object* v_val_904_; 
v_val_904_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v_a_903_, 1);
v_a_899_ = v_val_904_;
goto v___jp_898_;
}
v___jp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_val_897_);
lean_ctor_set(v___x_900_, 1, v_a_899_);
v___x_901_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___redArg(v_declName_884_, v___x_900_, v___y_888_, v___y_890_);
return v___x_901_;
}
}
else
{
lean_object* v___x_905_; lean_object* v___x_907_; 
lean_dec(v_a_893_);
lean_dec(v_declName_884_);
v___x_905_ = lean_box(0);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_905_);
v___x_907_ = v___x_895_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9___boxed(lean_object* v_declName_910_, lean_object* v_rangeStx_911_, lean_object* v_selectionRangeStx_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_declName_910_, v_rangeStx_911_, v_selectionRangeStx_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v_selectionRangeStx_912_);
lean_dec(v_rangeStx_911_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
if (lean_obj_tag(v_a_919_) == 0)
{
lean_object* v___x_921_; 
v___x_921_ = l_List_reverse___redArg(v_a_920_);
return v___x_921_;
}
else
{
lean_object* v_head_922_; lean_object* v_tail_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_932_; 
v_head_922_ = lean_ctor_get(v_a_919_, 0);
v_tail_923_ = lean_ctor_get(v_a_919_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_932_ == 0)
{
v___x_925_ = v_a_919_;
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_tail_923_);
lean_inc(v_head_922_);
lean_dec(v_a_919_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = l_Lean_mkLevelParam(v_head_922_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v_a_920_);
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_a_920_);
v___x_929_ = v_reuseFailAlloc_931_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v_a_919_ = v_tail_923_;
v_a_920_ = v___x_929_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg(lean_object* v_env_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; lean_object* v_nextMacroScope_938_; lean_object* v_ngen_939_; lean_object* v_auxDeclNGen_940_; lean_object* v_traceState_941_; lean_object* v_recordedDeps_942_; lean_object* v_messages_943_; lean_object* v_infoState_944_; lean_object* v_snapshotTasks_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_971_; 
v___x_937_ = lean_st_ref_take(v___y_935_);
v_nextMacroScope_938_ = lean_ctor_get(v___x_937_, 1);
v_ngen_939_ = lean_ctor_get(v___x_937_, 2);
v_auxDeclNGen_940_ = lean_ctor_get(v___x_937_, 3);
v_traceState_941_ = lean_ctor_get(v___x_937_, 4);
v_recordedDeps_942_ = lean_ctor_get(v___x_937_, 6);
v_messages_943_ = lean_ctor_get(v___x_937_, 7);
v_infoState_944_ = lean_ctor_get(v___x_937_, 8);
v_snapshotTasks_945_ = lean_ctor_get(v___x_937_, 9);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_972_ = lean_ctor_get(v___x_937_, 5);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v___x_937_, 0);
lean_dec(v_unused_973_);
v___x_947_ = v___x_937_;
v_isShared_948_ = v_isSharedCheck_971_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snapshotTasks_945_);
lean_inc(v_infoState_944_);
lean_inc(v_messages_943_);
lean_inc(v_recordedDeps_942_);
lean_inc(v_traceState_941_);
lean_inc(v_auxDeclNGen_940_);
lean_inc(v_ngen_939_);
lean_inc(v_nextMacroScope_938_);
lean_dec(v___x_937_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_971_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__8, &l_Lean_Meta_nativeEqTrue___lam__0___closed__8_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__8);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 5, v___x_949_);
lean_ctor_set(v___x_947_, 0, v_env_933_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_env_933_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_nextMacroScope_938_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_ngen_939_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_auxDeclNGen_940_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_traceState_941_);
lean_ctor_set(v_reuseFailAlloc_970_, 5, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_970_, 6, v_recordedDeps_942_);
lean_ctor_set(v_reuseFailAlloc_970_, 7, v_messages_943_);
lean_ctor_set(v_reuseFailAlloc_970_, 8, v_infoState_944_);
lean_ctor_set(v_reuseFailAlloc_970_, 9, v_snapshotTasks_945_);
v___x_951_ = v_reuseFailAlloc_970_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_mctx_954_; lean_object* v_zetaDeltaFVarIds_955_; lean_object* v_postponed_956_; lean_object* v_diag_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_968_; 
v___x_952_ = lean_st_ref_put(v___y_935_, v___x_951_);
v___x_953_ = lean_st_ref_take(v___y_934_);
v_mctx_954_ = lean_ctor_get(v___x_953_, 0);
v_zetaDeltaFVarIds_955_ = lean_ctor_get(v___x_953_, 2);
v_postponed_956_ = lean_ctor_get(v___x_953_, 3);
v_diag_957_ = lean_ctor_get(v___x_953_, 4);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v___x_953_, 1);
lean_dec(v_unused_969_);
v___x_959_ = v___x_953_;
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_diag_957_);
lean_inc(v_postponed_956_);
lean_inc(v_zetaDeltaFVarIds_955_);
lean_inc(v_mctx_954_);
lean_dec(v___x_953_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_961_ = lean_box(0);
v___x_962_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__10, &l_Lean_Meta_nativeEqTrue___lam__0___closed__10_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__10);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v___x_962_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_mctx_954_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_zetaDeltaFVarIds_955_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_postponed_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_diag_957_);
v___x_964_ = v_reuseFailAlloc_967_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_st_ref_put(v___y_934_, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_961_);
return v___x_966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg___boxed(lean_object* v_env_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg(v_env_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(lean_object* v_env_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v_env_987_; lean_object* v_a_989_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_986_ = lean_st_ref_get(v___y_984_);
v_env_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_986_);
v___x_999_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg(v_env_979_, v___y_982_, v___y_984_);
lean_dec_ref(v___x_999_);
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
v___x_1000_ = lean_apply_5(v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, lean_box(0));
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg(v_env_987_, v___y_982_, v___y_984_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1010_);
v___x_1004_ = v___x_1002_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v___x_1002_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_a_1001_);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1001_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1000_, 1);
v_a_989_ = v_a_1011_;
goto v___jp_988_;
}
v___jp_988_:
{
lean_object* v___x_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
v___x_990_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg(v_env_987_, v___y_982_, v___y_984_);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v___x_990_, 0);
lean_dec(v_unused_998_);
v___x_992_ = v___x_990_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_dec(v___x_990_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 1);
lean_ctor_set(v___x_992_, 0, v_a_989_);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_989_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg___boxed(lean_object* v_env_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_1012_, v_x_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1019_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__0(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_unsigned_to_nat(16u);
v___x_1022_ = lean_mk_array(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__1(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__0, &l_Lean_Meta_nativeEqTrue___closed__0_once, _init_l_Lean_Meta_nativeEqTrue___closed__0);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1023_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__2));
v___x_1029_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__1, &l_Lean_Meta_nativeEqTrue___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___closed__1);
v___x_1030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
lean_ctor_set(v___x_1030_, 2, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__12(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = l_Lean_Level_ofNat(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__13(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__12, &l_Lean_Meta_nativeEqTrue___closed__12_once, _init_l_Lean_Meta_nativeEqTrue___closed__12);
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1045_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__14(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__13, &l_Lean_Meta_nativeEqTrue___closed__13_once, _init_l_Lean_Meta_nativeEqTrue___closed__13);
v___x_1049_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__11));
v___x_1050_ = l_Lean_mkConst(v___x_1049_, v___x_1048_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__15(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___lam__0___closed__5));
v___x_1053_ = l_Lean_mkConst(v___x_1052_, v___x_1051_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__18(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__17));
v___x_1060_ = l_Lean_mkConst(v___x_1059_, v___x_1058_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__20(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__19));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Meta_nativeEqTrue___closed__22(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__21));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue(lean_object* v_tacticName_1067_, lean_object* v_e_1068_, lean_object* v_axiomDeclRange_x3f_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v___x_1190_; 
v___x_1083_ = l_Lean_instantiateMVars___at___00Lean_Meta_nativeEqTrue_spec__0___redArg(v_e_1068_, v_a_1071_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
v___x_1190_ = l_Lean_Expr_hasFVar(v_a_1084_);
if (v___x_1190_ == 0)
{
v___y_1169_ = v_a_1070_;
v___y_1170_ = v_a_1071_;
v___y_1171_ = v_a_1072_;
v___y_1172_ = v_a_1073_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v___x_1191_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1192_ = l_Lean_MessageData_ofName(v_tacticName_1067_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__22, &l_Lean_Meta_nativeEqTrue___closed__22_once, _init_l_Lean_Meta_nativeEqTrue___closed__22);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_indentExpr(v_a_1084_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1197_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
v___jp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = l_List_mapTR_loop___at___00Lean_Meta_nativeEqTrue_spec__8(v___y_1076_, v___x_1078_);
v___x_1080_ = l_Lean_mkConst(v___y_1077_, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
v___jp_1085_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v_params_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1165_; 
v___x_1090_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__3, &l_Lean_Meta_nativeEqTrue___closed__3_once, _init_l_Lean_Meta_nativeEqTrue___closed__3);
lean_inc(v_a_1084_);
v___x_1091_ = l_Lean_collectLevelParams(v___x_1090_, v_a_1084_);
v_params_1092_ = lean_ctor_get(v___x_1091_, 2);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; lean_object* v_unused_1167_; 
v_unused_1166_ = lean_ctor_get(v___x_1091_, 1);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v___x_1091_, 0);
lean_dec(v_unused_1167_);
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1165_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_params_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1165_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v_env_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_array_to_list(v_params_1092_);
v___x_1098_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__5));
lean_inc(v_tacticName_1067_);
v___x_1099_ = l_Lean_Name_append(v___x_1098_, v_tacticName_1067_);
v___x_1100_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__7));
lean_inc(v___x_1099_);
v___x_1101_ = l_Lean_Name_append(v___x_1099_, v___x_1100_);
lean_inc(v_a_1084_);
lean_inc(v___x_1097_);
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Meta_nativeEqTrue___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1102_, 0, v___x_1101_);
lean_closure_set(v___f_1102_, 1, v_tacticName_1067_);
lean_closure_set(v___f_1102_, 2, v___x_1097_);
lean_closure_set(v___f_1102_, 3, v___x_1096_);
lean_closure_set(v___f_1102_, 4, v_a_1084_);
v___x_1103_ = lean_st_ref_get(v___y_1089_);
v_env_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc_ref(v_env_1104_);
lean_dec(v___x_1103_);
v___x_1105_ = l_Lean_Environment_unlockAsync(v_env_1104_);
v___x_1106_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v___x_1105_, v___f_1102_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1156_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1156_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1156_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_unbox(v_a_1107_);
lean_dec(v_a_1107_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
lean_dec(v___x_1099_);
lean_dec(v___x_1097_);
lean_del_object(v___x_1094_);
lean_dec(v_a_1084_);
v___x_1112_ = lean_box(1);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1155_; 
lean_del_object(v___x_1109_);
v___x_1116_ = ((lean_object*)(l_Lean_Meta_nativeEqTrue___closed__9));
v___x_1117_ = l_Lean_Name_append(v___x_1099_, v___x_1116_);
v___x_1118_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_nativeEqTrue_spec__1___redArg(v___x_1117_, v___y_1089_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1155_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1155_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1123_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__14, &l_Lean_Meta_nativeEqTrue___closed__14_once, _init_l_Lean_Meta_nativeEqTrue___closed__14);
v___x_1124_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__15, &l_Lean_Meta_nativeEqTrue___closed__15_once, _init_l_Lean_Meta_nativeEqTrue___closed__15);
v___x_1125_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__18, &l_Lean_Meta_nativeEqTrue___closed__18_once, _init_l_Lean_Meta_nativeEqTrue___closed__18);
v___x_1126_ = l_Lean_mkApp3(v___x_1123_, v___x_1124_, v_a_1084_, v___x_1125_);
lean_inc(v___x_1097_);
lean_inc(v_a_1119_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v___x_1126_);
lean_ctor_set(v___x_1094_, 1, v___x_1097_);
lean_ctor_set(v___x_1094_, 0, v_a_1119_);
v___x_1128_ = v___x_1094_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1119_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = 0;
v___x_1130_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*1, v___x_1129_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1130_);
v___x_1132_ = v___x_1121_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_addDecl(v___x_1132_, v___x_1129_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref_known(v___x_1133_, 1);
if (lean_obj_tag(v_axiomDeclRange_x3f_1069_) == 1)
{
lean_object* v_val_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_val_1134_ = lean_ctor_get(v_axiomDeclRange_x3f_1069_, 0);
v___x_1135_ = lean_box(0);
lean_inc(v_a_1119_);
v___x_1136_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9(v_a_1119_, v_val_1134_, v___x_1135_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec_ref_known(v___x_1136_, 1);
v___y_1076_ = v___x_1097_;
v___y_1077_ = v_a_1119_;
goto v___jp_1075_;
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_a_1119_);
lean_dec(v___x_1097_);
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
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
else
{
v___y_1076_ = v___x_1097_;
v___y_1077_ = v_a_1119_;
goto v___jp_1075_;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_a_1119_);
lean_dec(v___x_1097_);
v_a_1145_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1133_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1133_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
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
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v___x_1099_);
lean_dec(v___x_1097_);
lean_del_object(v___x_1094_);
lean_dec(v_a_1084_);
v_a_1157_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1106_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1106_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
v___jp_1168_:
{
uint8_t v___x_1173_; 
v___x_1173_ = l_Lean_Expr_hasMVar(v_a_1084_);
if (v___x_1173_ == 0)
{
v___y_1086_ = v___y_1169_;
v___y_1087_ = v___y_1170_;
v___y_1088_ = v___y_1171_;
v___y_1089_ = v___y_1172_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v___x_1174_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__1, &l_Lean_Meta_nativeEqTrue___lam__0___closed__1_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__1);
v___x_1175_ = l_Lean_MessageData_ofName(v_tacticName_1067_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___closed__20, &l_Lean_Meta_nativeEqTrue___closed__20_once, _init_l_Lean_Meta_nativeEqTrue___closed__20);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_indentExpr(v_a_1084_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v___x_1180_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_nativeEqTrue___boxed(lean_object* v_tacticName_1207_, lean_object* v_e_1208_, lean_object* v_axiomDeclRange_x3f_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Meta_nativeEqTrue(v_tacticName_1207_, v_e_1208_, v_axiomDeclRange_x3f_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_axiomDeclRange_x3f_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(lean_object* v_00_u03b1_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___redArg();
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__3(v_00_u03b1_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(lean_object* v_00_u03b1_1230_, lean_object* v_constName_1231_, uint8_t v_checkMeta_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___redArg(v_constName_1231_, v_checkMeta_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_constName_1240_, lean_object* v_checkMeta_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v_checkMeta_boxed_1247_; lean_object* v_res_1248_; 
v_checkMeta_boxed_1247_ = lean_unbox(v_checkMeta_1241_);
v_res_1248_ = l_Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2(v_00_u03b1_1239_, v_constName_1240_, v_checkMeta_boxed_1247_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(lean_object* v_00_u03b1_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___redArg(v_msg_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_msg_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwError___at___00Lean_Meta_nativeEqTrue_spec__3(v_00_u03b1_1257_, v_msg_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4_spec__7(lean_object* v_00_u03b2_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4___redArg(){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4___redArg___boxed(lean_object* v___dummy_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4___redArg();
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_nativeEqTrue_spec__4(lean_object* v_00_u03b2_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_obj_once(&l_Lean_Meta_nativeEqTrue___lam__0___closed__9, &l_Lean_Meta_nativeEqTrue___lam__0___closed__9_once, _init_l_Lean_Meta_nativeEqTrue___lam__0___closed__9);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(lean_object* v_00_u03b1_1273_, lean_object* v_env_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___redArg(v_env_1274_, v_x_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_env_1283_, lean_object* v_x_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7(v_00_u03b1_1282_, v_env_1283_, v_x_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(lean_object* v_stx_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___redArg(v_stx_1291_, v___y_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15___boxed(lean_object* v_stx_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__15(v_stx_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v_stx_1298_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(lean_object* v_00_u03b1_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___redArg(v_x_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2___boxed(lean_object* v_00_u03b1_1313_, lean_object* v_x_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_nativeEqTrue_spec__2_spec__2(v_00_u03b1_1313_, v_x_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12(lean_object* v_env_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___redArg(v_env_1321_, v___y_1323_, v___y_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12___boxed(lean_object* v_env_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_nativeEqTrue_spec__7_spec__12(v_env_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16(lean_object* v_declName_1335_, lean_object* v_declRanges_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___redArg(v_declName_1335_, v_declRanges_1336_, v___y_1338_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16___boxed(lean_object* v_declName_1343_, lean_object* v_declRanges_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Meta_nativeEqTrue_spec__9_spec__16(v_declName_1343_, v_declRanges_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1350_;
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

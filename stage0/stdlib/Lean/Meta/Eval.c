// Lean compiler output
// Module: Lean.Meta.Eval
// Imports: public import Lean.AddDecl public import Lean.Meta.Check public import Lean.Util.CollectLevelParams import Lean.Compiler.Options
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
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Environment_importEnv_x3f(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "compiler env"};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_tmp"};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(156, 26, 231, 16, 169, 5, 155, 241)}};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8;
static const lean_array_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "failed to evaluate expression, it contains metavariables"};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unexpected type at evalExpr"};
static const lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_evalExpr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_evalExpr___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_evalExpr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected type at `evalExpr` "};
static const lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_evalExpr___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
lean_object* v_name_46_; lean_object* v_defValue_47_; lean_object* v_map_48_; lean_object* v___x_49_; 
v_name_46_ = lean_ctor_get(v_opt_45_, 0);
v_defValue_47_ = lean_ctor_get(v_opt_45_, 1);
v_map_48_ = lean_ctor_get(v_opts_44_, 0);
v___x_49_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_48_, v_name_46_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_inc(v_defValue_47_);
return v_defValue_47_;
}
else
{
lean_object* v_val_50_; 
v_val_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_val_50_);
lean_dec_ref_known(v___x_49_, 1);
if (lean_obj_tag(v_val_50_) == 3)
{
lean_object* v_v_51_; 
v_v_51_ = lean_ctor_get(v_val_50_, 0);
lean_inc(v_v_51_);
lean_dec_ref_known(v_val_50_, 1);
return v_v_51_;
}
else
{
lean_dec(v_val_50_);
lean_inc(v_defValue_47_);
return v_defValue_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_opts_52_, lean_object* v_opt_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v_opts_52_, v_opt_53_);
lean_dec_ref(v_opt_53_);
lean_dec_ref(v_opts_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__9(lean_object* v_msgData_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_env_62_; uint8_t v___x_63_; lean_object* v_env_64_; lean_object* v___x_65_; lean_object* v_toCold_66_; lean_object* v_mctx_67_; lean_object* v_lctx_68_; lean_object* v_options_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_61_ = lean_st_ref_get(v___y_59_);
v_env_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_env_62_);
lean_dec(v___x_61_);
v___x_63_ = 0;
v_env_64_ = l_Lean_Environment_setRecordingDeps(v_env_62_, v___x_63_);
v___x_65_ = lean_st_ref_get(v___y_57_);
v_toCold_66_ = lean_ctor_get(v___y_58_, 0);
v_mctx_67_ = lean_ctor_get(v___x_65_, 0);
lean_inc_ref(v_mctx_67_);
lean_dec(v___x_65_);
v_lctx_68_ = lean_ctor_get(v___y_56_, 2);
v_options_69_ = lean_ctor_get(v_toCold_66_, 2);
lean_inc_ref(v_options_69_);
lean_inc_ref(v_lctx_68_);
v___x_70_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_70_, 0, v_env_64_);
lean_ctor_set(v___x_70_, 1, v_mctx_67_);
lean_ctor_set(v___x_70_, 2, v_lctx_68_);
lean_ctor_set(v___x_70_, 3, v_options_69_);
v___x_71_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_msgData_55_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__9___boxed(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__9(v_msgData_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(lean_object* v_msg_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_ref_86_; lean_object* v___x_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_ref_86_ = lean_ctor_get(v___y_83_, 2);
v___x_87_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__9(v_msg_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_inc(v_ref_86_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_ref_86_);
lean_ctor_set(v___x_92_, 1, v_a_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 1);
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(lean_object* v_x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_a_110_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v_x_104_, 1);
v___x_111_ = l_Lean_stringToMessageData(v_a_110_);
v___x_112_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_111_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
return v___x_112_;
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_a_113_ = lean_ctor_get(v_x_104_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v_x_104_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v_x_104_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 0);
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg___boxed(lean_object* v_x_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v_x_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_box(0);
v___x_129_ = l_Lean_Elab_abortCommandExceptionId;
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg(){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___closed__0);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg___boxed(lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(lean_object* v_constName_136_, uint8_t v_checkMeta_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v_env_144_; uint8_t v___x_145_; 
v___x_143_ = lean_st_ref_get(v___y_141_);
v_env_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc_ref(v_env_144_);
lean_dec(v___x_143_);
lean_inc(v_constName_136_);
v___x_145_ = lean_has_compile_error(v_env_144_, v_constName_136_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v_env_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = lean_st_ref_get(v___y_141_);
v_env_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc_ref(v_env_147_);
lean_dec(v___x_146_);
v___x_148_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_140_);
v___x_149_ = l_Lean_Environment_evalConst___redArg(v_env_147_, v___x_148_, v_constName_136_, v_checkMeta_137_);
lean_dec(v_constName_136_);
lean_dec_ref(v___x_148_);
lean_dec_ref(v_env_147_);
v___x_150_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v___x_149_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v___x_152_; lean_object* v_env_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec_ref_known(v___x_151_, 1);
v___x_152_ = lean_st_ref_get(v___y_141_);
v_env_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc_ref(v_env_153_);
lean_dec(v___x_152_);
v___x_154_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_140_);
v___x_155_ = l_Lean_Environment_evalConst___redArg(v_env_153_, v___x_154_, v_constName_136_, v_checkMeta_137_);
lean_dec(v_constName_136_);
lean_dec_ref(v___x_154_);
lean_dec_ref(v_env_153_);
v___x_156_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v___x_155_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_156_;
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_constName_136_);
v_a_157_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_151_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_151_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg___boxed(lean_object* v_constName_165_, lean_object* v_checkMeta_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v_checkMeta_boxed_172_; lean_object* v_res_173_; 
v_checkMeta_boxed_172_ = lean_unbox(v_checkMeta_166_);
v_res_173_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v_constName_165_, v_checkMeta_boxed_172_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_173_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v___x_174_, lean_object* v___x_175_, lean_object* v_as_176_, size_t v_i_177_, size_t v_stop_178_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_eq(v_i_177_, v_stop_178_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_array_uget_borrowed(v_as_176_, v_i_177_);
v___x_185_ = l_Lean_Environment_isImportedConst(v___x_174_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_nat_dec_lt(v___x_186_, v___x_175_);
if (v___x_187_ == 0)
{
goto v___jp_179_;
}
else
{
return v___x_187_;
}
}
else
{
goto v___jp_179_;
}
}
else
{
uint8_t v___x_188_; 
v___x_188_ = 0;
return v___x_188_;
}
v___jp_179_:
{
size_t v___x_180_; size_t v___x_181_; 
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_add(v_i_177_, v___x_180_);
v_i_177_ = v___x_181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v___x_189_, lean_object* v___x_190_, lean_object* v_as_191_, lean_object* v_i_192_, lean_object* v_stop_193_){
_start:
{
size_t v_i_boxed_194_; size_t v_stop_boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_i_boxed_194_ = lean_unbox_usize(v_i_192_);
lean_dec(v_i_192_);
v_stop_boxed_195_ = lean_unbox_usize(v_stop_193_);
lean_dec(v_stop_193_);
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v___x_189_, v___x_190_, v_as_191_, v_i_boxed_194_, v_stop_boxed_195_);
lean_dec_ref(v_as_191_);
lean_dec(v___x_190_);
lean_dec_ref(v___x_189_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7(lean_object* v_o_201_, lean_object* v_k_202_, uint8_t v_v_203_){
_start:
{
lean_object* v_map_204_; uint8_t v_hasTrace_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_219_; 
v_map_204_ = lean_ctor_get(v_o_201_, 0);
v_hasTrace_205_ = lean_ctor_get_uint8(v_o_201_, sizeof(void*)*1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_o_201_);
if (v_isSharedCheck_219_ == 0)
{
v___x_207_ = v_o_201_;
v_isShared_208_ = v_isSharedCheck_219_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_map_204_);
lean_dec(v_o_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_219_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_209_, 0, v_v_203_);
lean_inc(v_k_202_);
v___x_210_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_202_, v___x_209_, v_map_204_);
if (v_hasTrace_205_ == 0)
{
lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_214_; 
v___x_211_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___closed__1));
v___x_212_ = l_Lean_Name_isPrefixOf(v___x_211_, v_k_202_);
lean_dec(v_k_202_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_214_ = v___x_207_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_210_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_212_);
return v___x_214_;
}
}
else
{
lean_object* v___x_217_; 
lean_dec(v_k_202_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_217_ = v___x_207_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_218_, sizeof(void*)*1, v_hasTrace_205_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7___boxed(lean_object* v_o_220_, lean_object* v_k_221_, lean_object* v_v_222_){
_start:
{
uint8_t v_v_boxed_223_; lean_object* v_res_224_; 
v_v_boxed_223_ = lean_unbox(v_v_222_);
v_res_224_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_o_220_, v_k_221_, v_v_boxed_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_opts_225_, lean_object* v_opt_226_, uint8_t v_val_227_){
_start:
{
lean_object* v_name_228_; lean_object* v___x_229_; 
v_name_228_ = lean_ctor_get(v_opt_226_, 0);
lean_inc(v_name_228_);
lean_dec_ref(v_opt_226_);
v___x_229_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4_spec__7(v_opts_225_, v_name_228_, v_val_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_opts_230_, lean_object* v_opt_231_, lean_object* v_val_232_){
_start:
{
uint8_t v_val_boxed_233_; lean_object* v_res_234_; 
v_val_boxed_233_ = lean_unbox(v_val_232_);
v_res_234_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v_opts_230_, v_opt_231_, v_val_boxed_233_);
return v_res_234_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_235_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg(){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__1);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___boxed(lean_object* v___dummy_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg();
return v_res_241_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg___closed__0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1___redArg();
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_248_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_249_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_247_);
lean_ctor_set(v___x_249_, 3, v___x_247_);
lean_ctor_set(v___x_249_, 4, v___x_247_);
lean_ctor_set(v___x_249_, 5, v___x_247_);
lean_ctor_set(v___x_249_, 6, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_unsigned_to_nat(16u);
v___x_256_ = lean_mk_array(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9));
v___x_263_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_ctor_set(v___x_264_, 2, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11));
v___x_267_ = l_Lean_stringToMessageData(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_268_, lean_object* v_checkType_269_, uint8_t v_safety_270_, lean_object* v_value_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; uint8_t v___y_283_; uint8_t v___y_284_; uint16_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; uint8_t v___y_337_; uint8_t v___y_338_; lean_object* v___y_339_; uint8_t v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; uint16_t v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; uint8_t v___y_371_; uint8_t v___y_372_; uint8_t v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; uint16_t v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; uint8_t v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; uint16_t v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; uint8_t v___y_409_; uint8_t v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; uint8_t v___y_454_; uint8_t v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; uint16_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; uint8_t v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; uint16_t v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; uint8_t v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; uint8_t v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; uint16_t v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v___y_525_; uint8_t v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_569_; lean_object* v___y_570_; uint8_t v___y_571_; uint8_t v___y_572_; uint8_t v___y_573_; lean_object* v___y_574_; uint16_t v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; uint8_t v___y_605_; lean_object* v___y_606_; uint16_t v___y_607_; lean_object* v___y_608_; uint8_t v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; uint8_t v___y_614_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; uint8_t v___y_620_; lean_object* v___y_621_; uint8_t v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v_nextMacroScope_768_; lean_object* v_ngen_769_; lean_object* v_auxDeclNGen_770_; lean_object* v_traceState_771_; lean_object* v_recordedDeps_772_; lean_object* v_messages_773_; lean_object* v_infoState_774_; lean_object* v_snapshotTasks_775_; lean_object* v___y_776_; lean_object* v___x_795_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_795_ = lean_st_ref_get(v___y_275_);
lean_inc_ref(v_value_271_);
v___x_809_ = l_Lean_Expr_getUsedConstants(v_value_271_);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_array_get_size(v___x_809_);
v___x_812_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v___x_809_);
lean_dec(v___x_795_);
goto v___jp_796_;
}
else
{
if (v___x_812_ == 0)
{
lean_dec_ref(v___x_809_);
lean_dec(v___x_795_);
goto v___jp_796_;
}
else
{
lean_object* v_env_813_; size_t v___x_814_; size_t v___x_815_; uint8_t v___x_816_; 
v_env_813_ = lean_ctor_get(v___x_795_, 0);
lean_inc_ref(v_env_813_);
lean_dec(v___x_795_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_811_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_813_, v___x_811_, v___x_809_, v___x_814_, v___x_815_);
lean_dec_ref(v___x_809_);
lean_dec_ref(v_env_813_);
if (v___x_816_ == 0)
{
goto v___jp_796_;
}
else
{
goto v___jp_725_;
}
}
}
v___jp_277_:
{
lean_object* v_toCold_289_; lean_object* v_currRecDepth_290_; lean_object* v_ref_291_; uint8_t v_suppressElabErrors_292_; uint8_t v_checkDeprecated_293_; uint8_t v_isRecordingDeps_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_331_; 
v_toCold_289_ = lean_ctor_get(v___y_287_, 0);
v_currRecDepth_290_ = lean_ctor_get(v___y_287_, 1);
v_ref_291_ = lean_ctor_get(v___y_287_, 2);
v_suppressElabErrors_292_ = lean_ctor_get_uint8(v___y_287_, sizeof(void*)*3 + 2);
v_checkDeprecated_293_ = lean_ctor_get_uint8(v___y_287_, sizeof(void*)*3 + 3);
v_isRecordingDeps_294_ = lean_ctor_get_uint8(v___y_287_, sizeof(void*)*3 + 4);
v_isSharedCheck_331_ = !lean_is_exclusive(v___y_287_);
if (v_isSharedCheck_331_ == 0)
{
v___x_296_ = v___y_287_;
v_isShared_297_ = v_isSharedCheck_331_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_ref_291_);
lean_inc(v_currRecDepth_290_);
lean_inc(v_toCold_289_);
lean_dec(v___y_287_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_331_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_fileName_298_; lean_object* v_fileMap_299_; lean_object* v_currNamespace_300_; lean_object* v_openDecls_301_; lean_object* v_initHeartbeats_302_; lean_object* v_maxHeartbeats_303_; lean_object* v_quotContext_304_; lean_object* v_currMacroScope_305_; lean_object* v_cancelTk_x3f_306_; lean_object* v_inheritedTraceOptions_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_328_; 
v_fileName_298_ = lean_ctor_get(v_toCold_289_, 0);
v_fileMap_299_ = lean_ctor_get(v_toCold_289_, 1);
v_currNamespace_300_ = lean_ctor_get(v_toCold_289_, 4);
v_openDecls_301_ = lean_ctor_get(v_toCold_289_, 5);
v_initHeartbeats_302_ = lean_ctor_get(v_toCold_289_, 6);
v_maxHeartbeats_303_ = lean_ctor_get(v_toCold_289_, 7);
v_quotContext_304_ = lean_ctor_get(v_toCold_289_, 8);
v_currMacroScope_305_ = lean_ctor_get(v_toCold_289_, 9);
v_cancelTk_x3f_306_ = lean_ctor_get(v_toCold_289_, 10);
v_inheritedTraceOptions_307_ = lean_ctor_get(v_toCold_289_, 11);
v_isSharedCheck_328_ = !lean_is_exclusive(v_toCold_289_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; lean_object* v_unused_330_; 
v_unused_329_ = lean_ctor_get(v_toCold_289_, 3);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_toCold_289_, 2);
lean_dec(v_unused_330_);
v___x_309_ = v_toCold_289_;
v_isShared_310_ = v_isSharedCheck_328_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_inheritedTraceOptions_307_);
lean_inc(v_cancelTk_x3f_306_);
lean_inc(v_currMacroScope_305_);
lean_inc(v_quotContext_304_);
lean_inc(v_maxHeartbeats_303_);
lean_inc(v_initHeartbeats_302_);
lean_inc(v_openDecls_301_);
lean_inc(v_currNamespace_300_);
lean_inc(v_fileMap_299_);
lean_inc(v_fileName_298_);
lean_dec(v_toCold_289_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_328_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_282_, v___y_278_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v___x_311_);
lean_ctor_set(v___x_309_, 2, v___y_282_);
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_fileName_298_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_fileMap_299_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v___y_282_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_currNamespace_300_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v_openDecls_301_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_initHeartbeats_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 7, v_maxHeartbeats_303_);
lean_ctor_set(v_reuseFailAlloc_327_, 8, v_quotContext_304_);
lean_ctor_set(v_reuseFailAlloc_327_, 9, v_currMacroScope_305_);
lean_ctor_set(v_reuseFailAlloc_327_, 10, v_cancelTk_x3f_306_);
lean_ctor_set(v_reuseFailAlloc_327_, 11, v_inheritedTraceOptions_307_);
v___x_313_ = v_reuseFailAlloc_327_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_313_);
v___x_315_ = v___x_296_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_currRecDepth_290_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_ref_291_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3 + 2, v_suppressElabErrors_292_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3 + 3, v_checkDeprecated_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3 + 4, v_isRecordingDeps_294_);
v___x_315_ = v_reuseFailAlloc_326_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; 
lean_ctor_set_uint16(v___x_315_, sizeof(void*)*3, v___y_285_);
v___x_316_ = l_Lean_addAndCompile(v___y_279_, v___y_284_, v___y_283_, v___x_315_, v___y_288_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v___x_317_; 
lean_dec_ref_known(v___x_316_, 1);
v___x_317_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v___y_281_, v_checkMeta_268_, v___y_280_, v___y_286_, v___x_315_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___x_315_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_280_);
return v___x_317_;
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v___x_315_);
lean_dec(v___y_288_);
lean_dec(v___y_286_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
v_a_318_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_316_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
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
}
}
}
v___jp_332_:
{
lean_object* v___x_346_; lean_object* v_env_347_; lean_object* v_nextMacroScope_348_; lean_object* v_ngen_349_; lean_object* v_auxDeclNGen_350_; lean_object* v_traceState_351_; lean_object* v_recordedDeps_352_; lean_object* v_messages_353_; lean_object* v_infoState_354_; lean_object* v_snapshotTasks_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_364_; 
v___x_346_ = lean_st_ref_take(v___y_345_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
v_nextMacroScope_348_ = lean_ctor_get(v___x_346_, 1);
v_ngen_349_ = lean_ctor_get(v___x_346_, 2);
v_auxDeclNGen_350_ = lean_ctor_get(v___x_346_, 3);
v_traceState_351_ = lean_ctor_get(v___x_346_, 4);
v_recordedDeps_352_ = lean_ctor_get(v___x_346_, 6);
v_messages_353_ = lean_ctor_get(v___x_346_, 7);
v_infoState_354_ = lean_ctor_get(v___x_346_, 8);
v_snapshotTasks_355_ = lean_ctor_get(v___x_346_, 9);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_346_, 5);
lean_dec(v_unused_365_);
v___x_357_ = v___x_346_;
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snapshotTasks_355_);
lean_inc(v_infoState_354_);
lean_inc(v_messages_353_);
lean_inc(v_recordedDeps_352_);
lean_inc(v_traceState_351_);
lean_inc(v_auxDeclNGen_350_);
lean_inc(v_ngen_349_);
lean_inc(v_nextMacroScope_348_);
lean_inc(v_env_347_);
lean_dec(v___x_346_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = l_Lean_Kernel_enableDiag(v_env_347_, v___y_340_);
lean_inc_ref(v___y_341_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 5, v___y_341_);
lean_ctor_set(v___x_357_, 0, v___x_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_nextMacroScope_348_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_ngen_349_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_auxDeclNGen_350_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v_traceState_351_);
lean_ctor_set(v_reuseFailAlloc_363_, 5, v___y_341_);
lean_ctor_set(v_reuseFailAlloc_363_, 6, v_recordedDeps_352_);
lean_ctor_set(v_reuseFailAlloc_363_, 7, v_messages_353_);
lean_ctor_set(v_reuseFailAlloc_363_, 8, v_infoState_354_);
lean_ctor_set(v_reuseFailAlloc_363_, 9, v_snapshotTasks_355_);
v___x_361_ = v_reuseFailAlloc_363_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_st_ref_put(v___y_345_, v___x_361_);
v___y_278_ = v___y_333_;
v___y_279_ = v___y_334_;
v___y_280_ = v___y_339_;
v___y_281_ = v___y_335_;
v___y_282_ = v___y_336_;
v___y_283_ = v___y_337_;
v___y_284_ = v___y_338_;
v___y_285_ = v___y_343_;
v___y_286_ = v___y_344_;
v___y_287_ = v___y_342_;
v___y_288_ = v___y_345_;
goto v___jp_277_;
}
}
}
v___jp_366_:
{
if (v___y_380_ == 0)
{
if (v___y_373_ == 0)
{
v___y_278_ = v___y_367_;
v___y_279_ = v___y_368_;
v___y_280_ = v___y_374_;
v___y_281_ = v___y_369_;
v___y_282_ = v___y_370_;
v___y_283_ = v___y_371_;
v___y_284_ = v___y_372_;
v___y_285_ = v___y_377_;
v___y_286_ = v___y_378_;
v___y_287_ = v___y_376_;
v___y_288_ = v___y_379_;
goto v___jp_277_;
}
else
{
v___y_333_ = v___y_367_;
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_371_;
v___y_338_ = v___y_372_;
v___y_339_ = v___y_374_;
v___y_340_ = v___y_380_;
v___y_341_ = v___y_375_;
v___y_342_ = v___y_376_;
v___y_343_ = v___y_377_;
v___y_344_ = v___y_378_;
v___y_345_ = v___y_379_;
goto v___jp_332_;
}
}
else
{
if (v___y_373_ == 0)
{
v___y_333_ = v___y_367_;
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_371_;
v___y_338_ = v___y_372_;
v___y_339_ = v___y_374_;
v___y_340_ = v___y_380_;
v___y_341_ = v___y_375_;
v___y_342_ = v___y_376_;
v___y_343_ = v___y_377_;
v___y_344_ = v___y_378_;
v___y_345_ = v___y_379_;
goto v___jp_332_;
}
else
{
v___y_278_ = v___y_367_;
v___y_279_ = v___y_368_;
v___y_280_ = v___y_374_;
v___y_281_ = v___y_369_;
v___y_282_ = v___y_370_;
v___y_283_ = v___y_371_;
v___y_284_ = v___y_372_;
v___y_285_ = v___y_377_;
v___y_286_ = v___y_378_;
v___y_287_ = v___y_376_;
v___y_288_ = v___y_379_;
goto v___jp_277_;
}
}
}
v___jp_381_:
{
uint16_t v___x_393_; lean_object* v___x_394_; lean_object* v_env_395_; uint8_t v___x_396_; uint16_t v___x_397_; uint16_t v___x_398_; uint16_t v___x_399_; uint8_t v___x_400_; 
v___x_393_ = l_Lean_OptionFlags_ofOptions(v___y_392_);
v___x_394_ = lean_st_ref_get(v___y_390_);
v_env_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_env_395_);
lean_dec(v___x_394_);
v___x_396_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_395_);
lean_dec_ref(v_env_395_);
v___x_397_ = 512;
v___x_398_ = lean_uint16_land(v___x_393_, v___x_397_);
v___x_399_ = 0;
v___x_400_ = lean_uint16_dec_eq(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
v___y_367_ = v___y_382_;
v___y_368_ = v___y_383_;
v___y_369_ = v___y_385_;
v___y_370_ = v___y_392_;
v___y_371_ = v___y_387_;
v___y_372_ = v___y_388_;
v___y_373_ = v___x_396_;
v___y_374_ = v___y_384_;
v___y_375_ = v___y_386_;
v___y_376_ = v___y_389_;
v___y_377_ = v___x_393_;
v___y_378_ = v___y_391_;
v___y_379_ = v___y_390_;
v___y_380_ = v___y_388_;
goto v___jp_366_;
}
else
{
v___y_367_ = v___y_382_;
v___y_368_ = v___y_383_;
v___y_369_ = v___y_385_;
v___y_370_ = v___y_392_;
v___y_371_ = v___y_387_;
v___y_372_ = v___y_388_;
v___y_373_ = v___x_396_;
v___y_374_ = v___y_384_;
v___y_375_ = v___y_386_;
v___y_376_ = v___y_389_;
v___y_377_ = v___x_393_;
v___y_378_ = v___y_391_;
v___y_379_ = v___y_390_;
v___y_380_ = v___y_387_;
goto v___jp_366_;
}
}
v___jp_401_:
{
lean_object* v_toCold_414_; lean_object* v_currRecDepth_415_; lean_object* v_ref_416_; uint8_t v_suppressElabErrors_417_; uint8_t v_checkDeprecated_418_; uint8_t v_isRecordingDeps_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_449_; 
v_toCold_414_ = lean_ctor_get(v___y_412_, 0);
v_currRecDepth_415_ = lean_ctor_get(v___y_412_, 1);
v_ref_416_ = lean_ctor_get(v___y_412_, 2);
v_suppressElabErrors_417_ = lean_ctor_get_uint8(v___y_412_, sizeof(void*)*3 + 2);
v_checkDeprecated_418_ = lean_ctor_get_uint8(v___y_412_, sizeof(void*)*3 + 3);
v_isRecordingDeps_419_ = lean_ctor_get_uint8(v___y_412_, sizeof(void*)*3 + 4);
v_isSharedCheck_449_ = !lean_is_exclusive(v___y_412_);
if (v_isSharedCheck_449_ == 0)
{
v___x_421_ = v___y_412_;
v_isShared_422_ = v_isSharedCheck_449_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_ref_416_);
lean_inc(v_currRecDepth_415_);
lean_inc(v_toCold_414_);
lean_dec(v___y_412_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_449_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_fileName_423_; lean_object* v_fileMap_424_; lean_object* v_currNamespace_425_; lean_object* v_openDecls_426_; lean_object* v_initHeartbeats_427_; lean_object* v_maxHeartbeats_428_; lean_object* v_quotContext_429_; lean_object* v_currMacroScope_430_; lean_object* v_cancelTk_x3f_431_; lean_object* v_inheritedTraceOptions_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_446_; 
v_fileName_423_ = lean_ctor_get(v_toCold_414_, 0);
v_fileMap_424_ = lean_ctor_get(v_toCold_414_, 1);
v_currNamespace_425_ = lean_ctor_get(v_toCold_414_, 4);
v_openDecls_426_ = lean_ctor_get(v_toCold_414_, 5);
v_initHeartbeats_427_ = lean_ctor_get(v_toCold_414_, 6);
v_maxHeartbeats_428_ = lean_ctor_get(v_toCold_414_, 7);
v_quotContext_429_ = lean_ctor_get(v_toCold_414_, 8);
v_currMacroScope_430_ = lean_ctor_get(v_toCold_414_, 9);
v_cancelTk_x3f_431_ = lean_ctor_get(v_toCold_414_, 10);
v_inheritedTraceOptions_432_ = lean_ctor_get(v_toCold_414_, 11);
v_isSharedCheck_446_ = !lean_is_exclusive(v_toCold_414_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_447_ = lean_ctor_get(v_toCold_414_, 3);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_toCold_414_, 2);
lean_dec(v_unused_448_);
v___x_434_ = v_toCold_414_;
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_inheritedTraceOptions_432_);
lean_inc(v_cancelTk_x3f_431_);
lean_inc(v_currMacroScope_430_);
lean_inc(v_quotContext_429_);
lean_inc(v_maxHeartbeats_428_);
lean_inc(v_initHeartbeats_427_);
lean_inc(v_openDecls_426_);
lean_inc(v_currNamespace_425_);
lean_inc(v_fileMap_424_);
lean_inc(v_fileName_423_);
lean_dec(v_toCold_414_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_407_, v___y_402_);
lean_inc_ref(v___y_407_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 3, v___x_436_);
lean_ctor_set(v___x_434_, 2, v___y_407_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fileName_423_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_fileMap_424_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v___y_407_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_currNamespace_425_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v_openDecls_426_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_initHeartbeats_427_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_maxHeartbeats_428_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_quotContext_429_);
lean_ctor_set(v_reuseFailAlloc_445_, 9, v_currMacroScope_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 10, v_cancelTk_x3f_431_);
lean_ctor_set(v_reuseFailAlloc_445_, 11, v_inheritedTraceOptions_432_);
v___x_438_ = v_reuseFailAlloc_445_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_438_);
v___x_440_ = v___x_421_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_currRecDepth_415_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_ref_416_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*3 + 2, v_suppressElabErrors_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*3 + 3, v_checkDeprecated_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*3 + 4, v_isRecordingDeps_419_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_ctor_set_uint16(v___x_440_, sizeof(void*)*3, v___y_405_);
if (v_isRecordingDeps_419_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_442_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v___y_407_, v___x_441_, v___y_410_);
v___y_382_ = v___y_402_;
v___y_383_ = v___y_403_;
v___y_384_ = v___y_404_;
v___y_385_ = v___y_406_;
v___y_386_ = v___y_408_;
v___y_387_ = v___y_409_;
v___y_388_ = v___y_410_;
v___y_389_ = v___x_440_;
v___y_390_ = v___y_413_;
v___y_391_ = v___y_411_;
v___y_392_ = v___x_442_;
goto v___jp_381_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_407_);
v___y_382_ = v___y_402_;
v___y_383_ = v___y_403_;
v___y_384_ = v___y_404_;
v___y_385_ = v___y_406_;
v___y_386_ = v___y_408_;
v___y_387_ = v___y_409_;
v___y_388_ = v___y_410_;
v___y_389_ = v___x_440_;
v___y_390_ = v___y_413_;
v___y_391_ = v___y_411_;
v___y_392_ = v___x_443_;
goto v___jp_381_;
}
}
}
}
}
}
v___jp_450_:
{
lean_object* v___x_464_; lean_object* v_env_465_; lean_object* v_nextMacroScope_466_; lean_object* v_ngen_467_; lean_object* v_auxDeclNGen_468_; lean_object* v_traceState_469_; lean_object* v_recordedDeps_470_; lean_object* v_messages_471_; lean_object* v_infoState_472_; lean_object* v_snapshotTasks_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
v___x_464_ = lean_st_ref_take(v___y_457_);
v_env_465_ = lean_ctor_get(v___x_464_, 0);
v_nextMacroScope_466_ = lean_ctor_get(v___x_464_, 1);
v_ngen_467_ = lean_ctor_get(v___x_464_, 2);
v_auxDeclNGen_468_ = lean_ctor_get(v___x_464_, 3);
v_traceState_469_ = lean_ctor_get(v___x_464_, 4);
v_recordedDeps_470_ = lean_ctor_get(v___x_464_, 6);
v_messages_471_ = lean_ctor_get(v___x_464_, 7);
v_infoState_472_ = lean_ctor_get(v___x_464_, 8);
v_snapshotTasks_473_ = lean_ctor_get(v___x_464_, 9);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_464_, 5);
lean_dec(v_unused_483_);
v___x_475_ = v___x_464_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snapshotTasks_473_);
lean_inc(v_infoState_472_);
lean_inc(v_messages_471_);
lean_inc(v_recordedDeps_470_);
lean_inc(v_traceState_469_);
lean_inc(v_auxDeclNGen_468_);
lean_inc(v_ngen_467_);
lean_inc(v_nextMacroScope_466_);
lean_inc(v_env_465_);
lean_dec(v___x_464_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_Lean_Kernel_enableDiag(v_env_465_, v___y_462_);
lean_inc_ref(v___y_461_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 5, v___y_461_);
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_nextMacroScope_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ngen_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_auxDeclNGen_468_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_traceState_469_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v___y_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_recordedDeps_470_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_messages_471_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_infoState_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 9, v_snapshotTasks_473_);
v___x_479_ = v_reuseFailAlloc_481_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; 
v___x_480_ = lean_st_ref_put(v___y_457_, v___x_479_);
v___y_402_ = v___y_451_;
v___y_403_ = v___y_452_;
v___y_404_ = v___y_458_;
v___y_405_ = v___y_459_;
v___y_406_ = v___y_453_;
v___y_407_ = v___y_460_;
v___y_408_ = v___y_461_;
v___y_409_ = v___y_454_;
v___y_410_ = v___y_455_;
v___y_411_ = v___y_463_;
v___y_412_ = v___y_456_;
v___y_413_ = v___y_457_;
goto v___jp_401_;
}
}
}
v___jp_484_:
{
if (v___y_498_ == 0)
{
if (v___y_496_ == 0)
{
v___y_402_ = v___y_485_;
v___y_403_ = v___y_486_;
v___y_404_ = v___y_492_;
v___y_405_ = v___y_493_;
v___y_406_ = v___y_487_;
v___y_407_ = v___y_494_;
v___y_408_ = v___y_495_;
v___y_409_ = v___y_488_;
v___y_410_ = v___y_489_;
v___y_411_ = v___y_497_;
v___y_412_ = v___y_490_;
v___y_413_ = v___y_491_;
goto v___jp_401_;
}
else
{
v___y_451_ = v___y_485_;
v___y_452_ = v___y_486_;
v___y_453_ = v___y_487_;
v___y_454_ = v___y_488_;
v___y_455_ = v___y_489_;
v___y_456_ = v___y_490_;
v___y_457_ = v___y_491_;
v___y_458_ = v___y_492_;
v___y_459_ = v___y_493_;
v___y_460_ = v___y_494_;
v___y_461_ = v___y_495_;
v___y_462_ = v___y_498_;
v___y_463_ = v___y_497_;
goto v___jp_450_;
}
}
else
{
if (v___y_496_ == 0)
{
v___y_451_ = v___y_485_;
v___y_452_ = v___y_486_;
v___y_453_ = v___y_487_;
v___y_454_ = v___y_488_;
v___y_455_ = v___y_489_;
v___y_456_ = v___y_490_;
v___y_457_ = v___y_491_;
v___y_458_ = v___y_492_;
v___y_459_ = v___y_493_;
v___y_460_ = v___y_494_;
v___y_461_ = v___y_495_;
v___y_462_ = v___y_498_;
v___y_463_ = v___y_497_;
goto v___jp_450_;
}
else
{
v___y_402_ = v___y_485_;
v___y_403_ = v___y_486_;
v___y_404_ = v___y_492_;
v___y_405_ = v___y_493_;
v___y_406_ = v___y_487_;
v___y_407_ = v___y_494_;
v___y_408_ = v___y_495_;
v___y_409_ = v___y_488_;
v___y_410_ = v___y_489_;
v___y_411_ = v___y_497_;
v___y_412_ = v___y_490_;
v___y_413_ = v___y_491_;
goto v___jp_401_;
}
}
}
v___jp_499_:
{
uint16_t v___x_511_; lean_object* v___x_512_; lean_object* v_env_513_; uint8_t v___x_514_; uint16_t v___x_515_; uint16_t v___x_516_; uint16_t v___x_517_; uint8_t v___x_518_; 
v___x_511_ = l_Lean_OptionFlags_ofOptions(v___y_510_);
v___x_512_ = lean_st_ref_get(v___y_500_);
v_env_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_env_513_);
lean_dec(v___x_512_);
v___x_514_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_513_);
lean_dec_ref(v_env_513_);
v___x_515_ = 512;
v___x_516_ = lean_uint16_land(v___x_511_, v___x_515_);
v___x_517_ = 0;
v___x_518_ = lean_uint16_dec_eq(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
v___y_485_ = v___y_501_;
v___y_486_ = v___y_502_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_506_;
v___y_489_ = v___y_507_;
v___y_490_ = v___y_508_;
v___y_491_ = v___y_500_;
v___y_492_ = v___y_503_;
v___y_493_ = v___x_511_;
v___y_494_ = v___y_510_;
v___y_495_ = v___y_505_;
v___y_496_ = v___x_514_;
v___y_497_ = v___y_509_;
v___y_498_ = v___y_507_;
goto v___jp_484_;
}
else
{
v___y_485_ = v___y_501_;
v___y_486_ = v___y_502_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_506_;
v___y_489_ = v___y_507_;
v___y_490_ = v___y_508_;
v___y_491_ = v___y_500_;
v___y_492_ = v___y_503_;
v___y_493_ = v___x_511_;
v___y_494_ = v___y_510_;
v___y_495_ = v___y_505_;
v___y_496_ = v___x_514_;
v___y_497_ = v___y_509_;
v___y_498_ = v___y_506_;
goto v___jp_484_;
}
}
v___jp_519_:
{
lean_object* v_toCold_531_; lean_object* v_currRecDepth_532_; lean_object* v_ref_533_; uint8_t v_suppressElabErrors_534_; uint8_t v_checkDeprecated_535_; uint8_t v_isRecordingDeps_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_567_; 
v_toCold_531_ = lean_ctor_get(v___y_529_, 0);
v_currRecDepth_532_ = lean_ctor_get(v___y_529_, 1);
v_ref_533_ = lean_ctor_get(v___y_529_, 2);
v_suppressElabErrors_534_ = lean_ctor_get_uint8(v___y_529_, sizeof(void*)*3 + 2);
v_checkDeprecated_535_ = lean_ctor_get_uint8(v___y_529_, sizeof(void*)*3 + 3);
v_isRecordingDeps_536_ = lean_ctor_get_uint8(v___y_529_, sizeof(void*)*3 + 4);
v_isSharedCheck_567_ = !lean_is_exclusive(v___y_529_);
if (v_isSharedCheck_567_ == 0)
{
v___x_538_ = v___y_529_;
v_isShared_539_ = v_isSharedCheck_567_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_ref_533_);
lean_inc(v_currRecDepth_532_);
lean_inc(v_toCold_531_);
lean_dec(v___y_529_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_567_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_fileName_540_; lean_object* v_fileMap_541_; lean_object* v_currNamespace_542_; lean_object* v_openDecls_543_; lean_object* v_initHeartbeats_544_; lean_object* v_maxHeartbeats_545_; lean_object* v_quotContext_546_; lean_object* v_currMacroScope_547_; lean_object* v_cancelTk_x3f_548_; lean_object* v_inheritedTraceOptions_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_564_; 
v_fileName_540_ = lean_ctor_get(v_toCold_531_, 0);
v_fileMap_541_ = lean_ctor_get(v_toCold_531_, 1);
v_currNamespace_542_ = lean_ctor_get(v_toCold_531_, 4);
v_openDecls_543_ = lean_ctor_get(v_toCold_531_, 5);
v_initHeartbeats_544_ = lean_ctor_get(v_toCold_531_, 6);
v_maxHeartbeats_545_ = lean_ctor_get(v_toCold_531_, 7);
v_quotContext_546_ = lean_ctor_get(v_toCold_531_, 8);
v_currMacroScope_547_ = lean_ctor_get(v_toCold_531_, 9);
v_cancelTk_x3f_548_ = lean_ctor_get(v_toCold_531_, 10);
v_inheritedTraceOptions_549_ = lean_ctor_get(v_toCold_531_, 11);
v_isSharedCheck_564_ = !lean_is_exclusive(v_toCold_531_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; lean_object* v_unused_566_; 
v_unused_565_ = lean_ctor_get(v_toCold_531_, 3);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_toCold_531_, 2);
lean_dec(v_unused_566_);
v___x_551_ = v_toCold_531_;
v_isShared_552_ = v_isSharedCheck_564_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_inheritedTraceOptions_549_);
lean_inc(v_cancelTk_x3f_548_);
lean_inc(v_currMacroScope_547_);
lean_inc(v_quotContext_546_);
lean_inc(v_maxHeartbeats_545_);
lean_inc(v_initHeartbeats_544_);
lean_inc(v_openDecls_543_);
lean_inc(v_currNamespace_542_);
lean_inc(v_fileMap_541_);
lean_inc(v_fileName_540_);
lean_dec(v_toCold_531_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_564_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = l_Lean_maxRecDepth;
v___x_554_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_527_, v___x_553_);
lean_inc_ref(v___y_527_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 3, v___x_554_);
lean_ctor_set(v___x_551_, 2, v___y_527_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_fileName_540_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_fileMap_541_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v___y_527_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_currNamespace_542_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v_openDecls_543_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v_initHeartbeats_544_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v_maxHeartbeats_545_);
lean_ctor_set(v_reuseFailAlloc_563_, 8, v_quotContext_546_);
lean_ctor_set(v_reuseFailAlloc_563_, 9, v_currMacroScope_547_);
lean_ctor_set(v_reuseFailAlloc_563_, 10, v_cancelTk_x3f_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 11, v_inheritedTraceOptions_549_);
v___x_556_ = v_reuseFailAlloc_563_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_556_);
v___x_558_ = v___x_538_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_currRecDepth_532_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_ref_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*3 + 2, v_suppressElabErrors_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*3 + 3, v_checkDeprecated_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*3 + 4, v_isRecordingDeps_536_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_ctor_set_uint16(v___x_558_, sizeof(void*)*3, v___y_520_);
if (v_isRecordingDeps_536_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_560_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v___y_527_, v___x_559_, v_isRecordingDeps_536_);
v___y_500_ = v___y_530_;
v___y_501_ = v___x_553_;
v___y_502_ = v___y_521_;
v___y_503_ = v___y_522_;
v___y_504_ = v___y_523_;
v___y_505_ = v___y_524_;
v___y_506_ = v___y_525_;
v___y_507_ = v___y_526_;
v___y_508_ = v___x_558_;
v___y_509_ = v___y_528_;
v___y_510_ = v___x_560_;
goto v___jp_499_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_527_);
v___y_500_ = v___y_530_;
v___y_501_ = v___x_553_;
v___y_502_ = v___y_521_;
v___y_503_ = v___y_522_;
v___y_504_ = v___y_523_;
v___y_505_ = v___y_524_;
v___y_506_ = v___y_525_;
v___y_507_ = v___y_526_;
v___y_508_ = v___x_558_;
v___y_509_ = v___y_528_;
v___y_510_ = v___x_561_;
goto v___jp_499_;
}
}
}
}
}
}
v___jp_568_:
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v_nextMacroScope_583_; lean_object* v_ngen_584_; lean_object* v_auxDeclNGen_585_; lean_object* v_traceState_586_; lean_object* v_recordedDeps_587_; lean_object* v_messages_588_; lean_object* v_infoState_589_; lean_object* v_snapshotTasks_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_599_; 
v___x_581_ = lean_st_ref_take(v___y_574_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
v_nextMacroScope_583_ = lean_ctor_get(v___x_581_, 1);
v_ngen_584_ = lean_ctor_get(v___x_581_, 2);
v_auxDeclNGen_585_ = lean_ctor_get(v___x_581_, 3);
v_traceState_586_ = lean_ctor_get(v___x_581_, 4);
v_recordedDeps_587_ = lean_ctor_get(v___x_581_, 6);
v_messages_588_ = lean_ctor_get(v___x_581_, 7);
v_infoState_589_ = lean_ctor_get(v___x_581_, 8);
v_snapshotTasks_590_ = lean_ctor_get(v___x_581_, 9);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_581_, 5);
lean_dec(v_unused_600_);
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snapshotTasks_590_);
lean_inc(v_infoState_589_);
lean_inc(v_messages_588_);
lean_inc(v_recordedDeps_587_);
lean_inc(v_traceState_586_);
lean_inc(v_auxDeclNGen_585_);
lean_inc(v_ngen_584_);
lean_inc(v_nextMacroScope_583_);
lean_inc(v_env_582_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_Kernel_enableDiag(v_env_582_, v___y_572_);
lean_inc_ref(v___y_577_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 5, v___y_577_);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_nextMacroScope_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_ngen_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_auxDeclNGen_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_traceState_586_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v___y_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_recordedDeps_587_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_messages_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_infoState_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 9, v_snapshotTasks_590_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_st_ref_put(v___y_574_, v___x_596_);
v___y_520_ = v___y_575_;
v___y_521_ = v___y_569_;
v___y_522_ = v___y_576_;
v___y_523_ = v___y_570_;
v___y_524_ = v___y_577_;
v___y_525_ = v___y_571_;
v___y_526_ = v___y_573_;
v___y_527_ = v___y_579_;
v___y_528_ = v___y_580_;
v___y_529_ = v___y_578_;
v___y_530_ = v___y_574_;
goto v___jp_519_;
}
}
}
v___jp_601_:
{
if (v___y_614_ == 0)
{
if (v___y_609_ == 0)
{
v___y_520_ = v___y_607_;
v___y_521_ = v___y_602_;
v___y_522_ = v___y_608_;
v___y_523_ = v___y_603_;
v___y_524_ = v___y_610_;
v___y_525_ = v___y_604_;
v___y_526_ = v___y_605_;
v___y_527_ = v___y_612_;
v___y_528_ = v___y_613_;
v___y_529_ = v___y_611_;
v___y_530_ = v___y_606_;
goto v___jp_519_;
}
else
{
v___y_569_ = v___y_602_;
v___y_570_ = v___y_603_;
v___y_571_ = v___y_604_;
v___y_572_ = v___y_614_;
v___y_573_ = v___y_605_;
v___y_574_ = v___y_606_;
v___y_575_ = v___y_607_;
v___y_576_ = v___y_608_;
v___y_577_ = v___y_610_;
v___y_578_ = v___y_611_;
v___y_579_ = v___y_612_;
v___y_580_ = v___y_613_;
goto v___jp_568_;
}
}
else
{
if (v___y_609_ == 0)
{
v___y_569_ = v___y_602_;
v___y_570_ = v___y_603_;
v___y_571_ = v___y_604_;
v___y_572_ = v___y_614_;
v___y_573_ = v___y_605_;
v___y_574_ = v___y_606_;
v___y_575_ = v___y_607_;
v___y_576_ = v___y_608_;
v___y_577_ = v___y_610_;
v___y_578_ = v___y_611_;
v___y_579_ = v___y_612_;
v___y_580_ = v___y_613_;
goto v___jp_568_;
}
else
{
v___y_520_ = v___y_607_;
v___y_521_ = v___y_602_;
v___y_522_ = v___y_608_;
v___y_523_ = v___y_603_;
v___y_524_ = v___y_610_;
v___y_525_ = v___y_604_;
v___y_526_ = v___y_605_;
v___y_527_ = v___y_612_;
v___y_528_ = v___y_613_;
v___y_529_ = v___y_611_;
v___y_530_ = v___y_606_;
goto v___jp_519_;
}
}
}
v___jp_615_:
{
uint16_t v___x_626_; lean_object* v___x_627_; lean_object* v_env_628_; uint8_t v___x_629_; uint16_t v___x_630_; uint16_t v___x_631_; uint16_t v___x_632_; uint8_t v___x_633_; 
v___x_626_ = l_Lean_OptionFlags_ofOptions(v___y_625_);
v___x_627_ = lean_st_ref_get(v___y_623_);
v_env_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_env_628_);
lean_dec(v___x_627_);
v___x_629_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_628_);
lean_dec_ref(v_env_628_);
v___x_630_ = 512;
v___x_631_ = lean_uint16_land(v___x_626_, v___x_630_);
v___x_632_ = 0;
v___x_633_ = lean_uint16_dec_eq(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
v___y_602_ = v___y_616_;
v___y_603_ = v___y_618_;
v___y_604_ = v___y_620_;
v___y_605_ = v___y_622_;
v___y_606_ = v___y_623_;
v___y_607_ = v___x_626_;
v___y_608_ = v___y_617_;
v___y_609_ = v___x_629_;
v___y_610_ = v___y_619_;
v___y_611_ = v___y_621_;
v___y_612_ = v___y_625_;
v___y_613_ = v___y_624_;
v___y_614_ = v___y_622_;
goto v___jp_601_;
}
else
{
v___y_602_ = v___y_616_;
v___y_603_ = v___y_618_;
v___y_604_ = v___y_620_;
v___y_605_ = v___y_622_;
v___y_606_ = v___y_623_;
v___y_607_ = v___x_626_;
v___y_608_ = v___y_617_;
v___y_609_ = v___x_629_;
v___y_610_ = v___y_619_;
v___y_611_ = v___y_621_;
v___y_612_ = v___y_625_;
v___y_613_ = v___y_624_;
v___y_614_ = v___y_620_;
goto v___jp_601_;
}
}
v___jp_634_:
{
lean_object* v___x_643_; 
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
lean_inc(v___y_640_);
lean_inc_ref(v___y_639_);
lean_inc_ref(v___y_635_);
v___x_643_ = lean_infer_type(v___y_635_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_n(v_a_644_, 2);
lean_dec_ref_known(v___x_643_, 1);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
lean_inc(v___y_640_);
lean_inc_ref(v___y_639_);
v___x_645_ = lean_apply_6(v_checkType_269_, v_a_644_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, lean_box(0));
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_env_653_; lean_object* v_nextMacroScope_654_; lean_object* v_ngen_655_; lean_object* v_auxDeclNGen_656_; lean_object* v_traceState_657_; lean_object* v_recordedDeps_658_; lean_object* v_messages_659_; lean_object* v_infoState_660_; lean_object* v_snapshotTasks_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref_known(v___x_645_, 1);
v___x_646_ = lean_array_to_list(v___y_638_);
lean_inc_n(v___y_636_, 2);
v___x_647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_647_, 0, v___y_636_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_ctor_set(v___x_647_, 2, v_a_644_);
v___x_648_ = lean_box(0);
lean_inc(v___y_637_);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_636_);
lean_ctor_set(v___x_649_, 1, v___y_637_);
v___x_650_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_650_, 0, v___x_647_);
lean_ctor_set(v___x_650_, 1, v___y_635_);
lean_ctor_set(v___x_650_, 2, v___x_648_);
lean_ctor_set(v___x_650_, 3, v___x_649_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*4, v_safety_270_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_st_ref_take(v___y_642_);
v_env_653_ = lean_ctor_get(v___x_652_, 0);
v_nextMacroScope_654_ = lean_ctor_get(v___x_652_, 1);
v_ngen_655_ = lean_ctor_get(v___x_652_, 2);
v_auxDeclNGen_656_ = lean_ctor_get(v___x_652_, 3);
v_traceState_657_ = lean_ctor_get(v___x_652_, 4);
v_recordedDeps_658_ = lean_ctor_get(v___x_652_, 6);
v_messages_659_ = lean_ctor_get(v___x_652_, 7);
v_infoState_660_ = lean_ctor_get(v___x_652_, 8);
v_snapshotTasks_661_ = lean_ctor_get(v___x_652_, 9);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_652_, 5);
lean_dec(v_unused_708_);
v___x_663_ = v___x_652_;
v_isShared_664_ = v_isSharedCheck_707_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snapshotTasks_661_);
lean_inc(v_infoState_660_);
lean_inc(v_messages_659_);
lean_inc(v_recordedDeps_658_);
lean_inc(v_traceState_657_);
lean_inc(v_auxDeclNGen_656_);
lean_inc(v_ngen_655_);
lean_inc(v_nextMacroScope_654_);
lean_inc(v_env_653_);
lean_dec(v___x_652_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_707_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_inc(v___y_636_);
v___x_665_ = l_Lean_markMeta(v_env_653_, v___y_636_);
v___x_666_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 5, v___x_666_);
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_nextMacroScope_654_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_ngen_655_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_auxDeclNGen_656_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_traceState_657_);
lean_ctor_set(v_reuseFailAlloc_706_, 5, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_706_, 6, v_recordedDeps_658_);
lean_ctor_set(v_reuseFailAlloc_706_, 7, v_messages_659_);
lean_ctor_set(v_reuseFailAlloc_706_, 8, v_infoState_660_);
lean_ctor_set(v_reuseFailAlloc_706_, 9, v_snapshotTasks_661_);
v___x_668_ = v_reuseFailAlloc_706_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v_mctx_671_; lean_object* v_zetaDeltaFVarIds_672_; lean_object* v_postponed_673_; lean_object* v_diag_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_704_; 
v___x_669_ = lean_st_ref_put(v___y_642_, v___x_668_);
v___x_670_ = lean_st_ref_take(v___y_640_);
v_mctx_671_ = lean_ctor_get(v___x_670_, 0);
v_zetaDeltaFVarIds_672_ = lean_ctor_get(v___x_670_, 2);
v_postponed_673_ = lean_ctor_get(v___x_670_, 3);
v_diag_674_ = lean_ctor_get(v___x_670_, 4);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_670_, 1);
lean_dec(v_unused_705_);
v___x_676_ = v___x_670_;
v_isShared_677_ = v_isSharedCheck_704_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_diag_674_);
lean_inc(v_postponed_673_);
lean_inc(v_zetaDeltaFVarIds_672_);
lean_inc(v_mctx_671_);
lean_dec(v___x_670_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_704_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_mctx_671_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_zetaDeltaFVarIds_672_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_postponed_673_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_diag_674_);
v___x_680_ = v_reuseFailAlloc_703_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_env_683_; lean_object* v_checked_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_681_ = lean_st_ref_put(v___y_640_, v___x_680_);
v___x_682_ = lean_st_ref_get(v___y_642_);
v_env_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref(v_env_683_);
lean_dec(v___x_682_);
v_checked_684_ = lean_ctor_get(v_env_683_, 2);
lean_inc_ref(v_checked_684_);
lean_dec_ref(v_env_683_);
v___x_685_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_686_ = l_Lean_traceBlock___redArg(v___x_685_, v_checked_684_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_toCold_687_; uint8_t v_isRecordingDeps_688_; lean_object* v_options_689_; uint8_t v___x_690_; uint8_t v___x_691_; 
lean_dec_ref_known(v___x_686_, 1);
v_toCold_687_ = lean_ctor_get(v___y_641_, 0);
v_isRecordingDeps_688_ = lean_ctor_get_uint8(v___y_641_, sizeof(void*)*3 + 4);
v_options_689_ = lean_ctor_get(v_toCold_687_, 2);
v___x_690_ = 1;
v___x_691_ = 0;
if (v_isRecordingDeps_688_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = l_Lean_Elab_async;
lean_inc_ref(v_options_689_);
v___x_693_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v_options_689_, v___x_692_, v_isRecordingDeps_688_);
v___y_616_ = v___x_651_;
v___y_617_ = v___y_639_;
v___y_618_ = v___y_636_;
v___y_619_ = v___x_666_;
v___y_620_ = v___x_691_;
v___y_621_ = v___y_641_;
v___y_622_ = v___x_690_;
v___y_623_ = v___y_642_;
v___y_624_ = v___y_640_;
v___y_625_ = v___x_693_;
goto v___jp_615_;
}
else
{
lean_object* v___x_694_; 
lean_inc_ref(v_options_689_);
v___x_694_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_689_);
v___y_616_ = v___x_651_;
v___y_617_ = v___y_639_;
v___y_618_ = v___y_636_;
v___y_619_ = v___x_666_;
v___y_620_ = v___x_691_;
v___y_621_ = v___y_641_;
v___y_622_ = v___x_690_;
v___y_623_ = v___y_642_;
v___y_624_ = v___y_640_;
v___y_625_ = v___x_694_;
goto v___jp_615_;
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref_known(v___x_651_, 1);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_636_);
v_a_695_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_686_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_686_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
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
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_a_644_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
v_a_709_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_645_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_645_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_checkType_269_);
v_a_717_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_643_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_643_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
v___jp_725_:
{
lean_object* v___x_726_; lean_object* v_env_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_st_ref_get(v___y_275_);
v_env_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_env_727_);
lean_dec(v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_729_ = l_Lean_Core_mkFreshUserName(v___x_728_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = l_Lean_mkPrivateName(v_env_727_, v_a_730_);
lean_dec_ref(v_env_727_);
v___x_732_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_271_, v___y_273_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_params_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_n(v_a_733_, 2);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_735_ = l_Lean_collectLevelParams(v___x_734_, v_a_733_);
v_params_736_ = lean_ctor_get(v___x_735_, 2);
lean_inc_ref(v_params_736_);
lean_dec_ref(v___x_735_);
v___x_737_ = lean_box(0);
v___x_738_ = l_Lean_Expr_hasMVar(v_a_733_);
if (v___x_738_ == 0)
{
v___y_635_ = v_a_733_;
v___y_636_ = v___x_731_;
v___y_637_ = v___x_737_;
v___y_638_ = v_params_736_;
v___y_639_ = v___y_272_;
v___y_640_ = v___y_273_;
v___y_641_ = v___y_274_;
v___y_642_ = v___y_275_;
goto v___jp_634_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_739_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_733_);
v___x_740_ = l_Lean_indentExpr(v_a_733_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_741_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_dec_ref_known(v___x_742_, 1);
v___y_635_ = v_a_733_;
v___y_636_ = v___x_731_;
v___y_637_ = v___x_737_;
v___y_638_ = v_params_736_;
v___y_639_ = v___y_272_;
v___y_640_ = v___y_273_;
v___y_641_ = v___y_274_;
v___y_642_ = v___y_275_;
goto v___jp_634_;
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_params_736_);
lean_dec(v_a_733_);
lean_dec(v___x_731_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_checkType_269_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v___x_731_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_checkType_269_);
v_a_751_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_732_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_732_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_env_727_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_value_271_);
lean_dec_ref(v_checkType_269_);
v_a_759_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_729_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_729_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
v___jp_767_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_mctx_781_; lean_object* v_zetaDeltaFVarIds_782_; lean_object* v_postponed_783_; lean_object* v_diag_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_793_; 
v___x_777_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_778_, 0, v___y_776_);
lean_ctor_set(v___x_778_, 1, v_nextMacroScope_768_);
lean_ctor_set(v___x_778_, 2, v_ngen_769_);
lean_ctor_set(v___x_778_, 3, v_auxDeclNGen_770_);
lean_ctor_set(v___x_778_, 4, v_traceState_771_);
lean_ctor_set(v___x_778_, 5, v___x_777_);
lean_ctor_set(v___x_778_, 6, v_recordedDeps_772_);
lean_ctor_set(v___x_778_, 7, v_messages_773_);
lean_ctor_set(v___x_778_, 8, v_infoState_774_);
lean_ctor_set(v___x_778_, 9, v_snapshotTasks_775_);
v___x_779_ = lean_st_ref_put(v___y_275_, v___x_778_);
v___x_780_ = lean_st_ref_take(v___y_273_);
v_mctx_781_ = lean_ctor_get(v___x_780_, 0);
v_zetaDeltaFVarIds_782_ = lean_ctor_get(v___x_780_, 2);
v_postponed_783_ = lean_ctor_get(v___x_780_, 3);
v_diag_784_ = lean_ctor_get(v___x_780_, 4);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v___x_780_, 1);
lean_dec(v_unused_794_);
v___x_786_ = v___x_780_;
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_diag_784_);
lean_inc(v_postponed_783_);
lean_inc(v_zetaDeltaFVarIds_782_);
lean_inc(v_mctx_781_);
lean_dec(v___x_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_mctx_781_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_zetaDeltaFVarIds_782_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v_postponed_783_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_diag_784_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_st_ref_put(v___y_273_, v___x_790_);
goto v___jp_725_;
}
}
}
v___jp_796_:
{
lean_object* v___x_797_; lean_object* v_env_798_; lean_object* v_nextMacroScope_799_; lean_object* v_ngen_800_; lean_object* v_auxDeclNGen_801_; lean_object* v_traceState_802_; lean_object* v_recordedDeps_803_; lean_object* v_messages_804_; lean_object* v_infoState_805_; lean_object* v_snapshotTasks_806_; lean_object* v___x_807_; 
v___x_797_ = lean_st_ref_take(v___y_275_);
v_env_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref_n(v_env_798_, 2);
v_nextMacroScope_799_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_nextMacroScope_799_);
v_ngen_800_ = lean_ctor_get(v___x_797_, 2);
lean_inc_ref(v_ngen_800_);
v_auxDeclNGen_801_ = lean_ctor_get(v___x_797_, 3);
lean_inc_ref(v_auxDeclNGen_801_);
v_traceState_802_ = lean_ctor_get(v___x_797_, 4);
lean_inc_ref(v_traceState_802_);
v_recordedDeps_803_ = lean_ctor_get(v___x_797_, 6);
lean_inc_ref(v_recordedDeps_803_);
v_messages_804_ = lean_ctor_get(v___x_797_, 7);
lean_inc_ref(v_messages_804_);
v_infoState_805_ = lean_ctor_get(v___x_797_, 8);
lean_inc_ref(v_infoState_805_);
v_snapshotTasks_806_ = lean_ctor_get(v___x_797_, 9);
lean_inc_ref(v_snapshotTasks_806_);
lean_dec(v___x_797_);
v___x_807_ = l_Lean_Environment_importEnv_x3f(v_env_798_);
if (lean_obj_tag(v___x_807_) == 0)
{
v_nextMacroScope_768_ = v_nextMacroScope_799_;
v_ngen_769_ = v_ngen_800_;
v_auxDeclNGen_770_ = v_auxDeclNGen_801_;
v_traceState_771_ = v_traceState_802_;
v_recordedDeps_772_ = v_recordedDeps_803_;
v_messages_773_ = v_messages_804_;
v_infoState_774_ = v_infoState_805_;
v_snapshotTasks_775_ = v_snapshotTasks_806_;
v___y_776_ = v_env_798_;
goto v___jp_767_;
}
else
{
lean_object* v_val_808_; 
lean_dec_ref(v_env_798_);
v_val_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___x_807_, 1);
v_nextMacroScope_768_ = v_nextMacroScope_799_;
v_ngen_769_ = v_ngen_800_;
v_auxDeclNGen_770_ = v_auxDeclNGen_801_;
v_traceState_771_ = v_traceState_802_;
v_recordedDeps_772_ = v_recordedDeps_803_;
v_messages_773_ = v_messages_804_;
v_infoState_774_ = v_infoState_805_;
v_snapshotTasks_775_ = v_snapshotTasks_806_;
v___y_776_ = v_val_808_;
goto v___jp_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_817_, lean_object* v_checkType_818_, lean_object* v_safety_819_, lean_object* v_value_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v_checkMeta_boxed_826_; uint8_t v_safety_boxed_827_; lean_object* v_res_828_; 
v_checkMeta_boxed_826_ = lean_unbox(v_checkMeta_817_);
v_safety_boxed_827_ = lean_unbox(v_safety_819_);
v_res_828_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_826_, v_checkType_818_, v_safety_boxed_827_, v_value_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(lean_object* v_env_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_nextMacroScope_834_; lean_object* v_ngen_835_; lean_object* v_auxDeclNGen_836_; lean_object* v_traceState_837_; lean_object* v_recordedDeps_838_; lean_object* v_messages_839_; lean_object* v_infoState_840_; lean_object* v_snapshotTasks_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_867_; 
v___x_833_ = lean_st_ref_take(v___y_831_);
v_nextMacroScope_834_ = lean_ctor_get(v___x_833_, 1);
v_ngen_835_ = lean_ctor_get(v___x_833_, 2);
v_auxDeclNGen_836_ = lean_ctor_get(v___x_833_, 3);
v_traceState_837_ = lean_ctor_get(v___x_833_, 4);
v_recordedDeps_838_ = lean_ctor_get(v___x_833_, 6);
v_messages_839_ = lean_ctor_get(v___x_833_, 7);
v_infoState_840_ = lean_ctor_get(v___x_833_, 8);
v_snapshotTasks_841_ = lean_ctor_get(v___x_833_, 9);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_868_ = lean_ctor_get(v___x_833_, 5);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v___x_833_, 0);
lean_dec(v_unused_869_);
v___x_843_ = v___x_833_;
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snapshotTasks_841_);
lean_inc(v_infoState_840_);
lean_inc(v_messages_839_);
lean_inc(v_recordedDeps_838_);
lean_inc(v_traceState_837_);
lean_inc(v_auxDeclNGen_836_);
lean_inc(v_ngen_835_);
lean_inc(v_nextMacroScope_834_);
lean_dec(v___x_833_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 5, v___x_845_);
lean_ctor_set(v___x_843_, 0, v_env_829_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_env_829_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_nextMacroScope_834_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_ngen_835_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_auxDeclNGen_836_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_traceState_837_);
lean_ctor_set(v_reuseFailAlloc_866_, 5, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_866_, 6, v_recordedDeps_838_);
lean_ctor_set(v_reuseFailAlloc_866_, 7, v_messages_839_);
lean_ctor_set(v_reuseFailAlloc_866_, 8, v_infoState_840_);
lean_ctor_set(v_reuseFailAlloc_866_, 9, v_snapshotTasks_841_);
v___x_847_ = v_reuseFailAlloc_866_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_mctx_850_; lean_object* v_zetaDeltaFVarIds_851_; lean_object* v_postponed_852_; lean_object* v_diag_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_864_; 
v___x_848_ = lean_st_ref_put(v___y_831_, v___x_847_);
v___x_849_ = lean_st_ref_take(v___y_830_);
v_mctx_850_ = lean_ctor_get(v___x_849_, 0);
v_zetaDeltaFVarIds_851_ = lean_ctor_get(v___x_849_, 2);
v_postponed_852_ = lean_ctor_get(v___x_849_, 3);
v_diag_853_ = lean_ctor_get(v___x_849_, 4);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v___x_849_, 1);
lean_dec(v_unused_865_);
v___x_855_ = v___x_849_;
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_diag_853_);
lean_inc(v_postponed_852_);
lean_inc(v_zetaDeltaFVarIds_851_);
lean_inc(v_mctx_850_);
lean_dec(v___x_849_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = lean_box(0);
v___x_858_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_mctx_850_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_zetaDeltaFVarIds_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_postponed_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v_diag_853_);
v___x_860_ = v_reuseFailAlloc_863_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_st_ref_put(v___y_830_, v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_857_);
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg___boxed(lean_object* v_env_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec(v___y_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; lean_object* v_env_883_; lean_object* v_a_885_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_882_ = lean_st_ref_get(v___y_880_);
v_env_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc_ref(v_env_883_);
lean_dec(v___x_882_);
v___x_895_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_875_, v___y_878_, v___y_880_);
lean_dec_ref(v___x_895_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
v___x_896_ = lean_apply_5(v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_883_, v___y_878_, v___y_880_);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_898_, 0);
lean_dec(v_unused_906_);
v___x_900_ = v___x_898_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_dec(v___x_898_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v_a_897_);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_897_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_907_; 
v_a_907_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_896_, 1);
v_a_885_ = v_a_907_;
goto v___jp_884_;
}
v___jp_884_:
{
lean_object* v___x_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v___x_886_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_883_, v___y_878_, v___y_880_);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_886_, 0);
lean_dec(v_unused_894_);
v___x_888_ = v___x_886_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_dec(v___x_886_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 1);
lean_ctor_set(v___x_888_, 0, v_a_885_);
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_885_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_908_, lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_908_, v_x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_916_, lean_object* v_checkType_917_, uint8_t v_safety_918_, uint8_t v_checkMeta_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v_env_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_925_ = lean_box(v_checkMeta_919_);
v___x_926_ = lean_box(v_safety_918_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_927_, 0, v___x_925_);
lean_closure_set(v___f_927_, 1, v_checkType_917_);
lean_closure_set(v___f_927_, 2, v___x_926_);
lean_closure_set(v___f_927_, 3, v_value_916_);
v___x_928_ = lean_st_ref_get(v_a_923_);
v_env_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_ref(v_env_929_);
lean_dec(v___x_928_);
v___x_930_ = l_Lean_Environment_unlockAsync(v_env_929_);
v___x_931_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_930_, v___f_927_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_932_, lean_object* v_checkType_933_, lean_object* v_safety_934_, lean_object* v_checkMeta_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
uint8_t v_safety_boxed_941_; uint8_t v_checkMeta_boxed_942_; lean_object* v_res_943_; 
v_safety_boxed_941_ = lean_unbox(v_safety_934_);
v_checkMeta_boxed_942_ = lean_unbox(v_checkMeta_935_);
v_res_943_ = l_Lean_Meta_evalExprCore___redArg(v_value_932_, v_checkType_933_, v_safety_boxed_941_, v_checkMeta_boxed_942_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_944_, lean_object* v_value_945_, lean_object* v_checkType_946_, uint8_t v_safety_947_, uint8_t v_checkMeta_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Meta_evalExprCore___redArg(v_value_945_, v_checkType_946_, v_safety_947_, v_checkMeta_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_955_, lean_object* v_value_956_, lean_object* v_checkType_957_, lean_object* v_safety_958_, lean_object* v_checkMeta_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
uint8_t v_safety_boxed_965_; uint8_t v_checkMeta_boxed_966_; lean_object* v_res_967_; 
v_safety_boxed_965_ = lean_unbox(v_safety_958_);
v_checkMeta_boxed_966_ = lean_unbox(v_checkMeta_959_);
v_res_967_ = l_Lean_Meta_evalExprCore(v_00_u03b1_955_, v_value_956_, v_checkType_957_, v_safety_boxed_965_, v_checkMeta_boxed_966_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_00_u03b2_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg(){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg___boxed(lean_object* v___dummy_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg();
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_00_u03b2_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object* v_00_u03b1_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object* v_00_u03b1_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_00_u03b1_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_00_u03b1_990_, lean_object* v_constName_991_, uint8_t v_checkMeta_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v_constName_991_, v_checkMeta_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_00_u03b1_999_, lean_object* v_constName_1000_, lean_object* v_checkMeta_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v_checkMeta_boxed_1007_; lean_object* v_res_1008_; 
v_checkMeta_boxed_1007_ = lean_unbox(v_checkMeta_1001_);
v_res_1008_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(v_00_u03b1_999_, v_constName_1000_, v_checkMeta_boxed_1007_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_1009_, lean_object* v_msg_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_1017_, v_msg_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_1025_, lean_object* v_env_1026_, lean_object* v_x_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_1026_, v_x_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_env_1035_, lean_object* v_x_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_1034_, v_env_1035_, v_x_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(lean_object* v_00_u03b1_1043_, lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v_x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_x_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(v_00_u03b1_1051_, v_x_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12(lean_object* v_env_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_1059_, v___y_1061_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___boxed(lean_object* v_env_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12(v_env_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1076_, lean_object* v_type_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_whnfD(v_type_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1097_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
uint8_t v___x_1088_; 
v___x_1088_ = l_Lean_Expr_isConstOf(v_a_1084_, v_typeName_1076_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_del_object(v___x_1086_);
v___x_1089_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1090_ = l_Lean_indentExpr(v_a_1084_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1091_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_a_1084_);
v___x_1093_ = lean_box(0);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1093_);
v___x_1095_ = v___x_1086_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1083_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1083_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1106_, lean_object* v_type_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1106_, v_type_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v_typeName_1106_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1114_, lean_object* v_value_1115_, uint8_t v_safety_1116_, uint8_t v_checkMeta_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1123_, 0, v_typeName_1114_);
v___x_1124_ = l_Lean_Meta_evalExprCore___redArg(v_value_1115_, v___f_1123_, v_safety_1116_, v_checkMeta_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1125_, lean_object* v_value_1126_, lean_object* v_safety_1127_, lean_object* v_checkMeta_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
uint8_t v_safety_boxed_1134_; uint8_t v_checkMeta_boxed_1135_; lean_object* v_res_1136_; 
v_safety_boxed_1134_ = lean_unbox(v_safety_1127_);
v_checkMeta_boxed_1135_ = lean_unbox(v_checkMeta_1128_);
v_res_1136_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1125_, v_value_1126_, v_safety_boxed_1134_, v_checkMeta_boxed_1135_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1137_, lean_object* v_typeName_1138_, lean_object* v_value_1139_, uint8_t v_safety_1140_, uint8_t v_checkMeta_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1138_, v_value_1139_, v_safety_1140_, v_checkMeta_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_typeName_1149_, lean_object* v_value_1150_, lean_object* v_safety_1151_, lean_object* v_checkMeta_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
uint8_t v_safety_boxed_1158_; uint8_t v_checkMeta_boxed_1159_; lean_object* v_res_1160_; 
v_safety_boxed_1158_ = lean_unbox(v_safety_1151_);
v_checkMeta_boxed_1159_ = lean_unbox(v_checkMeta_1152_);
v_res_1160_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1148_, v_typeName_1149_, v_value_1150_, v_safety_boxed_1158_, v_checkMeta_boxed_1159_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
return v_res_1160_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1166_, lean_object* v_type_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
lean_inc_ref(v_expectedType_1166_);
lean_inc_ref(v_type_1167_);
v___x_1173_ = l_Lean_Meta_isExprDefEq(v_type_1167_, v_expectedType_1166_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1198_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1198_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1198_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_unbox(v_a_1174_);
lean_dec(v_a_1174_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_del_object(v___x_1176_);
v___x_1179_ = lean_box(0);
v___x_1180_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1181_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1167_, v_expectedType_1166_, v___x_1179_, v___x_1180_, v___y_1168_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_a_1182_);
v___x_1185_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1184_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1185_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1181_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1181_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec_ref(v_type_1167_);
lean_dec_ref(v_expectedType_1166_);
v___x_1194_ = lean_box(0);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1194_);
v___x_1196_ = v___x_1176_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_type_1167_);
lean_dec_ref(v_expectedType_1166_);
v_a_1199_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1173_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1173_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1207_, lean_object* v_type_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1207_, v_type_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1215_, lean_object* v_value_1216_, uint8_t v_safety_1217_, uint8_t v_checkMeta_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___f_1224_; lean_object* v___x_1225_; 
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1224_, 0, v_expectedType_1215_);
v___x_1225_ = l_Lean_Meta_evalExprCore___redArg(v_value_1216_, v___f_1224_, v_safety_1217_, v_checkMeta_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1226_, lean_object* v_value_1227_, lean_object* v_safety_1228_, lean_object* v_checkMeta_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
uint8_t v_safety_boxed_1235_; uint8_t v_checkMeta_boxed_1236_; lean_object* v_res_1237_; 
v_safety_boxed_1235_ = lean_unbox(v_safety_1228_);
v_checkMeta_boxed_1236_ = lean_unbox(v_checkMeta_1229_);
v_res_1237_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1226_, v_value_1227_, v_safety_boxed_1235_, v_checkMeta_boxed_1236_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1238_, lean_object* v_expectedType_1239_, lean_object* v_value_1240_, uint8_t v_safety_1241_, uint8_t v_checkMeta_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1239_, v_value_1240_, v_safety_1241_, v_checkMeta_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_expectedType_1250_, lean_object* v_value_1251_, lean_object* v_safety_1252_, lean_object* v_checkMeta_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
uint8_t v_safety_boxed_1259_; uint8_t v_checkMeta_boxed_1260_; lean_object* v_res_1261_; 
v_safety_boxed_1259_ = lean_unbox(v_safety_1252_);
v_checkMeta_boxed_1260_ = lean_unbox(v_checkMeta_1253_);
v_res_1261_ = l_Lean_Meta_evalExpr(v_00_u03b1_1249_, v_expectedType_1250_, v_value_1251_, v_safety_boxed_1259_, v_checkMeta_boxed_1260_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
return v_res_1261_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Eval(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Eval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Eval(builtin);
}
#ifdef __cplusplus
}
#endif

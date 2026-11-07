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
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14;
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
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_box(0);
v___x_254_ = lean_unsigned_to_nat(16u);
v___x_255_ = lean_mk_array(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9));
v___x_262_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_ctor_set(v___x_263_, 2, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
lean_ctor_set(v___x_269_, 2, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_270_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13);
v___x_271_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
v___x_272_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_273_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_274_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_271_);
lean_ctor_set(v___x_274_, 3, v___x_272_);
lean_ctor_set(v___x_274_, 4, v___x_272_);
lean_ctor_set(v___x_274_, 5, v___x_272_);
lean_ctor_set(v___x_274_, 6, v___x_272_);
lean_ctor_set(v___x_274_, 7, v___x_270_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_275_, lean_object* v_checkType_276_, uint8_t v_safety_277_, lean_object* v_value_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
uint8_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; uint16_t v___y_290_; uint8_t v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_340_; lean_object* v___y_341_; uint16_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; uint8_t v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; uint8_t v___y_349_; lean_object* v___y_350_; uint8_t v___y_351_; lean_object* v___y_352_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; uint16_t v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; uint8_t v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; uint8_t v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; uint8_t v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; uint8_t v___y_409_; lean_object* v___y_410_; uint16_t v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; uint16_t v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; uint8_t v___y_468_; uint8_t v___y_469_; lean_object* v___y_470_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; uint16_t v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; uint8_t v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; uint8_t v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; uint8_t v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; uint16_t v___y_532_; uint8_t v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; uint16_t v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; uint8_t v___y_582_; lean_object* v___y_583_; uint8_t v___y_584_; lean_object* v___y_585_; uint8_t v___y_586_; lean_object* v___y_587_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; uint16_t v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; uint8_t v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; uint8_t v___y_619_; lean_object* v___y_620_; uint8_t v___y_621_; uint8_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; uint8_t v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v_nextMacroScope_781_; lean_object* v_ngen_782_; lean_object* v_auxDeclNGen_783_; lean_object* v_traceState_784_; lean_object* v_recordedDeps_785_; lean_object* v_messages_786_; lean_object* v_infoState_787_; lean_object* v_snapshotTasks_788_; lean_object* v___y_789_; lean_object* v___x_808_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_808_ = lean_st_ref_get(v___y_282_);
lean_inc_ref(v_value_278_);
v___x_822_ = l_Lean_Expr_getUsedConstants(v_value_278_);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_array_get_size(v___x_822_);
v___x_825_ = lean_nat_dec_lt(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec_ref(v___x_822_);
lean_dec(v___x_808_);
goto v___jp_809_;
}
else
{
if (v___x_825_ == 0)
{
lean_dec_ref(v___x_822_);
lean_dec(v___x_808_);
goto v___jp_809_;
}
else
{
lean_object* v_env_826_; size_t v___x_827_; size_t v___x_828_; uint8_t v___x_829_; 
v_env_826_ = lean_ctor_get(v___x_808_, 0);
lean_inc_ref(v_env_826_);
lean_dec(v___x_808_);
v___x_827_ = ((size_t)0ULL);
v___x_828_ = lean_usize_of_nat(v___x_824_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_826_, v___x_824_, v___x_822_, v___x_827_, v___x_828_);
lean_dec_ref(v___x_822_);
lean_dec_ref(v_env_826_);
if (v___x_829_ == 0)
{
goto v___jp_809_;
}
else
{
goto v___jp_737_;
}
}
}
v___jp_284_:
{
lean_object* v_toCold_296_; lean_object* v_currRecDepth_297_; lean_object* v_ref_298_; uint8_t v_suppressElabErrors_299_; uint8_t v_checkDeprecated_300_; uint8_t v_isRecordingDeps_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_338_; 
v_toCold_296_ = lean_ctor_get(v___y_294_, 0);
v_currRecDepth_297_ = lean_ctor_get(v___y_294_, 1);
v_ref_298_ = lean_ctor_get(v___y_294_, 2);
v_suppressElabErrors_299_ = lean_ctor_get_uint8(v___y_294_, sizeof(void*)*3 + 2);
v_checkDeprecated_300_ = lean_ctor_get_uint8(v___y_294_, sizeof(void*)*3 + 3);
v_isRecordingDeps_301_ = lean_ctor_get_uint8(v___y_294_, sizeof(void*)*3 + 4);
v_isSharedCheck_338_ = !lean_is_exclusive(v___y_294_);
if (v_isSharedCheck_338_ == 0)
{
v___x_303_ = v___y_294_;
v_isShared_304_ = v_isSharedCheck_338_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_ref_298_);
lean_inc(v_currRecDepth_297_);
lean_inc(v_toCold_296_);
lean_dec(v___y_294_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_338_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_fileName_305_; lean_object* v_fileMap_306_; lean_object* v_currNamespace_307_; lean_object* v_openDecls_308_; lean_object* v_initHeartbeats_309_; lean_object* v_maxHeartbeats_310_; lean_object* v_quotContext_311_; lean_object* v_currMacroScope_312_; lean_object* v_cancelTk_x3f_313_; lean_object* v_inheritedTraceOptions_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_335_; 
v_fileName_305_ = lean_ctor_get(v_toCold_296_, 0);
v_fileMap_306_ = lean_ctor_get(v_toCold_296_, 1);
v_currNamespace_307_ = lean_ctor_get(v_toCold_296_, 4);
v_openDecls_308_ = lean_ctor_get(v_toCold_296_, 5);
v_initHeartbeats_309_ = lean_ctor_get(v_toCold_296_, 6);
v_maxHeartbeats_310_ = lean_ctor_get(v_toCold_296_, 7);
v_quotContext_311_ = lean_ctor_get(v_toCold_296_, 8);
v_currMacroScope_312_ = lean_ctor_get(v_toCold_296_, 9);
v_cancelTk_x3f_313_ = lean_ctor_get(v_toCold_296_, 10);
v_inheritedTraceOptions_314_ = lean_ctor_get(v_toCold_296_, 11);
v_isSharedCheck_335_ = !lean_is_exclusive(v_toCold_296_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; lean_object* v_unused_337_; 
v_unused_336_ = lean_ctor_get(v_toCold_296_, 3);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_toCold_296_, 2);
lean_dec(v_unused_337_);
v___x_316_ = v_toCold_296_;
v_isShared_317_ = v_isSharedCheck_335_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_inheritedTraceOptions_314_);
lean_inc(v_cancelTk_x3f_313_);
lean_inc(v_currMacroScope_312_);
lean_inc(v_quotContext_311_);
lean_inc(v_maxHeartbeats_310_);
lean_inc(v_initHeartbeats_309_);
lean_inc(v_openDecls_308_);
lean_inc(v_currNamespace_307_);
lean_inc(v_fileMap_306_);
lean_inc(v_fileName_305_);
lean_dec(v_toCold_296_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_335_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_289_, v___y_287_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 3, v___x_318_);
lean_ctor_set(v___x_316_, 2, v___y_289_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_fileName_305_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_fileMap_306_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v___y_289_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_currNamespace_307_);
lean_ctor_set(v_reuseFailAlloc_334_, 5, v_openDecls_308_);
lean_ctor_set(v_reuseFailAlloc_334_, 6, v_initHeartbeats_309_);
lean_ctor_set(v_reuseFailAlloc_334_, 7, v_maxHeartbeats_310_);
lean_ctor_set(v_reuseFailAlloc_334_, 8, v_quotContext_311_);
lean_ctor_set(v_reuseFailAlloc_334_, 9, v_currMacroScope_312_);
lean_ctor_set(v_reuseFailAlloc_334_, 10, v_cancelTk_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_334_, 11, v_inheritedTraceOptions_314_);
v___x_320_ = v_reuseFailAlloc_334_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_320_);
v___x_322_ = v___x_303_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_currRecDepth_297_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_ref_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*3 + 2, v_suppressElabErrors_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*3 + 3, v_checkDeprecated_300_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*3 + 4, v_isRecordingDeps_301_);
v___x_322_ = v_reuseFailAlloc_333_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
lean_ctor_set_uint16(v___x_322_, sizeof(void*)*3, v___y_290_);
v___x_323_ = l_Lean_addAndCompile(v___y_286_, v___y_285_, v___y_291_, v___x_322_, v___y_295_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v___x_324_; 
lean_dec_ref_known(v___x_323_, 1);
v___x_324_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v___y_292_, v_checkMeta_275_, v___y_288_, v___y_293_, v___x_322_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___x_322_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_288_);
return v___x_324_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v___x_322_);
lean_dec(v___y_295_);
lean_dec(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_288_);
v_a_325_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_323_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
}
v___jp_339_:
{
lean_object* v___x_353_; lean_object* v_env_354_; lean_object* v_nextMacroScope_355_; lean_object* v_ngen_356_; lean_object* v_auxDeclNGen_357_; lean_object* v_traceState_358_; lean_object* v_recordedDeps_359_; lean_object* v_messages_360_; lean_object* v_infoState_361_; lean_object* v_snapshotTasks_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_371_; 
v___x_353_ = lean_st_ref_take(v___y_341_);
v_env_354_ = lean_ctor_get(v___x_353_, 0);
v_nextMacroScope_355_ = lean_ctor_get(v___x_353_, 1);
v_ngen_356_ = lean_ctor_get(v___x_353_, 2);
v_auxDeclNGen_357_ = lean_ctor_get(v___x_353_, 3);
v_traceState_358_ = lean_ctor_get(v___x_353_, 4);
v_recordedDeps_359_ = lean_ctor_get(v___x_353_, 6);
v_messages_360_ = lean_ctor_get(v___x_353_, 7);
v_infoState_361_ = lean_ctor_get(v___x_353_, 8);
v_snapshotTasks_362_ = lean_ctor_get(v___x_353_, 9);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_353_, 5);
lean_dec(v_unused_372_);
v___x_364_ = v___x_353_;
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_snapshotTasks_362_);
lean_inc(v_infoState_361_);
lean_inc(v_messages_360_);
lean_inc(v_recordedDeps_359_);
lean_inc(v_traceState_358_);
lean_inc(v_auxDeclNGen_357_);
lean_inc(v_ngen_356_);
lean_inc(v_nextMacroScope_355_);
lean_inc(v_env_354_);
lean_dec(v___x_353_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = l_Lean_Kernel_enableDiag(v_env_354_, v___y_349_);
lean_inc_ref(v___y_350_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 5, v___y_350_);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_nextMacroScope_355_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_ngen_356_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_auxDeclNGen_357_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_traceState_358_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v___y_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_recordedDeps_359_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_messages_360_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_infoState_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 9, v_snapshotTasks_362_);
v___x_368_ = v_reuseFailAlloc_370_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; 
v___x_369_ = lean_st_ref_put(v___y_341_, v___x_368_);
v___y_285_ = v___y_345_;
v___y_286_ = v___y_340_;
v___y_287_ = v___y_346_;
v___y_288_ = v___y_347_;
v___y_289_ = v___y_348_;
v___y_290_ = v___y_342_;
v___y_291_ = v___y_351_;
v___y_292_ = v___y_344_;
v___y_293_ = v___y_352_;
v___y_294_ = v___y_343_;
v___y_295_ = v___y_341_;
goto v___jp_284_;
}
}
}
v___jp_373_:
{
if (v___y_387_ == 0)
{
if (v___y_376_ == 0)
{
v___y_285_ = v___y_380_;
v___y_286_ = v___y_374_;
v___y_287_ = v___y_381_;
v___y_288_ = v___y_382_;
v___y_289_ = v___y_383_;
v___y_290_ = v___y_377_;
v___y_291_ = v___y_385_;
v___y_292_ = v___y_379_;
v___y_293_ = v___y_386_;
v___y_294_ = v___y_378_;
v___y_295_ = v___y_375_;
goto v___jp_284_;
}
else
{
v___y_340_ = v___y_374_;
v___y_341_ = v___y_375_;
v___y_342_ = v___y_377_;
v___y_343_ = v___y_378_;
v___y_344_ = v___y_379_;
v___y_345_ = v___y_380_;
v___y_346_ = v___y_381_;
v___y_347_ = v___y_382_;
v___y_348_ = v___y_383_;
v___y_349_ = v___y_387_;
v___y_350_ = v___y_384_;
v___y_351_ = v___y_385_;
v___y_352_ = v___y_386_;
goto v___jp_339_;
}
}
else
{
if (v___y_376_ == 0)
{
v___y_340_ = v___y_374_;
v___y_341_ = v___y_375_;
v___y_342_ = v___y_377_;
v___y_343_ = v___y_378_;
v___y_344_ = v___y_379_;
v___y_345_ = v___y_380_;
v___y_346_ = v___y_381_;
v___y_347_ = v___y_382_;
v___y_348_ = v___y_383_;
v___y_349_ = v___y_387_;
v___y_350_ = v___y_384_;
v___y_351_ = v___y_385_;
v___y_352_ = v___y_386_;
goto v___jp_339_;
}
else
{
v___y_285_ = v___y_380_;
v___y_286_ = v___y_374_;
v___y_287_ = v___y_381_;
v___y_288_ = v___y_382_;
v___y_289_ = v___y_383_;
v___y_290_ = v___y_377_;
v___y_291_ = v___y_385_;
v___y_292_ = v___y_379_;
v___y_293_ = v___y_386_;
v___y_294_ = v___y_378_;
v___y_295_ = v___y_375_;
goto v___jp_284_;
}
}
}
v___jp_388_:
{
uint16_t v___x_400_; lean_object* v___x_401_; lean_object* v_env_402_; uint8_t v___x_403_; uint16_t v___x_404_; uint16_t v___x_405_; uint16_t v___x_406_; uint8_t v___x_407_; 
v___x_400_ = l_Lean_OptionFlags_ofOptions(v___y_399_);
v___x_401_ = lean_st_ref_get(v___y_391_);
v_env_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_401_);
v___x_403_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_402_);
lean_dec_ref(v_env_402_);
v___x_404_ = 512;
v___x_405_ = lean_uint16_land(v___x_400_, v___x_404_);
v___x_406_ = 0;
v___x_407_ = lean_uint16_dec_eq(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
v___y_374_ = v___y_390_;
v___y_375_ = v___y_391_;
v___y_376_ = v___x_403_;
v___y_377_ = v___x_400_;
v___y_378_ = v___y_395_;
v___y_379_ = v___y_397_;
v___y_380_ = v___y_389_;
v___y_381_ = v___y_392_;
v___y_382_ = v___y_393_;
v___y_383_ = v___y_399_;
v___y_384_ = v___y_394_;
v___y_385_ = v___y_396_;
v___y_386_ = v___y_398_;
v___y_387_ = v___y_389_;
goto v___jp_373_;
}
else
{
v___y_374_ = v___y_390_;
v___y_375_ = v___y_391_;
v___y_376_ = v___x_403_;
v___y_377_ = v___x_400_;
v___y_378_ = v___y_395_;
v___y_379_ = v___y_397_;
v___y_380_ = v___y_389_;
v___y_381_ = v___y_392_;
v___y_382_ = v___y_393_;
v___y_383_ = v___y_399_;
v___y_384_ = v___y_394_;
v___y_385_ = v___y_396_;
v___y_386_ = v___y_398_;
v___y_387_ = v___y_396_;
goto v___jp_373_;
}
}
v___jp_408_:
{
lean_object* v_toCold_421_; lean_object* v_currRecDepth_422_; lean_object* v_ref_423_; uint8_t v_suppressElabErrors_424_; uint8_t v_checkDeprecated_425_; uint8_t v_isRecordingDeps_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_456_; 
v_toCold_421_ = lean_ctor_get(v___y_419_, 0);
v_currRecDepth_422_ = lean_ctor_get(v___y_419_, 1);
v_ref_423_ = lean_ctor_get(v___y_419_, 2);
v_suppressElabErrors_424_ = lean_ctor_get_uint8(v___y_419_, sizeof(void*)*3 + 2);
v_checkDeprecated_425_ = lean_ctor_get_uint8(v___y_419_, sizeof(void*)*3 + 3);
v_isRecordingDeps_426_ = lean_ctor_get_uint8(v___y_419_, sizeof(void*)*3 + 4);
v_isSharedCheck_456_ = !lean_is_exclusive(v___y_419_);
if (v_isSharedCheck_456_ == 0)
{
v___x_428_ = v___y_419_;
v_isShared_429_ = v_isSharedCheck_456_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_ref_423_);
lean_inc(v_currRecDepth_422_);
lean_inc(v_toCold_421_);
lean_dec(v___y_419_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_456_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_fileName_430_; lean_object* v_fileMap_431_; lean_object* v_currNamespace_432_; lean_object* v_openDecls_433_; lean_object* v_initHeartbeats_434_; lean_object* v_maxHeartbeats_435_; lean_object* v_quotContext_436_; lean_object* v_currMacroScope_437_; lean_object* v_cancelTk_x3f_438_; lean_object* v_inheritedTraceOptions_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_453_; 
v_fileName_430_ = lean_ctor_get(v_toCold_421_, 0);
v_fileMap_431_ = lean_ctor_get(v_toCold_421_, 1);
v_currNamespace_432_ = lean_ctor_get(v_toCold_421_, 4);
v_openDecls_433_ = lean_ctor_get(v_toCold_421_, 5);
v_initHeartbeats_434_ = lean_ctor_get(v_toCold_421_, 6);
v_maxHeartbeats_435_ = lean_ctor_get(v_toCold_421_, 7);
v_quotContext_436_ = lean_ctor_get(v_toCold_421_, 8);
v_currMacroScope_437_ = lean_ctor_get(v_toCold_421_, 9);
v_cancelTk_x3f_438_ = lean_ctor_get(v_toCold_421_, 10);
v_inheritedTraceOptions_439_ = lean_ctor_get(v_toCold_421_, 11);
v_isSharedCheck_453_ = !lean_is_exclusive(v_toCold_421_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; 
v_unused_454_ = lean_ctor_get(v_toCold_421_, 3);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_toCold_421_, 2);
lean_dec(v_unused_455_);
v___x_441_ = v_toCold_421_;
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_inheritedTraceOptions_439_);
lean_inc(v_cancelTk_x3f_438_);
lean_inc(v_currMacroScope_437_);
lean_inc(v_quotContext_436_);
lean_inc(v_maxHeartbeats_435_);
lean_inc(v_initHeartbeats_434_);
lean_inc(v_openDecls_433_);
lean_inc(v_currNamespace_432_);
lean_inc(v_fileMap_431_);
lean_inc(v_fileName_430_);
lean_dec(v_toCold_421_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_415_, v___y_412_);
lean_inc_ref(v___y_415_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 3, v___x_443_);
lean_ctor_set(v___x_441_, 2, v___y_415_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_fileName_430_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_fileMap_431_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v___y_415_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_currNamespace_432_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v_openDecls_433_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_initHeartbeats_434_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_maxHeartbeats_435_);
lean_ctor_set(v_reuseFailAlloc_452_, 8, v_quotContext_436_);
lean_ctor_set(v_reuseFailAlloc_452_, 9, v_currMacroScope_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 10, v_cancelTk_x3f_438_);
lean_ctor_set(v_reuseFailAlloc_452_, 11, v_inheritedTraceOptions_439_);
v___x_445_ = v_reuseFailAlloc_452_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_445_);
v___x_447_ = v___x_428_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_currRecDepth_422_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_ref_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_451_, sizeof(void*)*3 + 2, v_suppressElabErrors_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_451_, sizeof(void*)*3 + 3, v_checkDeprecated_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_451_, sizeof(void*)*3 + 4, v_isRecordingDeps_426_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_ctor_set_uint16(v___x_447_, sizeof(void*)*3, v___y_411_);
if (v_isRecordingDeps_426_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_449_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v___y_415_, v___x_448_, v___y_409_);
v___y_389_ = v___y_409_;
v___y_390_ = v___y_410_;
v___y_391_ = v___y_420_;
v___y_392_ = v___y_412_;
v___y_393_ = v___y_413_;
v___y_394_ = v___y_414_;
v___y_395_ = v___x_447_;
v___y_396_ = v___y_416_;
v___y_397_ = v___y_417_;
v___y_398_ = v___y_418_;
v___y_399_ = v___x_449_;
goto v___jp_388_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_415_);
v___y_389_ = v___y_409_;
v___y_390_ = v___y_410_;
v___y_391_ = v___y_420_;
v___y_392_ = v___y_412_;
v___y_393_ = v___y_413_;
v___y_394_ = v___y_414_;
v___y_395_ = v___x_447_;
v___y_396_ = v___y_416_;
v___y_397_ = v___y_417_;
v___y_398_ = v___y_418_;
v___y_399_ = v___x_450_;
goto v___jp_388_;
}
}
}
}
}
}
v___jp_457_:
{
lean_object* v___x_471_; lean_object* v_env_472_; lean_object* v_nextMacroScope_473_; lean_object* v_ngen_474_; lean_object* v_auxDeclNGen_475_; lean_object* v_traceState_476_; lean_object* v_recordedDeps_477_; lean_object* v_messages_478_; lean_object* v_infoState_479_; lean_object* v_snapshotTasks_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_489_; 
v___x_471_ = lean_st_ref_take(v___y_459_);
v_env_472_ = lean_ctor_get(v___x_471_, 0);
v_nextMacroScope_473_ = lean_ctor_get(v___x_471_, 1);
v_ngen_474_ = lean_ctor_get(v___x_471_, 2);
v_auxDeclNGen_475_ = lean_ctor_get(v___x_471_, 3);
v_traceState_476_ = lean_ctor_get(v___x_471_, 4);
v_recordedDeps_477_ = lean_ctor_get(v___x_471_, 6);
v_messages_478_ = lean_ctor_get(v___x_471_, 7);
v_infoState_479_ = lean_ctor_get(v___x_471_, 8);
v_snapshotTasks_480_ = lean_ctor_get(v___x_471_, 9);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v___x_471_, 5);
lean_dec(v_unused_490_);
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_489_;
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
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = l_Lean_Kernel_enableDiag(v_env_472_, v___y_469_);
lean_inc_ref(v___y_466_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 5, v___y_466_);
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_nextMacroScope_473_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_ngen_474_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_auxDeclNGen_475_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v_traceState_476_);
lean_ctor_set(v_reuseFailAlloc_488_, 5, v___y_466_);
lean_ctor_set(v_reuseFailAlloc_488_, 6, v_recordedDeps_477_);
lean_ctor_set(v_reuseFailAlloc_488_, 7, v_messages_478_);
lean_ctor_set(v_reuseFailAlloc_488_, 8, v_infoState_479_);
lean_ctor_set(v_reuseFailAlloc_488_, 9, v_snapshotTasks_480_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_st_ref_put(v___y_459_, v___x_486_);
v___y_409_ = v___y_461_;
v___y_410_ = v___y_458_;
v___y_411_ = v___y_462_;
v___y_412_ = v___y_463_;
v___y_413_ = v___y_465_;
v___y_414_ = v___y_466_;
v___y_415_ = v___y_467_;
v___y_416_ = v___y_468_;
v___y_417_ = v___y_460_;
v___y_418_ = v___y_470_;
v___y_419_ = v___y_464_;
v___y_420_ = v___y_459_;
goto v___jp_408_;
}
}
}
v___jp_491_:
{
if (v___y_505_ == 0)
{
if (v___y_502_ == 0)
{
v___y_409_ = v___y_495_;
v___y_410_ = v___y_492_;
v___y_411_ = v___y_496_;
v___y_412_ = v___y_497_;
v___y_413_ = v___y_499_;
v___y_414_ = v___y_500_;
v___y_415_ = v___y_501_;
v___y_416_ = v___y_503_;
v___y_417_ = v___y_494_;
v___y_418_ = v___y_504_;
v___y_419_ = v___y_498_;
v___y_420_ = v___y_493_;
goto v___jp_408_;
}
else
{
v___y_458_ = v___y_492_;
v___y_459_ = v___y_493_;
v___y_460_ = v___y_494_;
v___y_461_ = v___y_495_;
v___y_462_ = v___y_496_;
v___y_463_ = v___y_497_;
v___y_464_ = v___y_498_;
v___y_465_ = v___y_499_;
v___y_466_ = v___y_500_;
v___y_467_ = v___y_501_;
v___y_468_ = v___y_503_;
v___y_469_ = v___y_505_;
v___y_470_ = v___y_504_;
goto v___jp_457_;
}
}
else
{
if (v___y_502_ == 0)
{
v___y_458_ = v___y_492_;
v___y_459_ = v___y_493_;
v___y_460_ = v___y_494_;
v___y_461_ = v___y_495_;
v___y_462_ = v___y_496_;
v___y_463_ = v___y_497_;
v___y_464_ = v___y_498_;
v___y_465_ = v___y_499_;
v___y_466_ = v___y_500_;
v___y_467_ = v___y_501_;
v___y_468_ = v___y_503_;
v___y_469_ = v___y_505_;
v___y_470_ = v___y_504_;
goto v___jp_457_;
}
else
{
v___y_409_ = v___y_495_;
v___y_410_ = v___y_492_;
v___y_411_ = v___y_496_;
v___y_412_ = v___y_497_;
v___y_413_ = v___y_499_;
v___y_414_ = v___y_500_;
v___y_415_ = v___y_501_;
v___y_416_ = v___y_503_;
v___y_417_ = v___y_494_;
v___y_418_ = v___y_504_;
v___y_419_ = v___y_498_;
v___y_420_ = v___y_493_;
goto v___jp_408_;
}
}
}
v___jp_506_:
{
uint16_t v___x_518_; lean_object* v___x_519_; lean_object* v_env_520_; uint8_t v___x_521_; uint16_t v___x_522_; uint16_t v___x_523_; uint16_t v___x_524_; uint8_t v___x_525_; 
v___x_518_ = l_Lean_OptionFlags_ofOptions(v___y_517_);
v___x_519_ = lean_st_ref_get(v___y_513_);
v_env_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc_ref(v_env_520_);
lean_dec(v___x_519_);
v___x_521_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_520_);
lean_dec_ref(v_env_520_);
v___x_522_ = 512;
v___x_523_ = lean_uint16_land(v___x_518_, v___x_522_);
v___x_524_ = 0;
v___x_525_ = lean_uint16_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
v___y_492_ = v___y_508_;
v___y_493_ = v___y_513_;
v___y_494_ = v___y_515_;
v___y_495_ = v___y_507_;
v___y_496_ = v___x_518_;
v___y_497_ = v___y_509_;
v___y_498_ = v___y_510_;
v___y_499_ = v___y_511_;
v___y_500_ = v___y_512_;
v___y_501_ = v___y_517_;
v___y_502_ = v___x_521_;
v___y_503_ = v___y_514_;
v___y_504_ = v___y_516_;
v___y_505_ = v___y_507_;
goto v___jp_491_;
}
else
{
v___y_492_ = v___y_508_;
v___y_493_ = v___y_513_;
v___y_494_ = v___y_515_;
v___y_495_ = v___y_507_;
v___y_496_ = v___x_518_;
v___y_497_ = v___y_509_;
v___y_498_ = v___y_510_;
v___y_499_ = v___y_511_;
v___y_500_ = v___y_512_;
v___y_501_ = v___y_517_;
v___y_502_ = v___x_521_;
v___y_503_ = v___y_514_;
v___y_504_ = v___y_516_;
v___y_505_ = v___y_514_;
goto v___jp_491_;
}
}
v___jp_526_:
{
lean_object* v_toCold_538_; lean_object* v_currRecDepth_539_; lean_object* v_ref_540_; uint8_t v_suppressElabErrors_541_; uint8_t v_checkDeprecated_542_; uint8_t v_isRecordingDeps_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_574_; 
v_toCold_538_ = lean_ctor_get(v___y_536_, 0);
v_currRecDepth_539_ = lean_ctor_get(v___y_536_, 1);
v_ref_540_ = lean_ctor_get(v___y_536_, 2);
v_suppressElabErrors_541_ = lean_ctor_get_uint8(v___y_536_, sizeof(void*)*3 + 2);
v_checkDeprecated_542_ = lean_ctor_get_uint8(v___y_536_, sizeof(void*)*3 + 3);
v_isRecordingDeps_543_ = lean_ctor_get_uint8(v___y_536_, sizeof(void*)*3 + 4);
v_isSharedCheck_574_ = !lean_is_exclusive(v___y_536_);
if (v_isSharedCheck_574_ == 0)
{
v___x_545_ = v___y_536_;
v_isShared_546_ = v_isSharedCheck_574_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_ref_540_);
lean_inc(v_currRecDepth_539_);
lean_inc(v_toCold_538_);
lean_dec(v___y_536_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_574_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_fileName_547_; lean_object* v_fileMap_548_; lean_object* v_currNamespace_549_; lean_object* v_openDecls_550_; lean_object* v_initHeartbeats_551_; lean_object* v_maxHeartbeats_552_; lean_object* v_quotContext_553_; lean_object* v_currMacroScope_554_; lean_object* v_cancelTk_x3f_555_; lean_object* v_inheritedTraceOptions_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_571_; 
v_fileName_547_ = lean_ctor_get(v_toCold_538_, 0);
v_fileMap_548_ = lean_ctor_get(v_toCold_538_, 1);
v_currNamespace_549_ = lean_ctor_get(v_toCold_538_, 4);
v_openDecls_550_ = lean_ctor_get(v_toCold_538_, 5);
v_initHeartbeats_551_ = lean_ctor_get(v_toCold_538_, 6);
v_maxHeartbeats_552_ = lean_ctor_get(v_toCold_538_, 7);
v_quotContext_553_ = lean_ctor_get(v_toCold_538_, 8);
v_currMacroScope_554_ = lean_ctor_get(v_toCold_538_, 9);
v_cancelTk_x3f_555_ = lean_ctor_get(v_toCold_538_, 10);
v_inheritedTraceOptions_556_ = lean_ctor_get(v_toCold_538_, 11);
v_isSharedCheck_571_ = !lean_is_exclusive(v_toCold_538_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_572_ = lean_ctor_get(v_toCold_538_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_toCold_538_, 2);
lean_dec(v_unused_573_);
v___x_558_ = v_toCold_538_;
v_isShared_559_ = v_isSharedCheck_571_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_inheritedTraceOptions_556_);
lean_inc(v_cancelTk_x3f_555_);
lean_inc(v_currMacroScope_554_);
lean_inc(v_quotContext_553_);
lean_inc(v_maxHeartbeats_552_);
lean_inc(v_initHeartbeats_551_);
lean_inc(v_openDecls_550_);
lean_inc(v_currNamespace_549_);
lean_inc(v_fileMap_548_);
lean_inc(v_fileName_547_);
lean_dec(v_toCold_538_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_571_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_560_ = l_Lean_maxRecDepth;
v___x_561_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_528_, v___x_560_);
lean_inc_ref(v___y_528_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 3, v___x_561_);
lean_ctor_set(v___x_558_, 2, v___y_528_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_fileName_547_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_fileMap_548_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v___y_528_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_currNamespace_549_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v_openDecls_550_);
lean_ctor_set(v_reuseFailAlloc_570_, 6, v_initHeartbeats_551_);
lean_ctor_set(v_reuseFailAlloc_570_, 7, v_maxHeartbeats_552_);
lean_ctor_set(v_reuseFailAlloc_570_, 8, v_quotContext_553_);
lean_ctor_set(v_reuseFailAlloc_570_, 9, v_currMacroScope_554_);
lean_ctor_set(v_reuseFailAlloc_570_, 10, v_cancelTk_x3f_555_);
lean_ctor_set(v_reuseFailAlloc_570_, 11, v_inheritedTraceOptions_556_);
v___x_563_ = v_reuseFailAlloc_570_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_563_);
v___x_565_ = v___x_545_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_currRecDepth_539_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_ref_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3 + 2, v_suppressElabErrors_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3 + 3, v_checkDeprecated_542_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3 + 4, v_isRecordingDeps_543_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_ctor_set_uint16(v___x_565_, sizeof(void*)*3, v___y_532_);
if (v_isRecordingDeps_543_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_567_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v___y_528_, v___x_566_, v_isRecordingDeps_543_);
v___y_507_ = v___y_527_;
v___y_508_ = v___y_529_;
v___y_509_ = v___x_560_;
v___y_510_ = v___x_565_;
v___y_511_ = v___y_530_;
v___y_512_ = v___y_531_;
v___y_513_ = v___y_537_;
v___y_514_ = v___y_533_;
v___y_515_ = v___y_534_;
v___y_516_ = v___y_535_;
v___y_517_ = v___x_567_;
goto v___jp_506_;
}
else
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_528_);
v___y_507_ = v___y_527_;
v___y_508_ = v___y_529_;
v___y_509_ = v___x_560_;
v___y_510_ = v___x_565_;
v___y_511_ = v___y_530_;
v___y_512_ = v___y_531_;
v___y_513_ = v___y_537_;
v___y_514_ = v___y_533_;
v___y_515_ = v___y_534_;
v___y_516_ = v___y_535_;
v___y_517_ = v___x_568_;
goto v___jp_506_;
}
}
}
}
}
}
v___jp_575_:
{
lean_object* v___x_588_; lean_object* v_env_589_; lean_object* v_nextMacroScope_590_; lean_object* v_ngen_591_; lean_object* v_auxDeclNGen_592_; lean_object* v_traceState_593_; lean_object* v_recordedDeps_594_; lean_object* v_messages_595_; lean_object* v_infoState_596_; lean_object* v_snapshotTasks_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
v___x_588_ = lean_st_ref_take(v___y_580_);
v_env_589_ = lean_ctor_get(v___x_588_, 0);
v_nextMacroScope_590_ = lean_ctor_get(v___x_588_, 1);
v_ngen_591_ = lean_ctor_get(v___x_588_, 2);
v_auxDeclNGen_592_ = lean_ctor_get(v___x_588_, 3);
v_traceState_593_ = lean_ctor_get(v___x_588_, 4);
v_recordedDeps_594_ = lean_ctor_get(v___x_588_, 6);
v_messages_595_ = lean_ctor_get(v___x_588_, 7);
v_infoState_596_ = lean_ctor_get(v___x_588_, 8);
v_snapshotTasks_597_ = lean_ctor_get(v___x_588_, 9);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_588_, 5);
lean_dec(v_unused_607_);
v___x_599_ = v___x_588_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snapshotTasks_597_);
lean_inc(v_infoState_596_);
lean_inc(v_messages_595_);
lean_inc(v_recordedDeps_594_);
lean_inc(v_traceState_593_);
lean_inc(v_auxDeclNGen_592_);
lean_inc(v_ngen_591_);
lean_inc(v_nextMacroScope_590_);
lean_inc(v_env_589_);
lean_dec(v___x_588_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = l_Lean_Kernel_enableDiag(v_env_589_, v___y_584_);
lean_inc_ref(v___y_585_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 5, v___y_585_);
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_nextMacroScope_590_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_ngen_591_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_auxDeclNGen_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_traceState_593_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v___y_585_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_recordedDeps_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 8, v_infoState_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 9, v_snapshotTasks_597_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = lean_st_ref_put(v___y_580_, v___x_603_);
v___y_527_ = v___y_582_;
v___y_528_ = v___y_576_;
v___y_529_ = v___y_577_;
v___y_530_ = v___y_583_;
v___y_531_ = v___y_585_;
v___y_532_ = v___y_579_;
v___y_533_ = v___y_586_;
v___y_534_ = v___y_581_;
v___y_535_ = v___y_587_;
v___y_536_ = v___y_578_;
v___y_537_ = v___y_580_;
goto v___jp_526_;
}
}
}
v___jp_608_:
{
if (v___y_621_ == 0)
{
if (v___y_616_ == 0)
{
v___y_527_ = v___y_615_;
v___y_528_ = v___y_609_;
v___y_529_ = v___y_610_;
v___y_530_ = v___y_617_;
v___y_531_ = v___y_618_;
v___y_532_ = v___y_612_;
v___y_533_ = v___y_619_;
v___y_534_ = v___y_614_;
v___y_535_ = v___y_620_;
v___y_536_ = v___y_611_;
v___y_537_ = v___y_613_;
goto v___jp_526_;
}
else
{
v___y_576_ = v___y_609_;
v___y_577_ = v___y_610_;
v___y_578_ = v___y_611_;
v___y_579_ = v___y_612_;
v___y_580_ = v___y_613_;
v___y_581_ = v___y_614_;
v___y_582_ = v___y_615_;
v___y_583_ = v___y_617_;
v___y_584_ = v___y_621_;
v___y_585_ = v___y_618_;
v___y_586_ = v___y_619_;
v___y_587_ = v___y_620_;
goto v___jp_575_;
}
}
else
{
if (v___y_616_ == 0)
{
v___y_576_ = v___y_609_;
v___y_577_ = v___y_610_;
v___y_578_ = v___y_611_;
v___y_579_ = v___y_612_;
v___y_580_ = v___y_613_;
v___y_581_ = v___y_614_;
v___y_582_ = v___y_615_;
v___y_583_ = v___y_617_;
v___y_584_ = v___y_621_;
v___y_585_ = v___y_618_;
v___y_586_ = v___y_619_;
v___y_587_ = v___y_620_;
goto v___jp_575_;
}
else
{
v___y_527_ = v___y_615_;
v___y_528_ = v___y_609_;
v___y_529_ = v___y_610_;
v___y_530_ = v___y_617_;
v___y_531_ = v___y_618_;
v___y_532_ = v___y_612_;
v___y_533_ = v___y_619_;
v___y_534_ = v___y_614_;
v___y_535_ = v___y_620_;
v___y_536_ = v___y_611_;
v___y_537_ = v___y_613_;
goto v___jp_526_;
}
}
}
v___jp_622_:
{
uint16_t v___x_633_; lean_object* v___x_634_; lean_object* v_env_635_; uint8_t v___x_636_; uint16_t v___x_637_; uint16_t v___x_638_; uint16_t v___x_639_; uint8_t v___x_640_; 
v___x_633_ = l_Lean_OptionFlags_ofOptions(v___y_632_);
v___x_634_ = lean_st_ref_get(v___y_628_);
v_env_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_env_635_);
lean_dec(v___x_634_);
v___x_636_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_635_);
lean_dec_ref(v_env_635_);
v___x_637_ = 512;
v___x_638_ = lean_uint16_land(v___x_633_, v___x_637_);
v___x_639_ = 0;
v___x_640_ = lean_uint16_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
v___y_609_ = v___y_632_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_625_;
v___y_612_ = v___x_633_;
v___y_613_ = v___y_628_;
v___y_614_ = v___y_630_;
v___y_615_ = v___y_623_;
v___y_616_ = v___x_636_;
v___y_617_ = v___y_626_;
v___y_618_ = v___y_627_;
v___y_619_ = v___y_629_;
v___y_620_ = v___y_631_;
v___y_621_ = v___y_623_;
goto v___jp_608_;
}
else
{
v___y_609_ = v___y_632_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_625_;
v___y_612_ = v___x_633_;
v___y_613_ = v___y_628_;
v___y_614_ = v___y_630_;
v___y_615_ = v___y_623_;
v___y_616_ = v___x_636_;
v___y_617_ = v___y_626_;
v___y_618_ = v___y_627_;
v___y_619_ = v___y_629_;
v___y_620_ = v___y_631_;
v___y_621_ = v___y_629_;
goto v___jp_608_;
}
}
v___jp_641_:
{
lean_object* v___x_651_; 
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
lean_inc_ref(v___y_642_);
v___x_651_ = lean_infer_type(v___y_642_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc_n(v_a_652_, 2);
lean_dec_ref_known(v___x_651_, 1);
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
v___x_653_ = lean_apply_6(v_checkType_276_, v_a_652_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, lean_box(0));
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_env_661_; lean_object* v_nextMacroScope_662_; lean_object* v_ngen_663_; lean_object* v_auxDeclNGen_664_; lean_object* v_traceState_665_; lean_object* v_recordedDeps_666_; lean_object* v_messages_667_; lean_object* v_infoState_668_; lean_object* v_snapshotTasks_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref_known(v___x_653_, 1);
v___x_654_ = lean_array_to_list(v___y_646_);
lean_inc_n(v___y_645_, 2);
v___x_655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_655_, 0, v___y_645_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_ctor_set(v___x_655_, 2, v_a_652_);
v___x_656_ = lean_box(0);
lean_inc(v___y_644_);
v___x_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_645_);
lean_ctor_set(v___x_657_, 1, v___y_644_);
v___x_658_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_658_, 0, v___x_655_);
lean_ctor_set(v___x_658_, 1, v___y_642_);
lean_ctor_set(v___x_658_, 2, v___x_656_);
lean_ctor_set(v___x_658_, 3, v___x_657_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*4, v_safety_277_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
v___x_660_ = lean_st_ref_take(v___y_650_);
v_env_661_ = lean_ctor_get(v___x_660_, 0);
v_nextMacroScope_662_ = lean_ctor_get(v___x_660_, 1);
v_ngen_663_ = lean_ctor_get(v___x_660_, 2);
v_auxDeclNGen_664_ = lean_ctor_get(v___x_660_, 3);
v_traceState_665_ = lean_ctor_get(v___x_660_, 4);
v_recordedDeps_666_ = lean_ctor_get(v___x_660_, 6);
v_messages_667_ = lean_ctor_get(v___x_660_, 7);
v_infoState_668_ = lean_ctor_get(v___x_660_, 8);
v_snapshotTasks_669_ = lean_ctor_get(v___x_660_, 9);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_660_, 5);
lean_dec(v_unused_720_);
v___x_671_ = v___x_660_;
v_isShared_672_ = v_isSharedCheck_719_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snapshotTasks_669_);
lean_inc(v_infoState_668_);
lean_inc(v_messages_667_);
lean_inc(v_recordedDeps_666_);
lean_inc(v_traceState_665_);
lean_inc(v_auxDeclNGen_664_);
lean_inc(v_ngen_663_);
lean_inc(v_nextMacroScope_662_);
lean_inc(v_env_661_);
lean_dec(v___x_660_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_719_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v___y_645_);
v___x_673_ = l_Lean_markMeta(v_env_661_, v___y_645_);
v___x_674_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_675_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 5, v___x_675_);
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_677_ = v___x_671_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_nextMacroScope_662_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_ngen_663_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_auxDeclNGen_664_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_traceState_665_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_recordedDeps_666_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_messages_667_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_infoState_668_);
lean_ctor_set(v_reuseFailAlloc_718_, 9, v_snapshotTasks_669_);
v___x_677_ = v_reuseFailAlloc_718_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_mctx_680_; lean_object* v_zetaDeltaFVarIds_681_; lean_object* v_postponed_682_; lean_object* v_diag_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_716_; 
v___x_678_ = lean_st_ref_put(v___y_650_, v___x_677_);
v___x_679_ = lean_st_ref_take(v___y_648_);
v_mctx_680_ = lean_ctor_get(v___x_679_, 0);
v_zetaDeltaFVarIds_681_ = lean_ctor_get(v___x_679_, 2);
v_postponed_682_ = lean_ctor_get(v___x_679_, 3);
v_diag_683_ = lean_ctor_get(v___x_679_, 4);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_679_, 1);
lean_dec(v_unused_717_);
v___x_685_ = v___x_679_;
v_isShared_686_ = v_isSharedCheck_716_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_diag_683_);
lean_inc(v_postponed_682_);
lean_inc(v_zetaDeltaFVarIds_681_);
lean_inc(v_mctx_680_);
lean_dec(v___x_679_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_716_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_687_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_688_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
v___x_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_689_, 0, v___x_674_);
lean_ctor_set(v___x_689_, 1, v___x_674_);
lean_ctor_set(v___x_689_, 2, v___y_643_);
v___x_690_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_690_, 0, v___x_687_);
lean_ctor_set(v___x_690_, 1, v___x_674_);
lean_ctor_set(v___x_690_, 2, v___x_688_);
lean_ctor_set(v___x_690_, 3, v___x_674_);
lean_ctor_set(v___x_690_, 4, v___x_674_);
lean_ctor_set(v___x_690_, 5, v___x_674_);
lean_ctor_set(v___x_690_, 6, v___x_674_);
lean_ctor_set(v___x_690_, 7, v___x_689_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_690_);
v___x_692_ = v___x_685_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_mctx_680_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_zetaDeltaFVarIds_681_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_postponed_682_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_diag_683_);
v___x_692_ = v_reuseFailAlloc_715_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_env_695_; lean_object* v_checked_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = lean_st_ref_put(v___y_648_, v___x_692_);
v___x_694_ = lean_st_ref_get(v___y_650_);
v_env_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref(v_env_695_);
lean_dec(v___x_694_);
v_checked_696_ = lean_ctor_get(v_env_695_, 2);
lean_inc_ref(v_checked_696_);
lean_dec_ref(v_env_695_);
v___x_697_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_698_ = l_Lean_traceBlock___redArg(v___x_697_, v_checked_696_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_toCold_699_; uint8_t v_isRecordingDeps_700_; lean_object* v_options_701_; uint8_t v___x_702_; uint8_t v___x_703_; 
lean_dec_ref_known(v___x_698_, 1);
v_toCold_699_ = lean_ctor_get(v___y_649_, 0);
v_isRecordingDeps_700_ = lean_ctor_get_uint8(v___y_649_, sizeof(void*)*3 + 4);
v_options_701_ = lean_ctor_get(v_toCold_699_, 2);
v___x_702_ = 1;
v___x_703_ = 0;
if (v_isRecordingDeps_700_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = l_Lean_Elab_async;
lean_inc_ref(v_options_701_);
v___x_705_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v_options_701_, v___x_704_, v_isRecordingDeps_700_);
v___y_623_ = v___x_702_;
v___y_624_ = v___x_659_;
v___y_625_ = v___y_649_;
v___y_626_ = v___y_647_;
v___y_627_ = v___x_675_;
v___y_628_ = v___y_650_;
v___y_629_ = v___x_703_;
v___y_630_ = v___y_645_;
v___y_631_ = v___y_648_;
v___y_632_ = v___x_705_;
goto v___jp_622_;
}
else
{
lean_object* v___x_706_; 
lean_inc_ref(v_options_701_);
v___x_706_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_701_);
v___y_623_ = v___x_702_;
v___y_624_ = v___x_659_;
v___y_625_ = v___y_649_;
v___y_626_ = v___y_647_;
v___y_627_ = v___x_675_;
v___y_628_ = v___y_650_;
v___y_629_ = v___x_703_;
v___y_630_ = v___y_645_;
v___y_631_ = v___y_648_;
v___y_632_ = v___x_706_;
goto v___jp_622_;
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref_known(v___x_659_, 1);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_645_);
v_a_707_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_698_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_698_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
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
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_a_652_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
v_a_721_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_653_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_653_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_checkType_276_);
v_a_729_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_651_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_651_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
v___jp_737_:
{
lean_object* v___x_738_; lean_object* v_env_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_st_ref_get(v___y_282_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_env_739_);
lean_dec(v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_741_ = l_Lean_Core_mkFreshUserName(v___x_740_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_mkPrivateName(v_env_739_, v_a_742_);
lean_dec_ref(v_env_739_);
v___x_744_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_278_, v___y_280_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_params_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_n(v_a_745_, 2);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_748_ = l_Lean_collectLevelParams(v___x_747_, v_a_745_);
v_params_749_ = lean_ctor_get(v___x_748_, 2);
lean_inc_ref(v_params_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_box(0);
v___x_751_ = l_Lean_Expr_hasMVar(v_a_745_);
if (v___x_751_ == 0)
{
v___y_642_ = v_a_745_;
v___y_643_ = v___x_746_;
v___y_644_ = v___x_750_;
v___y_645_ = v___x_743_;
v___y_646_ = v_params_749_;
v___y_647_ = v___y_279_;
v___y_648_ = v___y_280_;
v___y_649_ = v___y_281_;
v___y_650_ = v___y_282_;
goto v___jp_641_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_745_);
v___x_753_ = l_Lean_indentExpr(v_a_745_);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_754_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_dec_ref_known(v___x_755_, 1);
v___y_642_ = v_a_745_;
v___y_643_ = v___x_746_;
v___y_644_ = v___x_750_;
v___y_645_ = v___x_743_;
v___y_646_ = v_params_749_;
v___y_647_ = v___y_279_;
v___y_648_ = v___y_280_;
v___y_649_ = v___y_281_;
v___y_650_ = v___y_282_;
goto v___jp_641_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_params_749_);
lean_dec(v_a_745_);
lean_dec(v___x_743_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v_checkType_276_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v___x_743_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v_checkType_276_);
v_a_764_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_744_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_744_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_env_739_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v_value_278_);
lean_dec_ref(v_checkType_276_);
v_a_772_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_741_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_741_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
v___jp_780_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_mctx_794_; lean_object* v_zetaDeltaFVarIds_795_; lean_object* v_postponed_796_; lean_object* v_diag_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_806_; 
v___x_790_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_791_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_791_, 0, v___y_789_);
lean_ctor_set(v___x_791_, 1, v_nextMacroScope_781_);
lean_ctor_set(v___x_791_, 2, v_ngen_782_);
lean_ctor_set(v___x_791_, 3, v_auxDeclNGen_783_);
lean_ctor_set(v___x_791_, 4, v_traceState_784_);
lean_ctor_set(v___x_791_, 5, v___x_790_);
lean_ctor_set(v___x_791_, 6, v_recordedDeps_785_);
lean_ctor_set(v___x_791_, 7, v_messages_786_);
lean_ctor_set(v___x_791_, 8, v_infoState_787_);
lean_ctor_set(v___x_791_, 9, v_snapshotTasks_788_);
v___x_792_ = lean_st_ref_put(v___y_282_, v___x_791_);
v___x_793_ = lean_st_ref_take(v___y_280_);
v_mctx_794_ = lean_ctor_get(v___x_793_, 0);
v_zetaDeltaFVarIds_795_ = lean_ctor_get(v___x_793_, 2);
v_postponed_796_ = lean_ctor_get(v___x_793_, 3);
v_diag_797_ = lean_ctor_get(v___x_793_, 4);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v___x_793_, 1);
lean_dec(v_unused_807_);
v___x_799_ = v___x_793_;
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_diag_797_);
lean_inc(v_postponed_796_);
lean_inc(v_zetaDeltaFVarIds_795_);
lean_inc(v_mctx_794_);
lean_dec(v___x_793_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_mctx_794_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_zetaDeltaFVarIds_795_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_postponed_796_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_diag_797_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; 
v___x_804_ = lean_st_ref_put(v___y_280_, v___x_803_);
goto v___jp_737_;
}
}
}
v___jp_809_:
{
lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v_nextMacroScope_812_; lean_object* v_ngen_813_; lean_object* v_auxDeclNGen_814_; lean_object* v_traceState_815_; lean_object* v_recordedDeps_816_; lean_object* v_messages_817_; lean_object* v_infoState_818_; lean_object* v_snapshotTasks_819_; lean_object* v___x_820_; 
v___x_810_ = lean_st_ref_take(v___y_282_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref_n(v_env_811_, 2);
v_nextMacroScope_812_ = lean_ctor_get(v___x_810_, 1);
lean_inc(v_nextMacroScope_812_);
v_ngen_813_ = lean_ctor_get(v___x_810_, 2);
lean_inc_ref(v_ngen_813_);
v_auxDeclNGen_814_ = lean_ctor_get(v___x_810_, 3);
lean_inc_ref(v_auxDeclNGen_814_);
v_traceState_815_ = lean_ctor_get(v___x_810_, 4);
lean_inc_ref(v_traceState_815_);
v_recordedDeps_816_ = lean_ctor_get(v___x_810_, 6);
lean_inc_ref(v_recordedDeps_816_);
v_messages_817_ = lean_ctor_get(v___x_810_, 7);
lean_inc_ref(v_messages_817_);
v_infoState_818_ = lean_ctor_get(v___x_810_, 8);
lean_inc_ref(v_infoState_818_);
v_snapshotTasks_819_ = lean_ctor_get(v___x_810_, 9);
lean_inc_ref(v_snapshotTasks_819_);
lean_dec(v___x_810_);
v___x_820_ = l_Lean_Environment_importEnv_x3f(v_env_811_);
if (lean_obj_tag(v___x_820_) == 0)
{
v_nextMacroScope_781_ = v_nextMacroScope_812_;
v_ngen_782_ = v_ngen_813_;
v_auxDeclNGen_783_ = v_auxDeclNGen_814_;
v_traceState_784_ = v_traceState_815_;
v_recordedDeps_785_ = v_recordedDeps_816_;
v_messages_786_ = v_messages_817_;
v_infoState_787_ = v_infoState_818_;
v_snapshotTasks_788_ = v_snapshotTasks_819_;
v___y_789_ = v_env_811_;
goto v___jp_780_;
}
else
{
lean_object* v_val_821_; 
lean_dec_ref(v_env_811_);
v_val_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_820_, 1);
v_nextMacroScope_781_ = v_nextMacroScope_812_;
v_ngen_782_ = v_ngen_813_;
v_auxDeclNGen_783_ = v_auxDeclNGen_814_;
v_traceState_784_ = v_traceState_815_;
v_recordedDeps_785_ = v_recordedDeps_816_;
v_messages_786_ = v_messages_817_;
v_infoState_787_ = v_infoState_818_;
v_snapshotTasks_788_ = v_snapshotTasks_819_;
v___y_789_ = v_val_821_;
goto v___jp_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_830_, lean_object* v_checkType_831_, lean_object* v_safety_832_, lean_object* v_value_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v_checkMeta_boxed_839_; uint8_t v_safety_boxed_840_; lean_object* v_res_841_; 
v_checkMeta_boxed_839_ = lean_unbox(v_checkMeta_830_);
v_safety_boxed_840_ = lean_unbox(v_safety_832_);
v_res_841_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_839_, v_checkType_831_, v_safety_boxed_840_, v_value_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(lean_object* v_env_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; lean_object* v_nextMacroScope_847_; lean_object* v_ngen_848_; lean_object* v_auxDeclNGen_849_; lean_object* v_traceState_850_; lean_object* v_recordedDeps_851_; lean_object* v_messages_852_; lean_object* v_infoState_853_; lean_object* v_snapshotTasks_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_880_; 
v___x_846_ = lean_st_ref_take(v___y_844_);
v_nextMacroScope_847_ = lean_ctor_get(v___x_846_, 1);
v_ngen_848_ = lean_ctor_get(v___x_846_, 2);
v_auxDeclNGen_849_ = lean_ctor_get(v___x_846_, 3);
v_traceState_850_ = lean_ctor_get(v___x_846_, 4);
v_recordedDeps_851_ = lean_ctor_get(v___x_846_, 6);
v_messages_852_ = lean_ctor_get(v___x_846_, 7);
v_infoState_853_ = lean_ctor_get(v___x_846_, 8);
v_snapshotTasks_854_ = lean_ctor_get(v___x_846_, 9);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; lean_object* v_unused_882_; 
v_unused_881_ = lean_ctor_get(v___x_846_, 5);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v___x_846_, 0);
lean_dec(v_unused_882_);
v___x_856_ = v___x_846_;
v_isShared_857_ = v_isSharedCheck_880_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snapshotTasks_854_);
lean_inc(v_infoState_853_);
lean_inc(v_messages_852_);
lean_inc(v_recordedDeps_851_);
lean_inc(v_traceState_850_);
lean_inc(v_auxDeclNGen_849_);
lean_inc(v_ngen_848_);
lean_inc(v_nextMacroScope_847_);
lean_dec(v___x_846_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_880_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 5, v___x_858_);
lean_ctor_set(v___x_856_, 0, v_env_842_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_env_842_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_nextMacroScope_847_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_ngen_848_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_auxDeclNGen_849_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_traceState_850_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_recordedDeps_851_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_messages_852_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_infoState_853_);
lean_ctor_set(v_reuseFailAlloc_879_, 9, v_snapshotTasks_854_);
v___x_860_ = v_reuseFailAlloc_879_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v_zetaDeltaFVarIds_864_; lean_object* v_postponed_865_; lean_object* v_diag_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v___x_861_ = lean_st_ref_put(v___y_844_, v___x_860_);
v___x_862_ = lean_st_ref_take(v___y_843_);
v_mctx_863_ = lean_ctor_get(v___x_862_, 0);
v_zetaDeltaFVarIds_864_ = lean_ctor_get(v___x_862_, 2);
v_postponed_865_ = lean_ctor_get(v___x_862_, 3);
v_diag_866_ = lean_ctor_get(v___x_862_, 4);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v___x_862_, 1);
lean_dec(v_unused_878_);
v___x_868_ = v___x_862_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_diag_866_);
lean_inc(v_postponed_865_);
lean_inc(v_zetaDeltaFVarIds_864_);
lean_inc(v_mctx_863_);
lean_dec(v___x_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_870_ = lean_box(0);
v___x_871_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_mctx_863_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_zetaDeltaFVarIds_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_postponed_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_diag_866_);
v___x_873_ = v_reuseFailAlloc_876_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_st_ref_put(v___y_843_, v___x_873_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_870_);
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg___boxed(lean_object* v_env_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec(v___y_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_888_, lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_env_896_; lean_object* v_a_898_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_895_ = lean_st_ref_get(v___y_893_);
v_env_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref(v_env_896_);
lean_dec(v___x_895_);
v___x_908_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_888_, v___y_891_, v___y_893_);
lean_dec_ref(v___x_908_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
v___x_909_ = lean_apply_5(v_x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_896_, v___y_891_, v___y_893_);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_919_);
v___x_913_ = v___x_911_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_911_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v_a_910_);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_910_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_object* v_a_920_; 
v_a_920_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_909_, 1);
v_a_898_ = v_a_920_;
goto v___jp_897_;
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v___x_899_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_896_, v___y_891_, v___y_893_);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_907_);
v___x_901_ = v___x_899_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_dec(v___x_899_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 1);
lean_ctor_set(v___x_901_, 0, v_a_898_);
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_898_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_921_, v_x_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_929_, lean_object* v_checkType_930_, uint8_t v_safety_931_, uint8_t v_checkMeta_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v_env_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_938_ = lean_box(v_checkMeta_932_);
v___x_939_ = lean_box(v_safety_931_);
v___f_940_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_940_, 0, v___x_938_);
lean_closure_set(v___f_940_, 1, v_checkType_930_);
lean_closure_set(v___f_940_, 2, v___x_939_);
lean_closure_set(v___f_940_, 3, v_value_929_);
v___x_941_ = lean_st_ref_get(v_a_936_);
v_env_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc_ref(v_env_942_);
lean_dec(v___x_941_);
v___x_943_ = l_Lean_Environment_unlockAsync(v_env_942_);
v___x_944_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_943_, v___f_940_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_945_, lean_object* v_checkType_946_, lean_object* v_safety_947_, lean_object* v_checkMeta_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_safety_boxed_954_; uint8_t v_checkMeta_boxed_955_; lean_object* v_res_956_; 
v_safety_boxed_954_ = lean_unbox(v_safety_947_);
v_checkMeta_boxed_955_ = lean_unbox(v_checkMeta_948_);
v_res_956_ = l_Lean_Meta_evalExprCore___redArg(v_value_945_, v_checkType_946_, v_safety_boxed_954_, v_checkMeta_boxed_955_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_957_, lean_object* v_value_958_, lean_object* v_checkType_959_, uint8_t v_safety_960_, uint8_t v_checkMeta_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_evalExprCore___redArg(v_value_958_, v_checkType_959_, v_safety_960_, v_checkMeta_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_968_, lean_object* v_value_969_, lean_object* v_checkType_970_, lean_object* v_safety_971_, lean_object* v_checkMeta_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
uint8_t v_safety_boxed_978_; uint8_t v_checkMeta_boxed_979_; lean_object* v_res_980_; 
v_safety_boxed_978_ = lean_unbox(v_safety_971_);
v_checkMeta_boxed_979_ = lean_unbox(v_checkMeta_972_);
v_res_980_ = l_Lean_Meta_evalExprCore(v_00_u03b1_968_, v_value_969_, v_checkType_970_, v_safety_boxed_978_, v_checkMeta_boxed_979_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_00_u03b2_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg(){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg___boxed(lean_object* v___dummy_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg();
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_00_u03b2_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object* v_00_u03b1_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object* v_00_u03b1_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_00_u03b1_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_00_u03b1_1003_, lean_object* v_constName_1004_, uint8_t v_checkMeta_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v_constName_1004_, v_checkMeta_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_constName_1013_, lean_object* v_checkMeta_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v_checkMeta_boxed_1020_; lean_object* v_res_1021_; 
v_checkMeta_boxed_1020_ = lean_unbox(v_checkMeta_1014_);
v_res_1021_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(v_00_u03b1_1012_, v_constName_1013_, v_checkMeta_boxed_1020_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_1022_, lean_object* v_msg_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_1030_, v_msg_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_1038_, lean_object* v_env_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_1039_, v_x_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_env_1048_, lean_object* v_x_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_1047_, v_env_1048_, v_x_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(lean_object* v_00_u03b1_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_x_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(v_00_u03b1_1064_, v_x_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12(lean_object* v_env_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_1072_, v___y_1074_, v___y_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___boxed(lean_object* v_env_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12(v_env_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1085_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1089_, lean_object* v_type_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Meta_whnfD(v_type_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1110_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Expr_isConstOf(v_a_1097_, v_typeName_1089_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_del_object(v___x_1099_);
v___x_1102_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1103_ = l_Lean_indentExpr(v_a_1097_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1104_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec(v_a_1097_);
v___x_1106_ = lean_box(0);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1106_);
v___x_1108_ = v___x_1099_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1096_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1096_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1119_, lean_object* v_type_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1119_, v_type_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_typeName_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1127_, lean_object* v_value_1128_, uint8_t v_safety_1129_, uint8_t v_checkMeta_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___f_1136_; lean_object* v___x_1137_; 
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1136_, 0, v_typeName_1127_);
v___x_1137_ = l_Lean_Meta_evalExprCore___redArg(v_value_1128_, v___f_1136_, v_safety_1129_, v_checkMeta_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1138_, lean_object* v_value_1139_, lean_object* v_safety_1140_, lean_object* v_checkMeta_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
uint8_t v_safety_boxed_1147_; uint8_t v_checkMeta_boxed_1148_; lean_object* v_res_1149_; 
v_safety_boxed_1147_ = lean_unbox(v_safety_1140_);
v_checkMeta_boxed_1148_ = lean_unbox(v_checkMeta_1141_);
v_res_1149_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1138_, v_value_1139_, v_safety_boxed_1147_, v_checkMeta_boxed_1148_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1150_, lean_object* v_typeName_1151_, lean_object* v_value_1152_, uint8_t v_safety_1153_, uint8_t v_checkMeta_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1151_, v_value_1152_, v_safety_1153_, v_checkMeta_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_typeName_1162_, lean_object* v_value_1163_, lean_object* v_safety_1164_, lean_object* v_checkMeta_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
uint8_t v_safety_boxed_1171_; uint8_t v_checkMeta_boxed_1172_; lean_object* v_res_1173_; 
v_safety_boxed_1171_ = lean_unbox(v_safety_1164_);
v_checkMeta_boxed_1172_ = lean_unbox(v_checkMeta_1165_);
v_res_1173_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1161_, v_typeName_1162_, v_value_1163_, v_safety_boxed_1171_, v_checkMeta_boxed_1172_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1173_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1179_, lean_object* v_type_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
lean_inc_ref(v_expectedType_1179_);
lean_inc_ref(v_type_1180_);
v___x_1186_ = l_Lean_Meta_isExprDefEq(v_type_1180_, v_expectedType_1179_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1211_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
uint8_t v___x_1191_; 
v___x_1191_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_del_object(v___x_1189_);
v___x_1192_ = lean_box(0);
v___x_1193_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1194_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1180_, v_expectedType_1179_, v___x_1192_, v___x_1193_, v___y_1181_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v_a_1195_);
v___x_1198_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1197_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1198_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v_a_1199_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1194_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1194_);
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
else
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_dec_ref(v_type_1180_);
lean_dec_ref(v_expectedType_1179_);
v___x_1207_ = lean_box(0);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1207_);
v___x_1209_ = v___x_1189_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_type_1180_);
lean_dec_ref(v_expectedType_1179_);
v_a_1212_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1186_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1186_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1220_, lean_object* v_type_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1220_, v_type_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1228_, lean_object* v_value_1229_, uint8_t v_safety_1230_, uint8_t v_checkMeta_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___f_1237_; lean_object* v___x_1238_; 
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1237_, 0, v_expectedType_1228_);
v___x_1238_ = l_Lean_Meta_evalExprCore___redArg(v_value_1229_, v___f_1237_, v_safety_1230_, v_checkMeta_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1239_, lean_object* v_value_1240_, lean_object* v_safety_1241_, lean_object* v_checkMeta_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
uint8_t v_safety_boxed_1248_; uint8_t v_checkMeta_boxed_1249_; lean_object* v_res_1250_; 
v_safety_boxed_1248_ = lean_unbox(v_safety_1241_);
v_checkMeta_boxed_1249_ = lean_unbox(v_checkMeta_1242_);
v_res_1250_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1239_, v_value_1240_, v_safety_boxed_1248_, v_checkMeta_boxed_1249_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1251_, lean_object* v_expectedType_1252_, lean_object* v_value_1253_, uint8_t v_safety_1254_, uint8_t v_checkMeta_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1252_, v_value_1253_, v_safety_1254_, v_checkMeta_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1262_, lean_object* v_expectedType_1263_, lean_object* v_value_1264_, lean_object* v_safety_1265_, lean_object* v_checkMeta_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
uint8_t v_safety_boxed_1272_; uint8_t v_checkMeta_boxed_1273_; lean_object* v_res_1274_; 
v_safety_boxed_1272_ = lean_unbox(v_safety_1265_);
v_checkMeta_boxed_1273_ = lean_unbox(v_checkMeta_1266_);
v_res_1274_ = l_Lean_Meta_evalExpr(v_00_u03b1_1262_, v_expectedType_1263_, v_value_1264_, v_safety_boxed_1272_, v_checkMeta_boxed_1273_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1274_;
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

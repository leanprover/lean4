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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "compiler env"};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_tmp"};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(156, 26, 231, 16, 169, 5, 155, 241)}};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7;
static const lean_array_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "failed to evaluate expression, it contains metavariables"};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13;
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
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_box(0);
v___x_252_ = lean_unsigned_to_nat(16u);
v___x_253_ = lean_mk_array(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8));
v___x_260_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_ctor_set(v___x_261_, 2, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
lean_ctor_set(v___x_267_, 2, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
v___x_269_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_270_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_271_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_269_);
lean_ctor_set(v___x_271_, 3, v___x_269_);
lean_ctor_set(v___x_271_, 4, v___x_269_);
lean_ctor_set(v___x_271_, 5, v___x_269_);
lean_ctor_set(v___x_271_, 6, v___x_269_);
lean_ctor_set(v___x_271_, 7, v___x_268_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_272_, lean_object* v_checkType_273_, uint8_t v_safety_274_, lean_object* v_value_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; uint8_t v___y_286_; uint8_t v___y_287_; lean_object* v___y_288_; uint16_t v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; uint8_t v___y_341_; uint16_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; uint8_t v___y_346_; uint8_t v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; uint8_t v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; uint16_t v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; uint8_t v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; uint8_t v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; uint8_t v___y_410_; lean_object* v___y_411_; uint16_t v___y_412_; uint8_t v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; uint8_t v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; uint16_t v___y_466_; lean_object* v___y_467_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; uint8_t v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_496_; uint8_t v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; uint16_t v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; uint8_t v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; uint8_t v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; uint16_t v___y_528_; lean_object* v___y_529_; uint8_t v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; uint16_t v___y_576_; lean_object* v___y_577_; uint8_t v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; uint8_t v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_606_; lean_object* v___y_607_; uint16_t v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; uint8_t v___y_613_; uint8_t v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; uint8_t v___y_618_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v_nextMacroScope_777_; lean_object* v_ngen_778_; lean_object* v_auxDeclNGen_779_; lean_object* v_traceState_780_; lean_object* v_recordedDeps_781_; lean_object* v_messages_782_; lean_object* v_infoState_783_; lean_object* v_snapshotTasks_784_; lean_object* v___y_785_; lean_object* v___x_804_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_804_ = lean_st_ref_get(v___y_279_);
lean_inc_ref(v_value_275_);
v___x_818_ = l_Lean_Expr_getUsedConstants(v_value_275_);
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_array_get_size(v___x_818_);
v___x_821_ = lean_nat_dec_lt(v___x_819_, v___x_820_);
if (v___x_821_ == 0)
{
lean_dec_ref(v___x_818_);
lean_dec(v___x_804_);
goto v___jp_805_;
}
else
{
if (v___x_821_ == 0)
{
lean_dec_ref(v___x_818_);
lean_dec(v___x_804_);
goto v___jp_805_;
}
else
{
lean_object* v_env_822_; size_t v___x_823_; size_t v___x_824_; uint8_t v___x_825_; 
v_env_822_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_804_);
v___x_823_ = ((size_t)0ULL);
v___x_824_ = lean_usize_of_nat(v___x_820_);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_822_, v___x_820_, v___x_818_, v___x_823_, v___x_824_);
lean_dec_ref(v___x_818_);
lean_dec_ref(v_env_822_);
if (v___x_825_ == 0)
{
goto v___jp_805_;
}
else
{
goto v___jp_733_;
}
}
}
v___jp_281_:
{
lean_object* v_toCold_293_; lean_object* v_currRecDepth_294_; lean_object* v_ref_295_; uint8_t v_suppressElabErrors_296_; uint8_t v_checkDeprecated_297_; uint8_t v_isRecordingDeps_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_335_; 
v_toCold_293_ = lean_ctor_get(v___y_291_, 0);
v_currRecDepth_294_ = lean_ctor_get(v___y_291_, 1);
v_ref_295_ = lean_ctor_get(v___y_291_, 2);
v_suppressElabErrors_296_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 2);
v_checkDeprecated_297_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 3);
v_isRecordingDeps_298_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*3 + 4);
v_isSharedCheck_335_ = !lean_is_exclusive(v___y_291_);
if (v_isSharedCheck_335_ == 0)
{
v___x_300_ = v___y_291_;
v_isShared_301_ = v_isSharedCheck_335_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_ref_295_);
lean_inc(v_currRecDepth_294_);
lean_inc(v_toCold_293_);
lean_dec(v___y_291_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_335_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_fileName_302_; lean_object* v_fileMap_303_; lean_object* v_currNamespace_304_; lean_object* v_openDecls_305_; lean_object* v_initHeartbeats_306_; lean_object* v_maxHeartbeats_307_; lean_object* v_quotContext_308_; lean_object* v_currMacroScope_309_; lean_object* v_cancelTk_x3f_310_; lean_object* v_inheritedTraceOptions_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_332_; 
v_fileName_302_ = lean_ctor_get(v_toCold_293_, 0);
v_fileMap_303_ = lean_ctor_get(v_toCold_293_, 1);
v_currNamespace_304_ = lean_ctor_get(v_toCold_293_, 4);
v_openDecls_305_ = lean_ctor_get(v_toCold_293_, 5);
v_initHeartbeats_306_ = lean_ctor_get(v_toCold_293_, 6);
v_maxHeartbeats_307_ = lean_ctor_get(v_toCold_293_, 7);
v_quotContext_308_ = lean_ctor_get(v_toCold_293_, 8);
v_currMacroScope_309_ = lean_ctor_get(v_toCold_293_, 9);
v_cancelTk_x3f_310_ = lean_ctor_get(v_toCold_293_, 10);
v_inheritedTraceOptions_311_ = lean_ctor_get(v_toCold_293_, 11);
v_isSharedCheck_332_ = !lean_is_exclusive(v_toCold_293_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_333_ = lean_ctor_get(v_toCold_293_, 3);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_toCold_293_, 2);
lean_dec(v_unused_334_);
v___x_313_ = v_toCold_293_;
v_isShared_314_ = v_isSharedCheck_332_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_inheritedTraceOptions_311_);
lean_inc(v_cancelTk_x3f_310_);
lean_inc(v_currMacroScope_309_);
lean_inc(v_quotContext_308_);
lean_inc(v_maxHeartbeats_307_);
lean_inc(v_initHeartbeats_306_);
lean_inc(v_openDecls_305_);
lean_inc(v_currNamespace_304_);
lean_inc(v_fileMap_303_);
lean_inc(v_fileName_302_);
lean_dec(v_toCold_293_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_332_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_290_, v___y_285_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v___x_315_);
lean_ctor_set(v___x_313_, 2, v___y_290_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_fileName_302_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_fileMap_303_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v___y_290_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_currNamespace_304_);
lean_ctor_set(v_reuseFailAlloc_331_, 5, v_openDecls_305_);
lean_ctor_set(v_reuseFailAlloc_331_, 6, v_initHeartbeats_306_);
lean_ctor_set(v_reuseFailAlloc_331_, 7, v_maxHeartbeats_307_);
lean_ctor_set(v_reuseFailAlloc_331_, 8, v_quotContext_308_);
lean_ctor_set(v_reuseFailAlloc_331_, 9, v_currMacroScope_309_);
lean_ctor_set(v_reuseFailAlloc_331_, 10, v_cancelTk_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_331_, 11, v_inheritedTraceOptions_311_);
v___x_317_ = v_reuseFailAlloc_331_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_317_);
v___x_319_ = v___x_300_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_currRecDepth_294_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_ref_295_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*3 + 2, v_suppressElabErrors_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*3 + 3, v_checkDeprecated_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*3 + 4, v_isRecordingDeps_298_);
v___x_319_ = v_reuseFailAlloc_330_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
lean_ctor_set_uint16(v___x_319_, sizeof(void*)*3, v___y_289_);
v___x_320_ = l_Lean_addAndCompile(v___y_288_, v___y_287_, v___y_286_, v___x_319_, v___y_292_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v___x_321_; 
lean_dec_ref_known(v___x_320_, 1);
v___x_321_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v___y_283_, v_checkMeta_272_, v___y_284_, v___y_282_, v___x_319_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___x_319_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_284_);
return v___x_321_;
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v___x_319_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
v_a_322_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_320_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
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
}
}
}
v___jp_336_:
{
lean_object* v___x_350_; lean_object* v_env_351_; lean_object* v_nextMacroScope_352_; lean_object* v_ngen_353_; lean_object* v_auxDeclNGen_354_; lean_object* v_traceState_355_; lean_object* v_recordedDeps_356_; lean_object* v_messages_357_; lean_object* v_infoState_358_; lean_object* v_snapshotTasks_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
v___x_350_ = lean_st_ref_take(v___y_343_);
v_env_351_ = lean_ctor_get(v___x_350_, 0);
v_nextMacroScope_352_ = lean_ctor_get(v___x_350_, 1);
v_ngen_353_ = lean_ctor_get(v___x_350_, 2);
v_auxDeclNGen_354_ = lean_ctor_get(v___x_350_, 3);
v_traceState_355_ = lean_ctor_get(v___x_350_, 4);
v_recordedDeps_356_ = lean_ctor_get(v___x_350_, 6);
v_messages_357_ = lean_ctor_get(v___x_350_, 7);
v_infoState_358_ = lean_ctor_get(v___x_350_, 8);
v_snapshotTasks_359_ = lean_ctor_get(v___x_350_, 9);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_350_, 5);
lean_dec(v_unused_369_);
v___x_361_ = v___x_350_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snapshotTasks_359_);
lean_inc(v_infoState_358_);
lean_inc(v_messages_357_);
lean_inc(v_recordedDeps_356_);
lean_inc(v_traceState_355_);
lean_inc(v_auxDeclNGen_354_);
lean_inc(v_ngen_353_);
lean_inc(v_nextMacroScope_352_);
lean_inc(v_env_351_);
lean_dec(v___x_350_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = l_Lean_Kernel_enableDiag(v_env_351_, v___y_347_);
lean_inc_ref(v___y_344_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 5, v___y_344_);
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_nextMacroScope_352_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_ngen_353_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_auxDeclNGen_354_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_traceState_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 5, v___y_344_);
lean_ctor_set(v_reuseFailAlloc_367_, 6, v_recordedDeps_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 7, v_messages_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 8, v_infoState_358_);
lean_ctor_set(v_reuseFailAlloc_367_, 9, v_snapshotTasks_359_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_st_ref_put(v___y_343_, v___x_365_);
v___y_282_ = v___y_345_;
v___y_283_ = v___y_337_;
v___y_284_ = v___y_338_;
v___y_285_ = v___y_339_;
v___y_286_ = v___y_346_;
v___y_287_ = v___y_341_;
v___y_288_ = v___y_349_;
v___y_289_ = v___y_342_;
v___y_290_ = v___y_340_;
v___y_291_ = v___y_348_;
v___y_292_ = v___y_343_;
goto v___jp_281_;
}
}
}
v___jp_370_:
{
if (v___y_384_ == 0)
{
if (v___y_371_ == 0)
{
v___y_282_ = v___y_380_;
v___y_283_ = v___y_372_;
v___y_284_ = v___y_373_;
v___y_285_ = v___y_374_;
v___y_286_ = v___y_381_;
v___y_287_ = v___y_376_;
v___y_288_ = v___y_383_;
v___y_289_ = v___y_377_;
v___y_290_ = v___y_375_;
v___y_291_ = v___y_382_;
v___y_292_ = v___y_378_;
goto v___jp_281_;
}
else
{
v___y_337_ = v___y_372_;
v___y_338_ = v___y_373_;
v___y_339_ = v___y_374_;
v___y_340_ = v___y_375_;
v___y_341_ = v___y_376_;
v___y_342_ = v___y_377_;
v___y_343_ = v___y_378_;
v___y_344_ = v___y_379_;
v___y_345_ = v___y_380_;
v___y_346_ = v___y_381_;
v___y_347_ = v___y_384_;
v___y_348_ = v___y_382_;
v___y_349_ = v___y_383_;
goto v___jp_336_;
}
}
else
{
if (v___y_371_ == 0)
{
v___y_337_ = v___y_372_;
v___y_338_ = v___y_373_;
v___y_339_ = v___y_374_;
v___y_340_ = v___y_375_;
v___y_341_ = v___y_376_;
v___y_342_ = v___y_377_;
v___y_343_ = v___y_378_;
v___y_344_ = v___y_379_;
v___y_345_ = v___y_380_;
v___y_346_ = v___y_381_;
v___y_347_ = v___y_384_;
v___y_348_ = v___y_382_;
v___y_349_ = v___y_383_;
goto v___jp_336_;
}
else
{
v___y_282_ = v___y_380_;
v___y_283_ = v___y_372_;
v___y_284_ = v___y_373_;
v___y_285_ = v___y_374_;
v___y_286_ = v___y_381_;
v___y_287_ = v___y_376_;
v___y_288_ = v___y_383_;
v___y_289_ = v___y_377_;
v___y_290_ = v___y_375_;
v___y_291_ = v___y_382_;
v___y_292_ = v___y_378_;
goto v___jp_281_;
}
}
}
v___jp_385_:
{
uint16_t v___x_397_; lean_object* v___x_398_; lean_object* v_env_399_; uint8_t v___x_400_; uint16_t v___x_401_; uint16_t v___x_402_; uint16_t v___x_403_; uint8_t v___x_404_; 
v___x_397_ = l_Lean_OptionFlags_ofOptions(v___y_396_);
v___x_398_ = lean_st_ref_get(v___y_394_);
v_env_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc_ref(v_env_399_);
lean_dec(v___x_398_);
v___x_400_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_399_);
lean_dec_ref(v_env_399_);
v___x_401_ = 512;
v___x_402_ = lean_uint16_land(v___x_397_, v___x_401_);
v___x_403_ = 0;
v___x_404_ = lean_uint16_dec_eq(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
v___y_371_ = v___x_400_;
v___y_372_ = v___y_386_;
v___y_373_ = v___y_389_;
v___y_374_ = v___y_388_;
v___y_375_ = v___y_396_;
v___y_376_ = v___y_393_;
v___y_377_ = v___x_397_;
v___y_378_ = v___y_394_;
v___y_379_ = v___y_395_;
v___y_380_ = v___y_387_;
v___y_381_ = v___y_390_;
v___y_382_ = v___y_391_;
v___y_383_ = v___y_392_;
v___y_384_ = v___y_393_;
goto v___jp_370_;
}
else
{
v___y_371_ = v___x_400_;
v___y_372_ = v___y_386_;
v___y_373_ = v___y_389_;
v___y_374_ = v___y_388_;
v___y_375_ = v___y_396_;
v___y_376_ = v___y_393_;
v___y_377_ = v___x_397_;
v___y_378_ = v___y_394_;
v___y_379_ = v___y_395_;
v___y_380_ = v___y_387_;
v___y_381_ = v___y_390_;
v___y_382_ = v___y_391_;
v___y_383_ = v___y_392_;
v___y_384_ = v___y_390_;
goto v___jp_370_;
}
}
v___jp_405_:
{
lean_object* v_toCold_418_; lean_object* v_currRecDepth_419_; lean_object* v_ref_420_; uint8_t v_suppressElabErrors_421_; uint8_t v_checkDeprecated_422_; uint8_t v_isRecordingDeps_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_453_; 
v_toCold_418_ = lean_ctor_get(v___y_416_, 0);
v_currRecDepth_419_ = lean_ctor_get(v___y_416_, 1);
v_ref_420_ = lean_ctor_get(v___y_416_, 2);
v_suppressElabErrors_421_ = lean_ctor_get_uint8(v___y_416_, sizeof(void*)*3 + 2);
v_checkDeprecated_422_ = lean_ctor_get_uint8(v___y_416_, sizeof(void*)*3 + 3);
v_isRecordingDeps_423_ = lean_ctor_get_uint8(v___y_416_, sizeof(void*)*3 + 4);
v_isSharedCheck_453_ = !lean_is_exclusive(v___y_416_);
if (v_isSharedCheck_453_ == 0)
{
v___x_425_ = v___y_416_;
v_isShared_426_ = v_isSharedCheck_453_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_ref_420_);
lean_inc(v_currRecDepth_419_);
lean_inc(v_toCold_418_);
lean_dec(v___y_416_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_453_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_fileName_427_; lean_object* v_fileMap_428_; lean_object* v_currNamespace_429_; lean_object* v_openDecls_430_; lean_object* v_initHeartbeats_431_; lean_object* v_maxHeartbeats_432_; lean_object* v_quotContext_433_; lean_object* v_currMacroScope_434_; lean_object* v_cancelTk_x3f_435_; lean_object* v_inheritedTraceOptions_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_450_; 
v_fileName_427_ = lean_ctor_get(v_toCold_418_, 0);
v_fileMap_428_ = lean_ctor_get(v_toCold_418_, 1);
v_currNamespace_429_ = lean_ctor_get(v_toCold_418_, 4);
v_openDecls_430_ = lean_ctor_get(v_toCold_418_, 5);
v_initHeartbeats_431_ = lean_ctor_get(v_toCold_418_, 6);
v_maxHeartbeats_432_ = lean_ctor_get(v_toCold_418_, 7);
v_quotContext_433_ = lean_ctor_get(v_toCold_418_, 8);
v_currMacroScope_434_ = lean_ctor_get(v_toCold_418_, 9);
v_cancelTk_x3f_435_ = lean_ctor_get(v_toCold_418_, 10);
v_inheritedTraceOptions_436_ = lean_ctor_get(v_toCold_418_, 11);
v_isSharedCheck_450_ = !lean_is_exclusive(v_toCold_418_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_451_ = lean_ctor_get(v_toCold_418_, 3);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_toCold_418_, 2);
lean_dec(v_unused_452_);
v___x_438_ = v_toCold_418_;
v_isShared_439_ = v_isSharedCheck_450_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_inheritedTraceOptions_436_);
lean_inc(v_cancelTk_x3f_435_);
lean_inc(v_currMacroScope_434_);
lean_inc(v_quotContext_433_);
lean_inc(v_maxHeartbeats_432_);
lean_inc(v_initHeartbeats_431_);
lean_inc(v_openDecls_430_);
lean_inc(v_currNamespace_429_);
lean_inc(v_fileMap_428_);
lean_inc(v_fileName_427_);
lean_dec(v_toCold_418_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_450_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_411_, v___y_409_);
lean_inc_ref(v___y_411_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 3, v___x_440_);
lean_ctor_set(v___x_438_, 2, v___y_411_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_fileName_427_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_fileMap_428_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v___y_411_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_currNamespace_429_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v_openDecls_430_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_initHeartbeats_431_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_maxHeartbeats_432_);
lean_ctor_set(v_reuseFailAlloc_449_, 8, v_quotContext_433_);
lean_ctor_set(v_reuseFailAlloc_449_, 9, v_currMacroScope_434_);
lean_ctor_set(v_reuseFailAlloc_449_, 10, v_cancelTk_x3f_435_);
lean_ctor_set(v_reuseFailAlloc_449_, 11, v_inheritedTraceOptions_436_);
v___x_442_ = v_reuseFailAlloc_449_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_444_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_442_);
v___x_444_ = v___x_425_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_currRecDepth_419_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_ref_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*3 + 2, v_suppressElabErrors_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*3 + 3, v_checkDeprecated_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*3 + 4, v_isRecordingDeps_423_);
v___x_444_ = v_reuseFailAlloc_448_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_ctor_set_uint16(v___x_444_, sizeof(void*)*3, v___y_412_);
if (v_isRecordingDeps_423_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_446_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v___y_411_, v___x_445_, v___y_413_);
v___y_386_ = v___y_407_;
v___y_387_ = v___y_406_;
v___y_388_ = v___y_409_;
v___y_389_ = v___y_408_;
v___y_390_ = v___y_410_;
v___y_391_ = v___x_444_;
v___y_392_ = v___y_414_;
v___y_393_ = v___y_413_;
v___y_394_ = v___y_417_;
v___y_395_ = v___y_415_;
v___y_396_ = v___x_446_;
goto v___jp_385_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_411_);
v___y_386_ = v___y_407_;
v___y_387_ = v___y_406_;
v___y_388_ = v___y_409_;
v___y_389_ = v___y_408_;
v___y_390_ = v___y_410_;
v___y_391_ = v___x_444_;
v___y_392_ = v___y_414_;
v___y_393_ = v___y_413_;
v___y_394_ = v___y_417_;
v___y_395_ = v___y_415_;
v___y_396_ = v___x_447_;
goto v___jp_385_;
}
}
}
}
}
}
v___jp_454_:
{
lean_object* v___x_468_; lean_object* v_env_469_; lean_object* v_nextMacroScope_470_; lean_object* v_ngen_471_; lean_object* v_auxDeclNGen_472_; lean_object* v_traceState_473_; lean_object* v_recordedDeps_474_; lean_object* v_messages_475_; lean_object* v_infoState_476_; lean_object* v_snapshotTasks_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
v___x_468_ = lean_st_ref_take(v___y_464_);
v_env_469_ = lean_ctor_get(v___x_468_, 0);
v_nextMacroScope_470_ = lean_ctor_get(v___x_468_, 1);
v_ngen_471_ = lean_ctor_get(v___x_468_, 2);
v_auxDeclNGen_472_ = lean_ctor_get(v___x_468_, 3);
v_traceState_473_ = lean_ctor_get(v___x_468_, 4);
v_recordedDeps_474_ = lean_ctor_get(v___x_468_, 6);
v_messages_475_ = lean_ctor_get(v___x_468_, 7);
v_infoState_476_ = lean_ctor_get(v___x_468_, 8);
v_snapshotTasks_477_ = lean_ctor_get(v___x_468_, 9);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v___x_468_, 5);
lean_dec(v_unused_487_);
v___x_479_ = v___x_468_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snapshotTasks_477_);
lean_inc(v_infoState_476_);
lean_inc(v_messages_475_);
lean_inc(v_recordedDeps_474_);
lean_inc(v_traceState_473_);
lean_inc(v_auxDeclNGen_472_);
lean_inc(v_ngen_471_);
lean_inc(v_nextMacroScope_470_);
lean_inc(v_env_469_);
lean_dec(v___x_468_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = l_Lean_Kernel_enableDiag(v_env_469_, v___y_458_);
lean_inc_ref(v___y_460_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 5, v___y_460_);
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_nextMacroScope_470_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_ngen_471_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_auxDeclNGen_472_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_traceState_473_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v___y_460_);
lean_ctor_set(v_reuseFailAlloc_485_, 6, v_recordedDeps_474_);
lean_ctor_set(v_reuseFailAlloc_485_, 7, v_messages_475_);
lean_ctor_set(v_reuseFailAlloc_485_, 8, v_infoState_476_);
lean_ctor_set(v_reuseFailAlloc_485_, 9, v_snapshotTasks_477_);
v___x_483_ = v_reuseFailAlloc_485_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = lean_st_ref_put(v___y_464_, v___x_483_);
v___y_406_ = v___y_461_;
v___y_407_ = v___y_455_;
v___y_408_ = v___y_456_;
v___y_409_ = v___y_457_;
v___y_410_ = v___y_462_;
v___y_411_ = v___y_463_;
v___y_412_ = v___y_466_;
v___y_413_ = v___y_459_;
v___y_414_ = v___y_467_;
v___y_415_ = v___y_460_;
v___y_416_ = v___y_465_;
v___y_417_ = v___y_464_;
goto v___jp_405_;
}
}
}
v___jp_488_:
{
if (v___y_502_ == 0)
{
if (v___y_497_ == 0)
{
v___y_406_ = v___y_494_;
v___y_407_ = v___y_489_;
v___y_408_ = v___y_490_;
v___y_409_ = v___y_491_;
v___y_410_ = v___y_495_;
v___y_411_ = v___y_496_;
v___y_412_ = v___y_500_;
v___y_413_ = v___y_492_;
v___y_414_ = v___y_501_;
v___y_415_ = v___y_493_;
v___y_416_ = v___y_499_;
v___y_417_ = v___y_498_;
goto v___jp_405_;
}
else
{
v___y_455_ = v___y_489_;
v___y_456_ = v___y_490_;
v___y_457_ = v___y_491_;
v___y_458_ = v___y_502_;
v___y_459_ = v___y_492_;
v___y_460_ = v___y_493_;
v___y_461_ = v___y_494_;
v___y_462_ = v___y_495_;
v___y_463_ = v___y_496_;
v___y_464_ = v___y_498_;
v___y_465_ = v___y_499_;
v___y_466_ = v___y_500_;
v___y_467_ = v___y_501_;
goto v___jp_454_;
}
}
else
{
if (v___y_497_ == 0)
{
v___y_455_ = v___y_489_;
v___y_456_ = v___y_490_;
v___y_457_ = v___y_491_;
v___y_458_ = v___y_502_;
v___y_459_ = v___y_492_;
v___y_460_ = v___y_493_;
v___y_461_ = v___y_494_;
v___y_462_ = v___y_495_;
v___y_463_ = v___y_496_;
v___y_464_ = v___y_498_;
v___y_465_ = v___y_499_;
v___y_466_ = v___y_500_;
v___y_467_ = v___y_501_;
goto v___jp_454_;
}
else
{
v___y_406_ = v___y_494_;
v___y_407_ = v___y_489_;
v___y_408_ = v___y_490_;
v___y_409_ = v___y_491_;
v___y_410_ = v___y_495_;
v___y_411_ = v___y_496_;
v___y_412_ = v___y_500_;
v___y_413_ = v___y_492_;
v___y_414_ = v___y_501_;
v___y_415_ = v___y_493_;
v___y_416_ = v___y_499_;
v___y_417_ = v___y_498_;
goto v___jp_405_;
}
}
}
v___jp_503_:
{
uint16_t v___x_515_; lean_object* v___x_516_; lean_object* v_env_517_; uint8_t v___x_518_; uint16_t v___x_519_; uint16_t v___x_520_; uint16_t v___x_521_; uint8_t v___x_522_; 
v___x_515_ = l_Lean_OptionFlags_ofOptions(v___y_514_);
v___x_516_ = lean_st_ref_get(v___y_510_);
v_env_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc_ref(v_env_517_);
lean_dec(v___x_516_);
v___x_518_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_517_);
lean_dec_ref(v_env_517_);
v___x_519_ = 512;
v___x_520_ = lean_uint16_land(v___x_515_, v___x_519_);
v___x_521_ = 0;
v___x_522_ = lean_uint16_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
v___y_489_ = v___y_504_;
v___y_490_ = v___y_507_;
v___y_491_ = v___y_506_;
v___y_492_ = v___y_512_;
v___y_493_ = v___y_513_;
v___y_494_ = v___y_505_;
v___y_495_ = v___y_508_;
v___y_496_ = v___y_514_;
v___y_497_ = v___x_518_;
v___y_498_ = v___y_510_;
v___y_499_ = v___y_509_;
v___y_500_ = v___x_515_;
v___y_501_ = v___y_511_;
v___y_502_ = v___y_512_;
goto v___jp_488_;
}
else
{
v___y_489_ = v___y_504_;
v___y_490_ = v___y_507_;
v___y_491_ = v___y_506_;
v___y_492_ = v___y_512_;
v___y_493_ = v___y_513_;
v___y_494_ = v___y_505_;
v___y_495_ = v___y_508_;
v___y_496_ = v___y_514_;
v___y_497_ = v___x_518_;
v___y_498_ = v___y_510_;
v___y_499_ = v___y_509_;
v___y_500_ = v___x_515_;
v___y_501_ = v___y_511_;
v___y_502_ = v___y_508_;
goto v___jp_488_;
}
}
v___jp_523_:
{
lean_object* v_toCold_535_; lean_object* v_currRecDepth_536_; lean_object* v_ref_537_; uint8_t v_suppressElabErrors_538_; uint8_t v_checkDeprecated_539_; uint8_t v_isRecordingDeps_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_571_; 
v_toCold_535_ = lean_ctor_get(v___y_533_, 0);
v_currRecDepth_536_ = lean_ctor_get(v___y_533_, 1);
v_ref_537_ = lean_ctor_get(v___y_533_, 2);
v_suppressElabErrors_538_ = lean_ctor_get_uint8(v___y_533_, sizeof(void*)*3 + 2);
v_checkDeprecated_539_ = lean_ctor_get_uint8(v___y_533_, sizeof(void*)*3 + 3);
v_isRecordingDeps_540_ = lean_ctor_get_uint8(v___y_533_, sizeof(void*)*3 + 4);
v_isSharedCheck_571_ = !lean_is_exclusive(v___y_533_);
if (v_isSharedCheck_571_ == 0)
{
v___x_542_ = v___y_533_;
v_isShared_543_ = v_isSharedCheck_571_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_ref_537_);
lean_inc(v_currRecDepth_536_);
lean_inc(v_toCold_535_);
lean_dec(v___y_533_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_571_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_fileName_544_; lean_object* v_fileMap_545_; lean_object* v_currNamespace_546_; lean_object* v_openDecls_547_; lean_object* v_initHeartbeats_548_; lean_object* v_maxHeartbeats_549_; lean_object* v_quotContext_550_; lean_object* v_currMacroScope_551_; lean_object* v_cancelTk_x3f_552_; lean_object* v_inheritedTraceOptions_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_568_; 
v_fileName_544_ = lean_ctor_get(v_toCold_535_, 0);
v_fileMap_545_ = lean_ctor_get(v_toCold_535_, 1);
v_currNamespace_546_ = lean_ctor_get(v_toCold_535_, 4);
v_openDecls_547_ = lean_ctor_get(v_toCold_535_, 5);
v_initHeartbeats_548_ = lean_ctor_get(v_toCold_535_, 6);
v_maxHeartbeats_549_ = lean_ctor_get(v_toCold_535_, 7);
v_quotContext_550_ = lean_ctor_get(v_toCold_535_, 8);
v_currMacroScope_551_ = lean_ctor_get(v_toCold_535_, 9);
v_cancelTk_x3f_552_ = lean_ctor_get(v_toCold_535_, 10);
v_inheritedTraceOptions_553_ = lean_ctor_get(v_toCold_535_, 11);
v_isSharedCheck_568_ = !lean_is_exclusive(v_toCold_535_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_569_ = lean_ctor_get(v_toCold_535_, 3);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_toCold_535_, 2);
lean_dec(v_unused_570_);
v___x_555_ = v_toCold_535_;
v_isShared_556_ = v_isSharedCheck_568_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_inheritedTraceOptions_553_);
lean_inc(v_cancelTk_x3f_552_);
lean_inc(v_currMacroScope_551_);
lean_inc(v_quotContext_550_);
lean_inc(v_maxHeartbeats_549_);
lean_inc(v_initHeartbeats_548_);
lean_inc(v_openDecls_547_);
lean_inc(v_currNamespace_546_);
lean_inc(v_fileMap_545_);
lean_inc(v_fileName_544_);
lean_dec(v_toCold_535_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_568_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = l_Lean_maxRecDepth;
v___x_558_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___y_529_, v___x_557_);
lean_inc_ref(v___y_529_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 3, v___x_558_);
lean_ctor_set(v___x_555_, 2, v___y_529_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_fileName_544_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_fileMap_545_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v___y_529_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_currNamespace_546_);
lean_ctor_set(v_reuseFailAlloc_567_, 5, v_openDecls_547_);
lean_ctor_set(v_reuseFailAlloc_567_, 6, v_initHeartbeats_548_);
lean_ctor_set(v_reuseFailAlloc_567_, 7, v_maxHeartbeats_549_);
lean_ctor_set(v_reuseFailAlloc_567_, 8, v_quotContext_550_);
lean_ctor_set(v_reuseFailAlloc_567_, 9, v_currMacroScope_551_);
lean_ctor_set(v_reuseFailAlloc_567_, 10, v_cancelTk_x3f_552_);
lean_ctor_set(v_reuseFailAlloc_567_, 11, v_inheritedTraceOptions_553_);
v___x_560_ = v_reuseFailAlloc_567_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_560_);
v___x_562_ = v___x_542_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_currRecDepth_536_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_ref_537_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3 + 2, v_suppressElabErrors_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3 + 3, v_checkDeprecated_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3 + 4, v_isRecordingDeps_540_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_uint16(v___x_562_, sizeof(void*)*3, v___y_528_);
if (v_isRecordingDeps_540_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_564_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v___y_529_, v___x_563_, v_isRecordingDeps_540_);
v___y_504_ = v___y_525_;
v___y_505_ = v___y_524_;
v___y_506_ = v___x_557_;
v___y_507_ = v___y_526_;
v___y_508_ = v___y_527_;
v___y_509_ = v___x_562_;
v___y_510_ = v___y_534_;
v___y_511_ = v___y_531_;
v___y_512_ = v___y_530_;
v___y_513_ = v___y_532_;
v___y_514_ = v___x_564_;
goto v___jp_503_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v___y_529_);
v___y_504_ = v___y_525_;
v___y_505_ = v___y_524_;
v___y_506_ = v___x_557_;
v___y_507_ = v___y_526_;
v___y_508_ = v___y_527_;
v___y_509_ = v___x_562_;
v___y_510_ = v___y_534_;
v___y_511_ = v___y_531_;
v___y_512_ = v___y_530_;
v___y_513_ = v___y_532_;
v___y_514_ = v___x_565_;
goto v___jp_503_;
}
}
}
}
}
}
v___jp_572_:
{
lean_object* v___x_585_; lean_object* v_env_586_; lean_object* v_nextMacroScope_587_; lean_object* v_ngen_588_; lean_object* v_auxDeclNGen_589_; lean_object* v_traceState_590_; lean_object* v_recordedDeps_591_; lean_object* v_messages_592_; lean_object* v_infoState_593_; lean_object* v_snapshotTasks_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v___x_585_ = lean_st_ref_take(v___y_584_);
v_env_586_ = lean_ctor_get(v___x_585_, 0);
v_nextMacroScope_587_ = lean_ctor_get(v___x_585_, 1);
v_ngen_588_ = lean_ctor_get(v___x_585_, 2);
v_auxDeclNGen_589_ = lean_ctor_get(v___x_585_, 3);
v_traceState_590_ = lean_ctor_get(v___x_585_, 4);
v_recordedDeps_591_ = lean_ctor_get(v___x_585_, 6);
v_messages_592_ = lean_ctor_get(v___x_585_, 7);
v_infoState_593_ = lean_ctor_get(v___x_585_, 8);
v_snapshotTasks_594_ = lean_ctor_get(v___x_585_, 9);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_585_, 5);
lean_dec(v_unused_604_);
v___x_596_ = v___x_585_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snapshotTasks_594_);
lean_inc(v_infoState_593_);
lean_inc(v_messages_592_);
lean_inc(v_recordedDeps_591_);
lean_inc(v_traceState_590_);
lean_inc(v_auxDeclNGen_589_);
lean_inc(v_ngen_588_);
lean_inc(v_nextMacroScope_587_);
lean_inc(v_env_586_);
lean_dec(v___x_585_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Lean_Kernel_enableDiag(v_env_586_, v___y_574_);
lean_inc_ref(v___y_579_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 5, v___y_579_);
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_nextMacroScope_587_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_ngen_588_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_auxDeclNGen_589_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_traceState_590_);
lean_ctor_set(v_reuseFailAlloc_602_, 5, v___y_579_);
lean_ctor_set(v_reuseFailAlloc_602_, 6, v_recordedDeps_591_);
lean_ctor_set(v_reuseFailAlloc_602_, 7, v_messages_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 8, v_infoState_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 9, v_snapshotTasks_594_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_st_ref_put(v___y_584_, v___x_600_);
v___y_524_ = v___y_580_;
v___y_525_ = v___y_573_;
v___y_526_ = v___y_575_;
v___y_527_ = v___y_581_;
v___y_528_ = v___y_576_;
v___y_529_ = v___y_577_;
v___y_530_ = v___y_578_;
v___y_531_ = v___y_583_;
v___y_532_ = v___y_579_;
v___y_533_ = v___y_582_;
v___y_534_ = v___y_584_;
goto v___jp_523_;
}
}
}
v___jp_605_:
{
if (v___y_618_ == 0)
{
if (v___y_614_ == 0)
{
v___y_524_ = v___y_612_;
v___y_525_ = v___y_606_;
v___y_526_ = v___y_607_;
v___y_527_ = v___y_613_;
v___y_528_ = v___y_608_;
v___y_529_ = v___y_609_;
v___y_530_ = v___y_610_;
v___y_531_ = v___y_616_;
v___y_532_ = v___y_611_;
v___y_533_ = v___y_615_;
v___y_534_ = v___y_617_;
goto v___jp_523_;
}
else
{
v___y_573_ = v___y_606_;
v___y_574_ = v___y_618_;
v___y_575_ = v___y_607_;
v___y_576_ = v___y_608_;
v___y_577_ = v___y_609_;
v___y_578_ = v___y_610_;
v___y_579_ = v___y_611_;
v___y_580_ = v___y_612_;
v___y_581_ = v___y_613_;
v___y_582_ = v___y_615_;
v___y_583_ = v___y_616_;
v___y_584_ = v___y_617_;
goto v___jp_572_;
}
}
else
{
if (v___y_614_ == 0)
{
v___y_573_ = v___y_606_;
v___y_574_ = v___y_618_;
v___y_575_ = v___y_607_;
v___y_576_ = v___y_608_;
v___y_577_ = v___y_609_;
v___y_578_ = v___y_610_;
v___y_579_ = v___y_611_;
v___y_580_ = v___y_612_;
v___y_581_ = v___y_613_;
v___y_582_ = v___y_615_;
v___y_583_ = v___y_616_;
v___y_584_ = v___y_617_;
goto v___jp_572_;
}
else
{
v___y_524_ = v___y_612_;
v___y_525_ = v___y_606_;
v___y_526_ = v___y_607_;
v___y_527_ = v___y_613_;
v___y_528_ = v___y_608_;
v___y_529_ = v___y_609_;
v___y_530_ = v___y_610_;
v___y_531_ = v___y_616_;
v___y_532_ = v___y_611_;
v___y_533_ = v___y_615_;
v___y_534_ = v___y_617_;
goto v___jp_523_;
}
}
}
v___jp_619_:
{
uint16_t v___x_630_; lean_object* v___x_631_; lean_object* v_env_632_; uint8_t v___x_633_; uint16_t v___x_634_; uint16_t v___x_635_; uint16_t v___x_636_; uint8_t v___x_637_; 
v___x_630_ = l_Lean_OptionFlags_ofOptions(v___y_629_);
v___x_631_ = lean_st_ref_get(v___y_628_);
v_env_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_env_632_);
lean_dec(v___x_631_);
v___x_633_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_632_);
lean_dec_ref(v_env_632_);
v___x_634_ = 512;
v___x_635_ = lean_uint16_land(v___x_630_, v___x_634_);
v___x_636_ = 0;
v___x_637_ = lean_uint16_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
v___y_606_ = v___y_620_;
v___y_607_ = v___y_622_;
v___y_608_ = v___x_630_;
v___y_609_ = v___y_629_;
v___y_610_ = v___y_626_;
v___y_611_ = v___y_627_;
v___y_612_ = v___y_621_;
v___y_613_ = v___y_623_;
v___y_614_ = v___x_633_;
v___y_615_ = v___y_624_;
v___y_616_ = v___y_625_;
v___y_617_ = v___y_628_;
v___y_618_ = v___y_626_;
goto v___jp_605_;
}
else
{
v___y_606_ = v___y_620_;
v___y_607_ = v___y_622_;
v___y_608_ = v___x_630_;
v___y_609_ = v___y_629_;
v___y_610_ = v___y_626_;
v___y_611_ = v___y_627_;
v___y_612_ = v___y_621_;
v___y_613_ = v___y_623_;
v___y_614_ = v___x_633_;
v___y_615_ = v___y_624_;
v___y_616_ = v___y_625_;
v___y_617_ = v___y_628_;
v___y_618_ = v___y_623_;
goto v___jp_605_;
}
}
v___jp_638_:
{
lean_object* v___x_648_; 
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc_ref(v___y_643_);
v___x_648_ = lean_infer_type(v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_n(v_a_649_, 2);
lean_dec_ref_known(v___x_648_, 1);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
v___x_650_ = lean_apply_6(v_checkType_273_, v_a_649_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, lean_box(0));
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_env_658_; lean_object* v_nextMacroScope_659_; lean_object* v_ngen_660_; lean_object* v_auxDeclNGen_661_; lean_object* v_traceState_662_; lean_object* v_recordedDeps_663_; lean_object* v_messages_664_; lean_object* v_infoState_665_; lean_object* v_snapshotTasks_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref_known(v___x_650_, 1);
v___x_651_ = lean_array_to_list(v___y_641_);
lean_inc_n(v___y_639_, 2);
v___x_652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_652_, 0, v___y_639_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_ctor_set(v___x_652_, 2, v_a_649_);
v___x_653_ = lean_box(0);
lean_inc(v___y_640_);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___y_639_);
lean_ctor_set(v___x_654_, 1, v___y_640_);
v___x_655_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_655_, 0, v___x_652_);
lean_ctor_set(v___x_655_, 1, v___y_643_);
lean_ctor_set(v___x_655_, 2, v___x_653_);
lean_ctor_set(v___x_655_, 3, v___x_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*4, v_safety_274_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = lean_st_ref_take(v___y_647_);
v_env_658_ = lean_ctor_get(v___x_657_, 0);
v_nextMacroScope_659_ = lean_ctor_get(v___x_657_, 1);
v_ngen_660_ = lean_ctor_get(v___x_657_, 2);
v_auxDeclNGen_661_ = lean_ctor_get(v___x_657_, 3);
v_traceState_662_ = lean_ctor_get(v___x_657_, 4);
v_recordedDeps_663_ = lean_ctor_get(v___x_657_, 6);
v_messages_664_ = lean_ctor_get(v___x_657_, 7);
v_infoState_665_ = lean_ctor_get(v___x_657_, 8);
v_snapshotTasks_666_ = lean_ctor_get(v___x_657_, 9);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___x_657_, 5);
lean_dec(v_unused_716_);
v___x_668_ = v___x_657_;
v_isShared_669_ = v_isSharedCheck_715_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_snapshotTasks_666_);
lean_inc(v_infoState_665_);
lean_inc(v_messages_664_);
lean_inc(v_recordedDeps_663_);
lean_inc(v_traceState_662_);
lean_inc(v_auxDeclNGen_661_);
lean_inc(v_ngen_660_);
lean_inc(v_nextMacroScope_659_);
lean_inc(v_env_658_);
lean_dec(v___x_657_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_715_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
lean_inc(v___y_639_);
v___x_670_ = l_Lean_markMeta(v_env_658_, v___y_639_);
v___x_671_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_672_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 5, v___x_672_);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_nextMacroScope_659_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_ngen_660_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_auxDeclNGen_661_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_traceState_662_);
lean_ctor_set(v_reuseFailAlloc_714_, 5, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_714_, 6, v_recordedDeps_663_);
lean_ctor_set(v_reuseFailAlloc_714_, 7, v_messages_664_);
lean_ctor_set(v_reuseFailAlloc_714_, 8, v_infoState_665_);
lean_ctor_set(v_reuseFailAlloc_714_, 9, v_snapshotTasks_666_);
v___x_674_ = v_reuseFailAlloc_714_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_mctx_677_; lean_object* v_zetaDeltaFVarIds_678_; lean_object* v_postponed_679_; lean_object* v_diag_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_712_; 
v___x_675_ = lean_st_ref_put(v___y_647_, v___x_674_);
v___x_676_ = lean_st_ref_take(v___y_645_);
v_mctx_677_ = lean_ctor_get(v___x_676_, 0);
v_zetaDeltaFVarIds_678_ = lean_ctor_get(v___x_676_, 2);
v_postponed_679_ = lean_ctor_get(v___x_676_, 3);
v_diag_680_ = lean_ctor_get(v___x_676_, 4);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_676_, 1);
lean_dec(v_unused_713_);
v___x_682_ = v___x_676_;
v_isShared_683_ = v_isSharedCheck_712_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_diag_680_);
lean_inc(v_postponed_679_);
lean_inc(v_zetaDeltaFVarIds_678_);
lean_inc(v_mctx_677_);
lean_dec(v___x_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_712_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_684_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_685_, 0, v___x_671_);
lean_ctor_set(v___x_685_, 1, v___x_671_);
lean_ctor_set(v___x_685_, 2, v___y_642_);
v___x_686_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_671_);
lean_ctor_set(v___x_686_, 2, v___x_671_);
lean_ctor_set(v___x_686_, 3, v___x_671_);
lean_ctor_set(v___x_686_, 4, v___x_671_);
lean_ctor_set(v___x_686_, 5, v___x_671_);
lean_ctor_set(v___x_686_, 6, v___x_671_);
lean_ctor_set(v___x_686_, 7, v___x_685_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_686_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_mctx_677_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_zetaDeltaFVarIds_678_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_postponed_679_);
lean_ctor_set(v_reuseFailAlloc_711_, 4, v_diag_680_);
v___x_688_ = v_reuseFailAlloc_711_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_env_691_; lean_object* v_checked_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = lean_st_ref_put(v___y_645_, v___x_688_);
v___x_690_ = lean_st_ref_get(v___y_647_);
v_env_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_env_691_);
lean_dec(v___x_690_);
v_checked_692_ = lean_ctor_get(v_env_691_, 2);
lean_inc_ref(v_checked_692_);
lean_dec_ref(v_env_691_);
v___x_693_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3));
v___x_694_ = l_Lean_traceBlock___redArg(v___x_693_, v_checked_692_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_toCold_695_; uint8_t v_isRecordingDeps_696_; lean_object* v_options_697_; uint8_t v___x_698_; uint8_t v___x_699_; 
lean_dec_ref_known(v___x_694_, 1);
v_toCold_695_ = lean_ctor_get(v___y_646_, 0);
v_isRecordingDeps_696_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 4);
v_options_697_ = lean_ctor_get(v_toCold_695_, 2);
v___x_698_ = 1;
v___x_699_ = 0;
if (v_isRecordingDeps_696_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = l_Lean_Elab_async;
lean_inc_ref(v_options_697_);
v___x_701_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__4(v_options_697_, v___x_700_, v_isRecordingDeps_696_);
v___y_620_ = v___y_639_;
v___y_621_ = v___y_645_;
v___y_622_ = v___y_644_;
v___y_623_ = v___x_699_;
v___y_624_ = v___y_646_;
v___y_625_ = v___x_656_;
v___y_626_ = v___x_698_;
v___y_627_ = v___x_672_;
v___y_628_ = v___y_647_;
v___y_629_ = v___x_701_;
goto v___jp_619_;
}
else
{
lean_object* v___x_702_; 
lean_inc_ref(v_options_697_);
v___x_702_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_697_);
v___y_620_ = v___y_639_;
v___y_621_ = v___y_645_;
v___y_622_ = v___y_644_;
v___y_623_ = v___x_699_;
v___y_624_ = v___y_646_;
v___y_625_ = v___x_656_;
v___y_626_ = v___x_698_;
v___y_627_ = v___x_672_;
v___y_628_ = v___y_647_;
v___y_629_ = v___x_702_;
goto v___jp_619_;
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref_known(v___x_656_, 1);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_639_);
v_a_703_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_694_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_694_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
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
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_a_649_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_639_);
v_a_717_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_650_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_650_);
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
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_639_);
lean_dec_ref(v_checkType_273_);
v_a_725_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_648_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_648_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
v___jp_733_:
{
lean_object* v___x_734_; lean_object* v_env_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_st_ref_get(v___y_279_);
v_env_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_env_735_);
lean_dec(v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5));
v___x_737_ = l_Lean_Core_mkFreshUserName(v___x_736_, v___y_278_, v___y_279_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = l_Lean_mkPrivateName(v_env_735_, v_a_738_);
lean_dec_ref(v_env_735_);
v___x_740_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_275_, v___y_277_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_params_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc_n(v_a_741_, 2);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9);
v___x_744_ = l_Lean_collectLevelParams(v___x_743_, v_a_741_);
v_params_745_ = lean_ctor_get(v___x_744_, 2);
lean_inc_ref(v_params_745_);
lean_dec_ref(v___x_744_);
v___x_746_ = lean_box(0);
v___x_747_ = l_Lean_Expr_hasMVar(v_a_741_);
if (v___x_747_ == 0)
{
v___y_639_ = v___x_739_;
v___y_640_ = v___x_746_;
v___y_641_ = v_params_745_;
v___y_642_ = v___x_742_;
v___y_643_ = v_a_741_;
v___y_644_ = v___y_276_;
v___y_645_ = v___y_277_;
v___y_646_ = v___y_278_;
v___y_647_ = v___y_279_;
goto v___jp_638_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11);
lean_inc(v_a_741_);
v___x_749_ = l_Lean_indentExpr(v_a_741_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_750_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_dec_ref_known(v___x_751_, 1);
v___y_639_ = v___x_739_;
v___y_640_ = v___x_746_;
v___y_641_ = v_params_745_;
v___y_642_ = v___x_742_;
v___y_643_ = v_a_741_;
v___y_644_ = v___y_276_;
v___y_645_ = v___y_277_;
v___y_646_ = v___y_278_;
v___y_647_ = v___y_279_;
goto v___jp_638_;
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v_params_745_);
lean_dec(v_a_741_);
lean_dec(v___x_739_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec_ref(v_checkType_273_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v___x_739_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec_ref(v_checkType_273_);
v_a_760_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_740_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_740_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_env_735_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec_ref(v_value_275_);
lean_dec_ref(v_checkType_273_);
v_a_768_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_737_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_737_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
v___jp_776_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_mctx_790_; lean_object* v_zetaDeltaFVarIds_791_; lean_object* v_postponed_792_; lean_object* v_diag_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_802_; 
v___x_786_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_787_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_787_, 0, v___y_785_);
lean_ctor_set(v___x_787_, 1, v_nextMacroScope_777_);
lean_ctor_set(v___x_787_, 2, v_ngen_778_);
lean_ctor_set(v___x_787_, 3, v_auxDeclNGen_779_);
lean_ctor_set(v___x_787_, 4, v_traceState_780_);
lean_ctor_set(v___x_787_, 5, v___x_786_);
lean_ctor_set(v___x_787_, 6, v_recordedDeps_781_);
lean_ctor_set(v___x_787_, 7, v_messages_782_);
lean_ctor_set(v___x_787_, 8, v_infoState_783_);
lean_ctor_set(v___x_787_, 9, v_snapshotTasks_784_);
v___x_788_ = lean_st_ref_put(v___y_279_, v___x_787_);
v___x_789_ = lean_st_ref_take(v___y_277_);
v_mctx_790_ = lean_ctor_get(v___x_789_, 0);
v_zetaDeltaFVarIds_791_ = lean_ctor_get(v___x_789_, 2);
v_postponed_792_ = lean_ctor_get(v___x_789_, 3);
v_diag_793_ = lean_ctor_get(v___x_789_, 4);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_789_, 1);
lean_dec(v_unused_803_);
v___x_795_ = v___x_789_;
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_diag_793_);
lean_inc(v_postponed_792_);
lean_inc(v_zetaDeltaFVarIds_791_);
lean_inc(v_mctx_790_);
lean_dec(v___x_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_mctx_790_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_zetaDeltaFVarIds_791_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_postponed_792_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_diag_793_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_st_ref_put(v___y_277_, v___x_799_);
goto v___jp_733_;
}
}
}
v___jp_805_:
{
lean_object* v___x_806_; lean_object* v_env_807_; lean_object* v_nextMacroScope_808_; lean_object* v_ngen_809_; lean_object* v_auxDeclNGen_810_; lean_object* v_traceState_811_; lean_object* v_recordedDeps_812_; lean_object* v_messages_813_; lean_object* v_infoState_814_; lean_object* v_snapshotTasks_815_; lean_object* v___x_816_; 
v___x_806_ = lean_st_ref_take(v___y_279_);
v_env_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref_n(v_env_807_, 2);
v_nextMacroScope_808_ = lean_ctor_get(v___x_806_, 1);
lean_inc(v_nextMacroScope_808_);
v_ngen_809_ = lean_ctor_get(v___x_806_, 2);
lean_inc_ref(v_ngen_809_);
v_auxDeclNGen_810_ = lean_ctor_get(v___x_806_, 3);
lean_inc_ref(v_auxDeclNGen_810_);
v_traceState_811_ = lean_ctor_get(v___x_806_, 4);
lean_inc_ref(v_traceState_811_);
v_recordedDeps_812_ = lean_ctor_get(v___x_806_, 6);
lean_inc_ref(v_recordedDeps_812_);
v_messages_813_ = lean_ctor_get(v___x_806_, 7);
lean_inc_ref(v_messages_813_);
v_infoState_814_ = lean_ctor_get(v___x_806_, 8);
lean_inc_ref(v_infoState_814_);
v_snapshotTasks_815_ = lean_ctor_get(v___x_806_, 9);
lean_inc_ref(v_snapshotTasks_815_);
lean_dec(v___x_806_);
v___x_816_ = l_Lean_Environment_importEnv_x3f(v_env_807_);
if (lean_obj_tag(v___x_816_) == 0)
{
v_nextMacroScope_777_ = v_nextMacroScope_808_;
v_ngen_778_ = v_ngen_809_;
v_auxDeclNGen_779_ = v_auxDeclNGen_810_;
v_traceState_780_ = v_traceState_811_;
v_recordedDeps_781_ = v_recordedDeps_812_;
v_messages_782_ = v_messages_813_;
v_infoState_783_ = v_infoState_814_;
v_snapshotTasks_784_ = v_snapshotTasks_815_;
v___y_785_ = v_env_807_;
goto v___jp_776_;
}
else
{
lean_object* v_val_817_; 
lean_dec_ref(v_env_807_);
v_val_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v___x_816_, 1);
v_nextMacroScope_777_ = v_nextMacroScope_808_;
v_ngen_778_ = v_ngen_809_;
v_auxDeclNGen_779_ = v_auxDeclNGen_810_;
v_traceState_780_ = v_traceState_811_;
v_recordedDeps_781_ = v_recordedDeps_812_;
v_messages_782_ = v_messages_813_;
v_infoState_783_ = v_infoState_814_;
v_snapshotTasks_784_ = v_snapshotTasks_815_;
v___y_785_ = v_val_817_;
goto v___jp_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_826_, lean_object* v_checkType_827_, lean_object* v_safety_828_, lean_object* v_value_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v_checkMeta_boxed_835_; uint8_t v_safety_boxed_836_; lean_object* v_res_837_; 
v_checkMeta_boxed_835_ = lean_unbox(v_checkMeta_826_);
v_safety_boxed_836_ = lean_unbox(v_safety_828_);
v_res_837_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_835_, v_checkType_827_, v_safety_boxed_836_, v_value_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(lean_object* v_env_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; lean_object* v_nextMacroScope_843_; lean_object* v_ngen_844_; lean_object* v_auxDeclNGen_845_; lean_object* v_traceState_846_; lean_object* v_recordedDeps_847_; lean_object* v_messages_848_; lean_object* v_infoState_849_; lean_object* v_snapshotTasks_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_876_; 
v___x_842_ = lean_st_ref_take(v___y_840_);
v_nextMacroScope_843_ = lean_ctor_get(v___x_842_, 1);
v_ngen_844_ = lean_ctor_get(v___x_842_, 2);
v_auxDeclNGen_845_ = lean_ctor_get(v___x_842_, 3);
v_traceState_846_ = lean_ctor_get(v___x_842_, 4);
v_recordedDeps_847_ = lean_ctor_get(v___x_842_, 6);
v_messages_848_ = lean_ctor_get(v___x_842_, 7);
v_infoState_849_ = lean_ctor_get(v___x_842_, 8);
v_snapshotTasks_850_ = lean_ctor_get(v___x_842_, 9);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; lean_object* v_unused_878_; 
v_unused_877_ = lean_ctor_get(v___x_842_, 5);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_878_);
v___x_852_ = v___x_842_;
v_isShared_853_ = v_isSharedCheck_876_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snapshotTasks_850_);
lean_inc(v_infoState_849_);
lean_inc(v_messages_848_);
lean_inc(v_recordedDeps_847_);
lean_inc(v_traceState_846_);
lean_inc(v_auxDeclNGen_845_);
lean_inc(v_ngen_844_);
lean_inc(v_nextMacroScope_843_);
lean_dec(v___x_842_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_876_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 5, v___x_854_);
lean_ctor_set(v___x_852_, 0, v_env_838_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_env_838_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_nextMacroScope_843_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_ngen_844_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_auxDeclNGen_845_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_traceState_846_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_875_, 6, v_recordedDeps_847_);
lean_ctor_set(v_reuseFailAlloc_875_, 7, v_messages_848_);
lean_ctor_set(v_reuseFailAlloc_875_, 8, v_infoState_849_);
lean_ctor_set(v_reuseFailAlloc_875_, 9, v_snapshotTasks_850_);
v___x_856_ = v_reuseFailAlloc_875_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_mctx_859_; lean_object* v_zetaDeltaFVarIds_860_; lean_object* v_postponed_861_; lean_object* v_diag_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_873_; 
v___x_857_ = lean_st_ref_put(v___y_840_, v___x_856_);
v___x_858_ = lean_st_ref_take(v___y_839_);
v_mctx_859_ = lean_ctor_get(v___x_858_, 0);
v_zetaDeltaFVarIds_860_ = lean_ctor_get(v___x_858_, 2);
v_postponed_861_ = lean_ctor_get(v___x_858_, 3);
v_diag_862_ = lean_ctor_get(v___x_858_, 4);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v___x_858_, 1);
lean_dec(v_unused_874_);
v___x_864_ = v___x_858_;
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_diag_862_);
lean_inc(v_postponed_861_);
lean_inc(v_zetaDeltaFVarIds_860_);
lean_inc(v_mctx_859_);
lean_dec(v___x_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_866_ = lean_box(0);
v___x_867_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_mctx_859_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_zetaDeltaFVarIds_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_postponed_861_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_diag_862_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_st_ref_put(v___y_839_, v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_866_);
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg___boxed(lean_object* v_env_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_884_, lean_object* v_x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_env_892_; lean_object* v_a_894_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_891_ = lean_st_ref_get(v___y_889_);
v_env_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_env_892_);
lean_dec(v___x_891_);
v___x_904_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_884_, v___y_887_, v___y_889_);
lean_dec_ref(v___x_904_);
lean_inc(v___y_889_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
v___x_905_ = lean_apply_5(v_x_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, lean_box(0));
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_892_, v___y_887_, v___y_889_);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_907_, 0);
lean_dec(v_unused_915_);
v___x_909_ = v___x_907_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_dec(v___x_907_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_a_906_);
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_906_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_a_916_; 
v_a_916_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_905_, 1);
v_a_894_ = v_a_916_;
goto v___jp_893_;
}
v___jp_893_:
{
lean_object* v___x_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v___x_895_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_892_, v___y_887_, v___y_889_);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_895_, 0);
lean_dec(v_unused_903_);
v___x_897_ = v___x_895_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_dec(v___x_895_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 1);
lean_ctor_set(v___x_897_, 0, v_a_894_);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_894_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_917_, v_x_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_925_, lean_object* v_checkType_926_, uint8_t v_safety_927_, uint8_t v_checkMeta_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v_env_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_934_ = lean_box(v_checkMeta_928_);
v___x_935_ = lean_box(v_safety_927_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_936_, 0, v___x_934_);
lean_closure_set(v___f_936_, 1, v_checkType_926_);
lean_closure_set(v___f_936_, 2, v___x_935_);
lean_closure_set(v___f_936_, 3, v_value_925_);
v___x_937_ = lean_st_ref_get(v_a_932_);
v_env_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_env_938_);
lean_dec(v___x_937_);
v___x_939_ = l_Lean_Environment_unlockAsync(v_env_938_);
v___x_940_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_939_, v___f_936_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_941_, lean_object* v_checkType_942_, lean_object* v_safety_943_, lean_object* v_checkMeta_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
uint8_t v_safety_boxed_950_; uint8_t v_checkMeta_boxed_951_; lean_object* v_res_952_; 
v_safety_boxed_950_ = lean_unbox(v_safety_943_);
v_checkMeta_boxed_951_ = lean_unbox(v_checkMeta_944_);
v_res_952_ = l_Lean_Meta_evalExprCore___redArg(v_value_941_, v_checkType_942_, v_safety_boxed_950_, v_checkMeta_boxed_951_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_953_, lean_object* v_value_954_, lean_object* v_checkType_955_, uint8_t v_safety_956_, uint8_t v_checkMeta_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Meta_evalExprCore___redArg(v_value_954_, v_checkType_955_, v_safety_956_, v_checkMeta_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_964_, lean_object* v_value_965_, lean_object* v_checkType_966_, lean_object* v_safety_967_, lean_object* v_checkMeta_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
uint8_t v_safety_boxed_974_; uint8_t v_checkMeta_boxed_975_; lean_object* v_res_976_; 
v_safety_boxed_974_ = lean_unbox(v_safety_967_);
v_checkMeta_boxed_975_ = lean_unbox(v_checkMeta_968_);
v_res_976_ = l_Lean_Meta_evalExprCore(v_00_u03b1_964_, v_value_965_, v_checkType_966_, v_safety_boxed_974_, v_checkMeta_boxed_975_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_00_u03b2_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg(){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg___boxed(lean_object* v___dummy_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1___redArg();
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_00_u03b2_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(lean_object* v_00_u03b1_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___redArg();
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5___boxed(lean_object* v_00_u03b1_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__5(v_00_u03b1_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_00_u03b1_999_, lean_object* v_constName_1000_, uint8_t v_checkMeta_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___redArg(v_constName_1000_, v_checkMeta_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_constName_1009_, lean_object* v_checkMeta_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v_checkMeta_boxed_1016_; lean_object* v_res_1017_; 
v_checkMeta_boxed_1016_ = lean_unbox(v_checkMeta_1010_);
v_res_1017_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3(v_00_u03b1_1008_, v_constName_1009_, v_checkMeta_boxed_1016_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_1026_, v_msg_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_1034_, lean_object* v_env_1035_, lean_object* v_x_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_1035_, v_x_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_env_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_1043_, v_env_1044_, v_x_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(lean_object* v_00_u03b1_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___redArg(v_x_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__3_spec__4(v_00_u03b1_1060_, v_x_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12(lean_object* v_env_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___redArg(v_env_1068_, v___y_1070_, v___y_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12___boxed(lean_object* v_env_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__12(v_env_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1085_, lean_object* v_type_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Meta_whnfD(v_type_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1106_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_Expr_isConstOf(v_a_1093_, v_typeName_1085_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_del_object(v___x_1095_);
v___x_1098_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1099_ = l_Lean_indentExpr(v_a_1093_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1100_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec(v_a_1093_);
v___x_1102_ = lean_box(0);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1102_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
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
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1092_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1092_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1115_, lean_object* v_type_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1115_, v_type_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v_typeName_1115_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1123_, lean_object* v_value_1124_, uint8_t v_safety_1125_, uint8_t v_checkMeta_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1132_, 0, v_typeName_1123_);
v___x_1133_ = l_Lean_Meta_evalExprCore___redArg(v_value_1124_, v___f_1132_, v_safety_1125_, v_checkMeta_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1134_, lean_object* v_value_1135_, lean_object* v_safety_1136_, lean_object* v_checkMeta_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
uint8_t v_safety_boxed_1143_; uint8_t v_checkMeta_boxed_1144_; lean_object* v_res_1145_; 
v_safety_boxed_1143_ = lean_unbox(v_safety_1136_);
v_checkMeta_boxed_1144_ = lean_unbox(v_checkMeta_1137_);
v_res_1145_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1134_, v_value_1135_, v_safety_boxed_1143_, v_checkMeta_boxed_1144_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1146_, lean_object* v_typeName_1147_, lean_object* v_value_1148_, uint8_t v_safety_1149_, uint8_t v_checkMeta_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1147_, v_value_1148_, v_safety_1149_, v_checkMeta_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_typeName_1158_, lean_object* v_value_1159_, lean_object* v_safety_1160_, lean_object* v_checkMeta_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
uint8_t v_safety_boxed_1167_; uint8_t v_checkMeta_boxed_1168_; lean_object* v_res_1169_; 
v_safety_boxed_1167_ = lean_unbox(v_safety_1160_);
v_checkMeta_boxed_1168_ = lean_unbox(v_checkMeta_1161_);
v_res_1169_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1157_, v_typeName_1158_, v_value_1159_, v_safety_boxed_1167_, v_checkMeta_boxed_1168_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1169_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1175_, lean_object* v_type_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
lean_inc_ref(v_expectedType_1175_);
lean_inc_ref(v_type_1176_);
v___x_1182_ = l_Lean_Meta_isExprDefEq(v_type_1176_, v_expectedType_1175_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1207_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1207_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1207_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_unbox(v_a_1183_);
lean_dec(v_a_1183_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_del_object(v___x_1185_);
v___x_1188_ = lean_box(0);
v___x_1189_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1190_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1176_, v_expectedType_1175_, v___x_1188_, v___x_1189_, v___y_1177_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v_a_1191_);
v___x_1194_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1193_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1194_;
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1190_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1190_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_dec_ref(v_type_1176_);
lean_dec_ref(v_expectedType_1175_);
v___x_1203_ = lean_box(0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1203_);
v___x_1205_ = v___x_1185_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v_type_1176_);
lean_dec_ref(v_expectedType_1175_);
v_a_1208_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1182_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1182_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1216_, lean_object* v_type_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1216_, v_type_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1224_, lean_object* v_value_1225_, uint8_t v_safety_1226_, uint8_t v_checkMeta_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___f_1233_; lean_object* v___x_1234_; 
v___f_1233_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1233_, 0, v_expectedType_1224_);
v___x_1234_ = l_Lean_Meta_evalExprCore___redArg(v_value_1225_, v___f_1233_, v_safety_1226_, v_checkMeta_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1235_, lean_object* v_value_1236_, lean_object* v_safety_1237_, lean_object* v_checkMeta_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_safety_boxed_1244_; uint8_t v_checkMeta_boxed_1245_; lean_object* v_res_1246_; 
v_safety_boxed_1244_ = lean_unbox(v_safety_1237_);
v_checkMeta_boxed_1245_ = lean_unbox(v_checkMeta_1238_);
v_res_1246_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1235_, v_value_1236_, v_safety_boxed_1244_, v_checkMeta_boxed_1245_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1247_, lean_object* v_expectedType_1248_, lean_object* v_value_1249_, uint8_t v_safety_1250_, uint8_t v_checkMeta_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1248_, v_value_1249_, v_safety_1250_, v_checkMeta_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_expectedType_1259_, lean_object* v_value_1260_, lean_object* v_safety_1261_, lean_object* v_checkMeta_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
uint8_t v_safety_boxed_1268_; uint8_t v_checkMeta_boxed_1269_; lean_object* v_res_1270_; 
v_safety_boxed_1268_ = lean_unbox(v_safety_1261_);
v_checkMeta_boxed_1269_ = lean_unbox(v_checkMeta_1262_);
v_res_1270_ = l_Lean_Meta_evalExpr(v_00_u03b1_1258_, v_expectedType_1259_, v_value_1260_, v_safety_boxed_1268_, v_checkMeta_boxed_1269_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
return v_res_1270_;
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

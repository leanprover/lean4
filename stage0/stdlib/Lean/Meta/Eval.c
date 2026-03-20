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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Environment_importEnv_x3f(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
lean_object* v_name_46_; lean_object* v_defValue_47_; lean_object* v_map_48_; lean_object* v___x_49_; 
v_name_46_ = lean_ctor_get(v_opt_45_, 0);
v_defValue_47_ = lean_ctor_get(v_opt_45_, 1);
v_map_48_ = lean_ctor_get(v_opts_44_, 0);
v___x_49_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_48_, v_name_46_);
if (lean_obj_tag(v___x_49_) == 0)
{
uint8_t v___x_50_; 
v___x_50_ = lean_unbox(v_defValue_47_);
return v___x_50_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_val_51_);
lean_dec_ref(v___x_49_);
if (lean_obj_tag(v_val_51_) == 1)
{
uint8_t v_v_52_; 
v_v_52_ = lean_ctor_get_uint8(v_val_51_, 0);
lean_dec_ref(v_val_51_);
return v_v_52_;
}
else
{
uint8_t v___x_53_; 
lean_dec(v_val_51_);
v___x_53_ = lean_unbox(v_defValue_47_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_opts_54_, lean_object* v_opt_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v_opts_54_, v_opt_55_);
lean_dec_ref(v_opt_55_);
lean_dec_ref(v_opts_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_opts_58_, lean_object* v_opt_59_){
_start:
{
lean_object* v_name_60_; lean_object* v_defValue_61_; lean_object* v_map_62_; lean_object* v___x_63_; 
v_name_60_ = lean_ctor_get(v_opt_59_, 0);
v_defValue_61_ = lean_ctor_get(v_opt_59_, 1);
v_map_62_ = lean_ctor_get(v_opts_58_, 0);
v___x_63_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_62_, v_name_60_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_inc(v_defValue_61_);
return v_defValue_61_;
}
else
{
lean_object* v_val_64_; 
v_val_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref(v___x_63_);
if (lean_obj_tag(v_val_64_) == 3)
{
lean_object* v_v_65_; 
v_v_65_ = lean_ctor_get(v_val_64_, 0);
lean_inc(v_v_65_);
lean_dec_ref(v_val_64_);
return v_v_65_;
}
else
{
lean_dec(v_val_64_);
lean_inc(v_defValue_61_);
return v_defValue_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_opts_66_, lean_object* v_opt_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v_opts_66_, v_opt_67_);
lean_dec_ref(v_opt_67_);
lean_dec_ref(v_opts_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v___x_77_; lean_object* v_mctx_78_; lean_object* v_lctx_79_; lean_object* v_options_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_st_ref_get(v___y_71_);
v_mctx_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_mctx_78_);
lean_dec(v___x_77_);
v_lctx_79_ = lean_ctor_get(v___y_70_, 2);
v_options_80_ = lean_ctor_get(v___y_72_, 2);
lean_inc_ref(v_options_80_);
lean_inc_ref(v_lctx_79_);
v___x_81_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_81_, 0, v_env_76_);
lean_ctor_set(v___x_81_, 1, v_mctx_78_);
lean_ctor_set(v___x_81_, 2, v_lctx_79_);
lean_ctor_set(v___x_81_, 3, v_options_80_);
v___x_82_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_msgData_69_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8___boxed(lean_object* v_msgData_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msgData_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(lean_object* v_msg_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_ref_97_; lean_object* v___x_98_; lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_ref_97_ = lean_ctor_get(v___y_94_, 5);
v___x_98_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msg_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
lean_inc(v_ref_97_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_97_);
lean_ctor_set(v___x_103_, 1, v_a_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 1);
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(lean_object* v_x_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_a_121_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v_x_115_);
v___x_122_ = l_Lean_stringToMessageData(v_a_121_);
v___x_123_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_122_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
return v___x_123_;
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_124_ = lean_ctor_get(v_x_115_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v_x_115_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v_x_115_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 0);
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg___boxed(lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
v___x_140_ = l_Lean_Elab_abortCommandExceptionId;
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg(){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___boxed(lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object* v_constName_147_, uint8_t v_checkMeta_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; lean_object* v_env_155_; uint8_t v___x_156_; 
v___x_154_ = lean_st_ref_get(v___y_152_);
v_env_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc_ref(v_env_155_);
lean_dec(v___x_154_);
lean_inc(v_constName_147_);
v___x_156_ = lean_has_compile_error(v_env_155_, v_constName_147_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v_env_158_; lean_object* v_options_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = lean_st_ref_get(v___y_152_);
v_env_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref(v_env_158_);
lean_dec(v___x_157_);
v_options_159_ = lean_ctor_get(v___y_151_, 2);
v___x_160_ = l_Lean_Environment_evalConst___redArg(v_env_158_, v_options_159_, v_constName_147_, v_checkMeta_148_);
v___x_161_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_160_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v___x_163_; lean_object* v_env_164_; lean_object* v_options_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec_ref(v___x_162_);
v___x_163_ = lean_st_ref_get(v___y_152_);
v_env_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_163_);
v_options_165_ = lean_ctor_get(v___y_151_, 2);
v___x_166_ = l_Lean_Environment_evalConst___redArg(v_env_164_, v_options_165_, v_constName_147_, v_checkMeta_148_);
v___x_167_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_166_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_167_;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec(v_constName_147_);
v_a_168_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_162_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_162_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* v_constName_176_, lean_object* v_checkMeta_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
uint8_t v_checkMeta_boxed_183_; lean_object* v_res_184_; 
v_checkMeta_boxed_183_ = lean_unbox(v_checkMeta_177_);
v_res_184_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_176_, v_checkMeta_boxed_183_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_184_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v___x_185_, lean_object* v_as_186_, size_t v_i_187_, size_t v_stop_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = lean_usize_dec_eq(v_i_187_, v_stop_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_190_ = 1;
v___x_191_ = lean_array_uget_borrowed(v_as_186_, v_i_187_);
v___x_192_ = l_Lean_Environment_isImportedConst(v___x_185_, v___x_191_);
if (v___x_192_ == 0)
{
return v___x_190_;
}
else
{
if (v___x_189_ == 0)
{
size_t v___x_193_; size_t v___x_194_; 
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_187_, v___x_193_);
v_i_187_ = v___x_194_;
goto _start;
}
else
{
return v___x_190_;
}
}
}
else
{
uint8_t v___x_196_; 
v___x_196_ = 0;
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v___x_197_, lean_object* v_as_198_, lean_object* v_i_199_, lean_object* v_stop_200_){
_start:
{
size_t v_i_boxed_201_; size_t v_stop_boxed_202_; uint8_t v_res_203_; lean_object* v_r_204_; 
v_i_boxed_201_ = lean_unbox_usize(v_i_199_);
lean_dec(v_i_199_);
v_stop_boxed_202_ = lean_unbox_usize(v_stop_200_);
lean_dec(v_stop_200_);
v_res_203_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v___x_197_, v_as_198_, v_i_boxed_201_, v_stop_boxed_202_);
lean_dec_ref(v_as_198_);
lean_dec_ref(v___x_197_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_o_208_, lean_object* v_k_209_, uint8_t v_v_210_){
_start:
{
lean_object* v_map_211_; uint8_t v_hasTrace_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_226_; 
v_map_211_ = lean_ctor_get(v_o_208_, 0);
v_hasTrace_212_ = lean_ctor_get_uint8(v_o_208_, sizeof(void*)*1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_o_208_);
if (v_isSharedCheck_226_ == 0)
{
v___x_214_ = v_o_208_;
v_isShared_215_ = v_isSharedCheck_226_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_map_211_);
lean_dec(v_o_208_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_226_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_216_, 0, v_v_210_);
lean_inc(v_k_209_);
v___x_217_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_209_, v___x_216_, v_map_211_);
if (v_hasTrace_212_ == 0)
{
lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_221_; 
v___x_218_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1));
v___x_219_ = l_Lean_Name_isPrefixOf(v___x_218_, v_k_209_);
lean_dec(v_k_209_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_217_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_217_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*1, v___x_219_);
return v___x_221_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v_k_209_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_217_);
v___x_224_ = v___x_214_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_225_, sizeof(void*)*1, v_hasTrace_212_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object* v_o_227_, lean_object* v_k_228_, lean_object* v_v_229_){
_start:
{
uint8_t v_v_boxed_230_; lean_object* v_res_231_; 
v_v_boxed_230_ = lean_unbox(v_v_229_);
v_res_231_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_o_227_, v_k_228_, v_v_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_opts_232_, lean_object* v_opt_233_, uint8_t v_val_234_){
_start:
{
lean_object* v_name_235_; lean_object* v___x_236_; 
v_name_235_ = lean_ctor_get(v_opt_233_, 0);
lean_inc(v_name_235_);
lean_dec_ref(v_opt_233_);
v___x_236_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_opts_232_, v_name_235_, v_val_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* v_opts_237_, lean_object* v_opt_238_, lean_object* v_val_239_){
_start:
{
uint8_t v_val_boxed_240_; lean_object* v_res_241_; 
v_val_boxed_240_ = lean_unbox(v_val_239_);
v_res_241_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_opts_237_, v_opt_238_, v_val_boxed_240_);
return v_res_241_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
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
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_266_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_ctor_set(v___x_266_, 2, v___x_265_);
lean_ctor_set(v___x_266_, 3, v___x_265_);
lean_ctor_set(v___x_266_, 4, v___x_265_);
lean_ctor_set(v___x_266_, 5, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_267_, lean_object* v_checkType_268_, uint8_t v_safety_269_, lean_object* v_value_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; uint8_t v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; lean_object* v_fileName_285_; lean_object* v_fileMap_286_; lean_object* v_currRecDepth_287_; lean_object* v_ref_288_; lean_object* v_currNamespace_289_; lean_object* v_openDecls_290_; lean_object* v_initHeartbeats_291_; lean_object* v_maxHeartbeats_292_; lean_object* v_quotContext_293_; lean_object* v_currMacroScope_294_; lean_object* v_cancelTk_x3f_295_; uint8_t v_suppressElabErrors_296_; lean_object* v_inheritedTraceOptions_297_; lean_object* v___y_298_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; uint8_t v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; uint8_t v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; uint8_t v___y_346_; lean_object* v___y_368_; uint8_t v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; uint8_t v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_410_; uint8_t v___y_411_; lean_object* v___y_412_; uint8_t v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; uint8_t v___y_419_; lean_object* v___y_420_; uint8_t v___y_421_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v_nextMacroScope_543_; lean_object* v_ngen_544_; lean_object* v_auxDeclNGen_545_; lean_object* v_traceState_546_; lean_object* v_messages_547_; lean_object* v_infoState_548_; lean_object* v_snapshotTasks_549_; lean_object* v___y_550_; lean_object* v___x_569_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_569_ = lean_st_ref_get(v___y_274_);
lean_inc_ref(v_value_270_);
v___x_582_ = l_Lean_Expr_getUsedConstants(v_value_270_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_array_get_size(v___x_582_);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec_ref(v___x_582_);
lean_dec(v___x_569_);
goto v___jp_570_;
}
else
{
if (v___x_585_ == 0)
{
lean_dec_ref(v___x_582_);
lean_dec(v___x_569_);
goto v___jp_570_;
}
else
{
lean_object* v_env_586_; size_t v___x_587_; size_t v___x_588_; uint8_t v___x_589_; 
v_env_586_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_env_586_);
lean_dec(v___x_569_);
v___x_587_ = ((size_t)0ULL);
v___x_588_ = lean_usize_of_nat(v___x_584_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_586_, v___x_582_, v___x_587_, v___x_588_);
lean_dec_ref(v___x_582_);
lean_dec_ref(v_env_586_);
if (v___x_589_ == 0)
{
goto v___jp_570_;
}
else
{
v___y_500_ = v___y_271_;
v___y_501_ = v___y_272_;
v___y_502_ = v___y_273_;
v___y_503_ = v___y_274_;
goto v___jp_499_;
}
}
}
v___jp_276_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_284_, v___y_279_);
lean_dec_ref(v___y_279_);
v___x_300_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_300_, 0, v_fileName_285_);
lean_ctor_set(v___x_300_, 1, v_fileMap_286_);
lean_ctor_set(v___x_300_, 2, v___y_284_);
lean_ctor_set(v___x_300_, 3, v_currRecDepth_287_);
lean_ctor_set(v___x_300_, 4, v___x_299_);
lean_ctor_set(v___x_300_, 5, v_ref_288_);
lean_ctor_set(v___x_300_, 6, v_currNamespace_289_);
lean_ctor_set(v___x_300_, 7, v_openDecls_290_);
lean_ctor_set(v___x_300_, 8, v_initHeartbeats_291_);
lean_ctor_set(v___x_300_, 9, v_maxHeartbeats_292_);
lean_ctor_set(v___x_300_, 10, v_quotContext_293_);
lean_ctor_set(v___x_300_, 11, v_currMacroScope_294_);
lean_ctor_set(v___x_300_, 12, v_cancelTk_x3f_295_);
lean_ctor_set(v___x_300_, 13, v_inheritedTraceOptions_297_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*14, v___y_283_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*14 + 1, v_suppressElabErrors_296_);
lean_inc(v___y_298_);
lean_inc_ref(v___x_300_);
v___x_301_ = l_Lean_addAndCompile(v___y_278_, v___y_282_, v___x_300_, v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_301_);
v___x_302_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_277_, v_checkMeta_267_, v___y_281_, v___y_280_, v___x_300_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___x_300_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_281_);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v___x_300_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec(v___y_277_);
v_a_303_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
v___jp_311_:
{
lean_object* v_fileName_322_; lean_object* v_fileMap_323_; lean_object* v_currRecDepth_324_; lean_object* v_ref_325_; lean_object* v_currNamespace_326_; lean_object* v_openDecls_327_; lean_object* v_initHeartbeats_328_; lean_object* v_maxHeartbeats_329_; lean_object* v_quotContext_330_; lean_object* v_currMacroScope_331_; lean_object* v_cancelTk_x3f_332_; uint8_t v_suppressElabErrors_333_; lean_object* v_inheritedTraceOptions_334_; 
v_fileName_322_ = lean_ctor_get(v___y_320_, 0);
lean_inc_ref(v_fileName_322_);
v_fileMap_323_ = lean_ctor_get(v___y_320_, 1);
lean_inc_ref(v_fileMap_323_);
v_currRecDepth_324_ = lean_ctor_get(v___y_320_, 3);
lean_inc(v_currRecDepth_324_);
v_ref_325_ = lean_ctor_get(v___y_320_, 5);
lean_inc(v_ref_325_);
v_currNamespace_326_ = lean_ctor_get(v___y_320_, 6);
lean_inc(v_currNamespace_326_);
v_openDecls_327_ = lean_ctor_get(v___y_320_, 7);
lean_inc(v_openDecls_327_);
v_initHeartbeats_328_ = lean_ctor_get(v___y_320_, 8);
lean_inc(v_initHeartbeats_328_);
v_maxHeartbeats_329_ = lean_ctor_get(v___y_320_, 9);
lean_inc(v_maxHeartbeats_329_);
v_quotContext_330_ = lean_ctor_get(v___y_320_, 10);
lean_inc(v_quotContext_330_);
v_currMacroScope_331_ = lean_ctor_get(v___y_320_, 11);
lean_inc(v_currMacroScope_331_);
v_cancelTk_x3f_332_ = lean_ctor_get(v___y_320_, 12);
lean_inc(v_cancelTk_x3f_332_);
v_suppressElabErrors_333_ = lean_ctor_get_uint8(v___y_320_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_334_ = lean_ctor_get(v___y_320_, 13);
lean_inc_ref(v_inheritedTraceOptions_334_);
lean_dec_ref(v___y_320_);
v___y_277_ = v___y_312_;
v___y_278_ = v___y_313_;
v___y_279_ = v___y_314_;
v___y_280_ = v___y_315_;
v___y_281_ = v___y_316_;
v___y_282_ = v___y_317_;
v___y_283_ = v___y_318_;
v___y_284_ = v___y_319_;
v_fileName_285_ = v_fileName_322_;
v_fileMap_286_ = v_fileMap_323_;
v_currRecDepth_287_ = v_currRecDepth_324_;
v_ref_288_ = v_ref_325_;
v_currNamespace_289_ = v_currNamespace_326_;
v_openDecls_290_ = v_openDecls_327_;
v_initHeartbeats_291_ = v_initHeartbeats_328_;
v_maxHeartbeats_292_ = v_maxHeartbeats_329_;
v_quotContext_293_ = v_quotContext_330_;
v_currMacroScope_294_ = v_currMacroScope_331_;
v_cancelTk_x3f_295_ = v_cancelTk_x3f_332_;
v_suppressElabErrors_296_ = v_suppressElabErrors_333_;
v_inheritedTraceOptions_297_ = v_inheritedTraceOptions_334_;
v___y_298_ = v___y_321_;
goto v___jp_276_;
}
v___jp_335_:
{
if (v___y_346_ == 0)
{
lean_object* v___x_347_; lean_object* v_env_348_; lean_object* v_nextMacroScope_349_; lean_object* v_ngen_350_; lean_object* v_auxDeclNGen_351_; lean_object* v_traceState_352_; lean_object* v_messages_353_; lean_object* v_infoState_354_; lean_object* v_snapshotTasks_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_365_; 
v___x_347_ = lean_st_ref_take(v___y_344_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
v_nextMacroScope_349_ = lean_ctor_get(v___x_347_, 1);
v_ngen_350_ = lean_ctor_get(v___x_347_, 2);
v_auxDeclNGen_351_ = lean_ctor_get(v___x_347_, 3);
v_traceState_352_ = lean_ctor_get(v___x_347_, 4);
v_messages_353_ = lean_ctor_get(v___x_347_, 6);
v_infoState_354_ = lean_ctor_get(v___x_347_, 7);
v_snapshotTasks_355_ = lean_ctor_get(v___x_347_, 8);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_347_, 5);
lean_dec(v_unused_366_);
v___x_357_ = v___x_347_;
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snapshotTasks_355_);
lean_inc(v_infoState_354_);
lean_inc(v_messages_353_);
lean_inc(v_traceState_352_);
lean_inc(v_auxDeclNGen_351_);
lean_inc(v_ngen_350_);
lean_inc(v_nextMacroScope_349_);
lean_inc(v_env_348_);
lean_dec(v___x_347_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = l_Lean_Kernel_enableDiag(v_env_348_, v___y_343_);
v___x_360_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 5, v___x_360_);
lean_ctor_set(v___x_357_, 0, v___x_359_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_ngen_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_auxDeclNGen_351_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_traceState_352_);
lean_ctor_set(v_reuseFailAlloc_364_, 5, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 6, v_messages_353_);
lean_ctor_set(v_reuseFailAlloc_364_, 7, v_infoState_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 8, v_snapshotTasks_355_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_st_ref_set(v___y_344_, v___x_362_);
v___y_312_ = v___y_337_;
v___y_313_ = v___y_338_;
v___y_314_ = v___y_339_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_342_;
v___y_318_ = v___y_343_;
v___y_319_ = v___y_345_;
v___y_320_ = v___y_336_;
v___y_321_ = v___y_344_;
goto v___jp_311_;
}
}
}
else
{
v___y_312_ = v___y_337_;
v___y_313_ = v___y_338_;
v___y_314_ = v___y_339_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_342_;
v___y_318_ = v___y_343_;
v___y_319_ = v___y_345_;
v___y_320_ = v___y_336_;
v___y_321_ = v___y_344_;
goto v___jp_311_;
}
}
v___jp_367_:
{
lean_object* v___x_379_; lean_object* v_fileName_380_; lean_object* v_fileMap_381_; lean_object* v_currRecDepth_382_; lean_object* v_ref_383_; lean_object* v_currNamespace_384_; lean_object* v_openDecls_385_; lean_object* v_initHeartbeats_386_; lean_object* v_maxHeartbeats_387_; lean_object* v_quotContext_388_; lean_object* v_currMacroScope_389_; lean_object* v_cancelTk_x3f_390_; uint8_t v_suppressElabErrors_391_; lean_object* v_inheritedTraceOptions_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_406_; 
v___x_379_ = lean_st_ref_get(v___y_378_);
v_fileName_380_ = lean_ctor_get(v___y_377_, 0);
v_fileMap_381_ = lean_ctor_get(v___y_377_, 1);
v_currRecDepth_382_ = lean_ctor_get(v___y_377_, 3);
v_ref_383_ = lean_ctor_get(v___y_377_, 5);
v_currNamespace_384_ = lean_ctor_get(v___y_377_, 6);
v_openDecls_385_ = lean_ctor_get(v___y_377_, 7);
v_initHeartbeats_386_ = lean_ctor_get(v___y_377_, 8);
v_maxHeartbeats_387_ = lean_ctor_get(v___y_377_, 9);
v_quotContext_388_ = lean_ctor_get(v___y_377_, 10);
v_currMacroScope_389_ = lean_ctor_get(v___y_377_, 11);
v_cancelTk_x3f_390_ = lean_ctor_get(v___y_377_, 12);
v_suppressElabErrors_391_ = lean_ctor_get_uint8(v___y_377_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_392_ = lean_ctor_get(v___y_377_, 13);
v_isSharedCheck_406_ = !lean_is_exclusive(v___y_377_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_407_ = lean_ctor_get(v___y_377_, 4);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v___y_377_, 2);
lean_dec(v_unused_408_);
v___x_394_ = v___y_377_;
v_isShared_395_ = v_isSharedCheck_406_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_inheritedTraceOptions_392_);
lean_inc(v_cancelTk_x3f_390_);
lean_inc(v_currMacroScope_389_);
lean_inc(v_quotContext_388_);
lean_inc(v_maxHeartbeats_387_);
lean_inc(v_initHeartbeats_386_);
lean_inc(v_openDecls_385_);
lean_inc(v_currNamespace_384_);
lean_inc(v_ref_383_);
lean_inc(v_currRecDepth_382_);
lean_inc(v_fileMap_381_);
lean_inc(v_fileName_380_);
lean_dec(v___y_377_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_406_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_env_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v_env_396_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_379_);
v___x_397_ = l_Lean_maxRecDepth;
v___x_398_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_373_, v___x_397_);
lean_inc_ref(v_inheritedTraceOptions_392_);
lean_inc(v_cancelTk_x3f_390_);
lean_inc(v_currMacroScope_389_);
lean_inc(v_quotContext_388_);
lean_inc(v_maxHeartbeats_387_);
lean_inc(v_initHeartbeats_386_);
lean_inc(v_openDecls_385_);
lean_inc(v_currNamespace_384_);
lean_inc(v_ref_383_);
lean_inc(v_currRecDepth_382_);
lean_inc_ref(v___y_373_);
lean_inc_ref(v_fileMap_381_);
lean_inc_ref(v_fileName_380_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 4, v___x_398_);
lean_ctor_set(v___x_394_, 2, v___y_373_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_fileName_380_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_fileMap_381_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v___y_373_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_currRecDepth_382_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v_ref_383_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_currNamespace_384_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_openDecls_385_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v_initHeartbeats_386_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_maxHeartbeats_387_);
lean_ctor_set(v_reuseFailAlloc_405_, 10, v_quotContext_388_);
lean_ctor_set(v_reuseFailAlloc_405_, 11, v_currMacroScope_389_);
lean_ctor_set(v_reuseFailAlloc_405_, 12, v_cancelTk_x3f_390_);
lean_ctor_set(v_reuseFailAlloc_405_, 13, v_inheritedTraceOptions_392_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*14 + 1, v_suppressElabErrors_391_);
v___x_400_ = v_reuseFailAlloc_405_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; uint8_t v___x_404_; 
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*14, v___y_369_);
v___x_401_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_402_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_373_, v___x_401_, v___y_372_);
v___x_403_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_402_, v___y_375_);
lean_dec_ref(v___y_375_);
v___x_404_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_396_);
lean_dec_ref(v_env_396_);
if (v___x_404_ == 0)
{
if (v___x_403_ == 0)
{
lean_dec_ref(v___x_400_);
v___y_277_ = v___y_368_;
v___y_278_ = v___y_370_;
v___y_279_ = v___x_397_;
v___y_280_ = v___y_371_;
v___y_281_ = v___y_374_;
v___y_282_ = v___y_376_;
v___y_283_ = v___x_403_;
v___y_284_ = v___x_402_;
v_fileName_285_ = v_fileName_380_;
v_fileMap_286_ = v_fileMap_381_;
v_currRecDepth_287_ = v_currRecDepth_382_;
v_ref_288_ = v_ref_383_;
v_currNamespace_289_ = v_currNamespace_384_;
v_openDecls_290_ = v_openDecls_385_;
v_initHeartbeats_291_ = v_initHeartbeats_386_;
v_maxHeartbeats_292_ = v_maxHeartbeats_387_;
v_quotContext_293_ = v_quotContext_388_;
v_currMacroScope_294_ = v_currMacroScope_389_;
v_cancelTk_x3f_295_ = v_cancelTk_x3f_390_;
v_suppressElabErrors_296_ = v_suppressElabErrors_391_;
v_inheritedTraceOptions_297_ = v_inheritedTraceOptions_392_;
v___y_298_ = v___y_378_;
goto v___jp_276_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_392_);
lean_dec(v_cancelTk_x3f_390_);
lean_dec(v_currMacroScope_389_);
lean_dec(v_quotContext_388_);
lean_dec(v_maxHeartbeats_387_);
lean_dec(v_initHeartbeats_386_);
lean_dec(v_openDecls_385_);
lean_dec(v_currNamespace_384_);
lean_dec(v_ref_383_);
lean_dec(v_currRecDepth_382_);
lean_dec_ref(v_fileMap_381_);
lean_dec_ref(v_fileName_380_);
v___y_336_ = v___x_400_;
v___y_337_ = v___y_368_;
v___y_338_ = v___y_370_;
v___y_339_ = v___x_397_;
v___y_340_ = v___y_371_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_376_;
v___y_343_ = v___x_403_;
v___y_344_ = v___y_378_;
v___y_345_ = v___x_402_;
v___y_346_ = v___x_404_;
goto v___jp_335_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_392_);
lean_dec(v_cancelTk_x3f_390_);
lean_dec(v_currMacroScope_389_);
lean_dec(v_quotContext_388_);
lean_dec(v_maxHeartbeats_387_);
lean_dec(v_initHeartbeats_386_);
lean_dec(v_openDecls_385_);
lean_dec(v_currNamespace_384_);
lean_dec(v_ref_383_);
lean_dec(v_currRecDepth_382_);
lean_dec_ref(v_fileMap_381_);
lean_dec_ref(v_fileName_380_);
v___y_336_ = v___x_400_;
v___y_337_ = v___y_368_;
v___y_338_ = v___y_370_;
v___y_339_ = v___x_397_;
v___y_340_ = v___y_371_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_376_;
v___y_343_ = v___x_403_;
v___y_344_ = v___y_378_;
v___y_345_ = v___x_402_;
v___y_346_ = v___x_403_;
goto v___jp_335_;
}
}
}
}
v___jp_409_:
{
if (v___y_421_ == 0)
{
lean_object* v___x_422_; lean_object* v_env_423_; lean_object* v_nextMacroScope_424_; lean_object* v_ngen_425_; lean_object* v_auxDeclNGen_426_; lean_object* v_traceState_427_; lean_object* v_messages_428_; lean_object* v_infoState_429_; lean_object* v_snapshotTasks_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_440_; 
v___x_422_ = lean_st_ref_take(v___y_415_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
v_nextMacroScope_424_ = lean_ctor_get(v___x_422_, 1);
v_ngen_425_ = lean_ctor_get(v___x_422_, 2);
v_auxDeclNGen_426_ = lean_ctor_get(v___x_422_, 3);
v_traceState_427_ = lean_ctor_get(v___x_422_, 4);
v_messages_428_ = lean_ctor_get(v___x_422_, 6);
v_infoState_429_ = lean_ctor_get(v___x_422_, 7);
v_snapshotTasks_430_ = lean_ctor_get(v___x_422_, 8);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_422_, 5);
lean_dec(v_unused_441_);
v___x_432_ = v___x_422_;
v_isShared_433_ = v_isSharedCheck_440_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snapshotTasks_430_);
lean_inc(v_infoState_429_);
lean_inc(v_messages_428_);
lean_inc(v_traceState_427_);
lean_inc(v_auxDeclNGen_426_);
lean_inc(v_ngen_425_);
lean_inc(v_nextMacroScope_424_);
lean_inc(v_env_423_);
lean_dec(v___x_422_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_440_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = l_Lean_Kernel_enableDiag(v_env_423_, v___y_411_);
v___x_435_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 5, v___x_435_);
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_nextMacroScope_424_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_ngen_425_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_auxDeclNGen_426_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_traceState_427_);
lean_ctor_set(v_reuseFailAlloc_439_, 5, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_439_, 6, v_messages_428_);
lean_ctor_set(v_reuseFailAlloc_439_, 7, v_infoState_429_);
lean_ctor_set(v_reuseFailAlloc_439_, 8, v_snapshotTasks_430_);
v___x_437_ = v_reuseFailAlloc_439_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; 
v___x_438_ = lean_st_ref_set(v___y_415_, v___x_437_);
v___y_368_ = v___y_410_;
v___y_369_ = v___y_411_;
v___y_370_ = v___y_412_;
v___y_371_ = v___y_414_;
v___y_372_ = v___y_413_;
v___y_373_ = v___y_416_;
v___y_374_ = v___y_418_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_419_;
v___y_377_ = v___y_420_;
v___y_378_ = v___y_415_;
goto v___jp_367_;
}
}
}
else
{
v___y_368_ = v___y_410_;
v___y_369_ = v___y_411_;
v___y_370_ = v___y_412_;
v___y_371_ = v___y_414_;
v___y_372_ = v___y_413_;
v___y_373_ = v___y_416_;
v___y_374_ = v___y_418_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_419_;
v___y_377_ = v___y_420_;
v___y_378_ = v___y_415_;
goto v___jp_367_;
}
}
v___jp_442_:
{
lean_object* v___x_451_; 
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
lean_inc_ref(v___y_445_);
v___x_451_ = lean_infer_type(v___y_445_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___x_451_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
lean_inc(v_a_452_);
v___x_453_ = lean_apply_6(v_checkType_268_, v_a_452_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, lean_box(0));
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v___x_454_; lean_object* v_env_455_; lean_object* v_checked_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v___x_453_);
v___x_454_ = lean_st_ref_get(v___y_450_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_env_455_);
lean_dec(v___x_454_);
v_checked_456_ = lean_ctor_get(v_env_455_, 2);
lean_inc_ref(v_checked_456_);
lean_dec_ref(v_env_455_);
v___x_457_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3));
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
v___x_458_ = l_Lean_traceBlock___redArg(v___x_457_, v_checked_456_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v___x_459_; lean_object* v_options_460_; lean_object* v_env_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; uint8_t v___x_474_; 
lean_dec_ref(v___x_458_);
v___x_459_ = lean_st_ref_get(v___y_450_);
v_options_460_ = lean_ctor_get(v___y_449_, 2);
v_env_461_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_env_461_);
lean_dec(v___x_459_);
v___x_462_ = lean_array_to_list(v___y_444_);
lean_inc(v___y_443_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v___y_443_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_ctor_set(v___x_463_, 2, v_a_452_);
v___x_464_ = lean_box(0);
lean_inc(v___y_443_);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v___y_443_);
lean_ctor_set(v___x_465_, 1, v___y_446_);
v___x_466_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_466_, 0, v___x_463_);
lean_ctor_set(v___x_466_, 1, v___y_445_);
lean_ctor_set(v___x_466_, 2, v___x_464_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*4, v_safety_269_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
v___x_468_ = 1;
v___x_469_ = l_Lean_Elab_async;
v___x_470_ = 0;
lean_inc_ref(v_options_460_);
v___x_471_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_460_, v___x_469_, v___x_470_);
v___x_472_ = l_Lean_diagnostics;
v___x_473_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_471_, v___x_472_);
v___x_474_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_461_);
lean_dec_ref(v_env_461_);
if (v___x_474_ == 0)
{
if (v___x_473_ == 0)
{
v___y_368_ = v___y_443_;
v___y_369_ = v___x_473_;
v___y_370_ = v___x_467_;
v___y_371_ = v___y_448_;
v___y_372_ = v___x_470_;
v___y_373_ = v___x_471_;
v___y_374_ = v___y_447_;
v___y_375_ = v___x_472_;
v___y_376_ = v___x_468_;
v___y_377_ = v___y_449_;
v___y_378_ = v___y_450_;
goto v___jp_367_;
}
else
{
v___y_410_ = v___y_443_;
v___y_411_ = v___x_473_;
v___y_412_ = v___x_467_;
v___y_413_ = v___x_470_;
v___y_414_ = v___y_448_;
v___y_415_ = v___y_450_;
v___y_416_ = v___x_471_;
v___y_417_ = v___x_472_;
v___y_418_ = v___y_447_;
v___y_419_ = v___x_468_;
v___y_420_ = v___y_449_;
v___y_421_ = v___x_474_;
goto v___jp_409_;
}
}
else
{
v___y_410_ = v___y_443_;
v___y_411_ = v___x_473_;
v___y_412_ = v___x_467_;
v___y_413_ = v___x_470_;
v___y_414_ = v___y_448_;
v___y_415_ = v___y_450_;
v___y_416_ = v___x_471_;
v___y_417_ = v___x_472_;
v___y_418_ = v___y_447_;
v___y_419_ = v___x_468_;
v___y_420_ = v___y_449_;
v___y_421_ = v___x_473_;
goto v___jp_409_;
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_a_452_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
v_a_475_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_458_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_458_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_a_452_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
v_a_483_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_453_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_453_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v_checkType_268_);
v_a_491_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_451_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_451_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
v___jp_499_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5));
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
v___x_505_ = l_Lean_Core_mkFreshUserName(v___x_504_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v___x_507_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_270_, v___y_501_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_params_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
v___x_509_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9);
lean_inc(v_a_508_);
v___x_510_ = l_Lean_collectLevelParams(v___x_509_, v_a_508_);
v_params_511_ = lean_ctor_get(v___x_510_, 2);
lean_inc_ref(v_params_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_box(0);
v___x_513_ = l_Lean_Expr_hasMVar(v_a_508_);
if (v___x_513_ == 0)
{
v___y_443_ = v_a_506_;
v___y_444_ = v_params_511_;
v___y_445_ = v_a_508_;
v___y_446_ = v___x_512_;
v___y_447_ = v___y_500_;
v___y_448_ = v___y_501_;
v___y_449_ = v___y_502_;
v___y_450_ = v___y_503_;
goto v___jp_442_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11);
lean_inc(v_a_508_);
v___x_515_ = l_Lean_indentExpr(v_a_508_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_516_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_dec_ref(v___x_517_);
v___y_443_ = v_a_506_;
v___y_444_ = v_params_511_;
v___y_445_ = v_a_508_;
v___y_446_ = v___x_512_;
v___y_447_ = v___y_500_;
v___y_448_ = v___y_501_;
v___y_449_ = v___y_502_;
v___y_450_ = v___y_503_;
goto v___jp_442_;
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_params_511_);
lean_dec(v_a_508_);
lean_dec(v_a_506_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_checkType_268_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_506_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_checkType_268_);
v_a_526_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_507_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_507_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_value_270_);
lean_dec_ref(v_checkType_268_);
v_a_534_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_505_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_505_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
v___jp_542_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_mctx_555_; lean_object* v_zetaDeltaFVarIds_556_; lean_object* v_postponed_557_; lean_object* v_diag_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_567_; 
v___x_551_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_552_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_552_, 0, v___y_550_);
lean_ctor_set(v___x_552_, 1, v_nextMacroScope_543_);
lean_ctor_set(v___x_552_, 2, v_ngen_544_);
lean_ctor_set(v___x_552_, 3, v_auxDeclNGen_545_);
lean_ctor_set(v___x_552_, 4, v_traceState_546_);
lean_ctor_set(v___x_552_, 5, v___x_551_);
lean_ctor_set(v___x_552_, 6, v_messages_547_);
lean_ctor_set(v___x_552_, 7, v_infoState_548_);
lean_ctor_set(v___x_552_, 8, v_snapshotTasks_549_);
v___x_553_ = lean_st_ref_set(v___y_274_, v___x_552_);
v___x_554_ = lean_st_ref_take(v___y_272_);
v_mctx_555_ = lean_ctor_get(v___x_554_, 0);
v_zetaDeltaFVarIds_556_ = lean_ctor_get(v___x_554_, 2);
v_postponed_557_ = lean_ctor_get(v___x_554_, 3);
v_diag_558_ = lean_ctor_get(v___x_554_, 4);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v___x_554_, 1);
lean_dec(v_unused_568_);
v___x_560_ = v___x_554_;
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_diag_558_);
lean_inc(v_postponed_557_);
lean_inc(v_zetaDeltaFVarIds_556_);
lean_inc(v_mctx_555_);
lean_dec(v___x_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_mctx_555_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_zetaDeltaFVarIds_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_postponed_557_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v_diag_558_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_st_ref_set(v___y_272_, v___x_564_);
v___y_500_ = v___y_271_;
v___y_501_ = v___y_272_;
v___y_502_ = v___y_273_;
v___y_503_ = v___y_274_;
goto v___jp_499_;
}
}
}
v___jp_570_:
{
lean_object* v___x_571_; lean_object* v_env_572_; lean_object* v_nextMacroScope_573_; lean_object* v_ngen_574_; lean_object* v_auxDeclNGen_575_; lean_object* v_traceState_576_; lean_object* v_messages_577_; lean_object* v_infoState_578_; lean_object* v_snapshotTasks_579_; lean_object* v___x_580_; 
v___x_571_ = lean_st_ref_take(v___y_274_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
v_nextMacroScope_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_nextMacroScope_573_);
v_ngen_574_ = lean_ctor_get(v___x_571_, 2);
lean_inc_ref(v_ngen_574_);
v_auxDeclNGen_575_ = lean_ctor_get(v___x_571_, 3);
lean_inc_ref(v_auxDeclNGen_575_);
v_traceState_576_ = lean_ctor_get(v___x_571_, 4);
lean_inc_ref(v_traceState_576_);
v_messages_577_ = lean_ctor_get(v___x_571_, 6);
lean_inc_ref(v_messages_577_);
v_infoState_578_ = lean_ctor_get(v___x_571_, 7);
lean_inc_ref(v_infoState_578_);
v_snapshotTasks_579_ = lean_ctor_get(v___x_571_, 8);
lean_inc_ref(v_snapshotTasks_579_);
lean_dec(v___x_571_);
lean_inc_ref(v_env_572_);
v___x_580_ = l_Lean_Environment_importEnv_x3f(v_env_572_);
if (lean_obj_tag(v___x_580_) == 0)
{
v_nextMacroScope_543_ = v_nextMacroScope_573_;
v_ngen_544_ = v_ngen_574_;
v_auxDeclNGen_545_ = v_auxDeclNGen_575_;
v_traceState_546_ = v_traceState_576_;
v_messages_547_ = v_messages_577_;
v_infoState_548_ = v_infoState_578_;
v_snapshotTasks_549_ = v_snapshotTasks_579_;
v___y_550_ = v_env_572_;
goto v___jp_542_;
}
else
{
lean_object* v_val_581_; 
lean_dec_ref(v_env_572_);
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v___x_580_);
v_nextMacroScope_543_ = v_nextMacroScope_573_;
v_ngen_544_ = v_ngen_574_;
v_auxDeclNGen_545_ = v_auxDeclNGen_575_;
v_traceState_546_ = v_traceState_576_;
v_messages_547_ = v_messages_577_;
v_infoState_548_ = v_infoState_578_;
v_snapshotTasks_549_ = v_snapshotTasks_579_;
v___y_550_ = v_val_581_;
goto v___jp_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_590_, lean_object* v_checkType_591_, lean_object* v_safety_592_, lean_object* v_value_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v_checkMeta_boxed_599_; uint8_t v_safety_boxed_600_; lean_object* v_res_601_; 
v_checkMeta_boxed_599_ = lean_unbox(v_checkMeta_590_);
v_safety_boxed_600_ = lean_unbox(v_safety_592_);
v_res_601_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_599_, v_checkType_591_, v_safety_boxed_600_, v_value_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v_nextMacroScope_607_; lean_object* v_ngen_608_; lean_object* v_auxDeclNGen_609_; lean_object* v_traceState_610_; lean_object* v_messages_611_; lean_object* v_infoState_612_; lean_object* v_snapshotTasks_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_639_; 
v___x_606_ = lean_st_ref_take(v___y_604_);
v_nextMacroScope_607_ = lean_ctor_get(v___x_606_, 1);
v_ngen_608_ = lean_ctor_get(v___x_606_, 2);
v_auxDeclNGen_609_ = lean_ctor_get(v___x_606_, 3);
v_traceState_610_ = lean_ctor_get(v___x_606_, 4);
v_messages_611_ = lean_ctor_get(v___x_606_, 6);
v_infoState_612_ = lean_ctor_get(v___x_606_, 7);
v_snapshotTasks_613_ = lean_ctor_get(v___x_606_, 8);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_640_ = lean_ctor_get(v___x_606_, 5);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v___x_606_, 0);
lean_dec(v_unused_641_);
v___x_615_ = v___x_606_;
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snapshotTasks_613_);
lean_inc(v_infoState_612_);
lean_inc(v_messages_611_);
lean_inc(v_traceState_610_);
lean_inc(v_auxDeclNGen_609_);
lean_inc(v_ngen_608_);
lean_inc(v_nextMacroScope_607_);
lean_dec(v___x_606_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 5, v___x_617_);
lean_ctor_set(v___x_615_, 0, v_env_602_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_env_602_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_nextMacroScope_607_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_ngen_608_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_auxDeclNGen_609_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_traceState_610_);
lean_ctor_set(v_reuseFailAlloc_638_, 5, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_638_, 6, v_messages_611_);
lean_ctor_set(v_reuseFailAlloc_638_, 7, v_infoState_612_);
lean_ctor_set(v_reuseFailAlloc_638_, 8, v_snapshotTasks_613_);
v___x_619_ = v_reuseFailAlloc_638_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_mctx_622_; lean_object* v_zetaDeltaFVarIds_623_; lean_object* v_postponed_624_; lean_object* v_diag_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_636_; 
v___x_620_ = lean_st_ref_set(v___y_604_, v___x_619_);
v___x_621_ = lean_st_ref_take(v___y_603_);
v_mctx_622_ = lean_ctor_get(v___x_621_, 0);
v_zetaDeltaFVarIds_623_ = lean_ctor_get(v___x_621_, 2);
v_postponed_624_ = lean_ctor_get(v___x_621_, 3);
v_diag_625_ = lean_ctor_get(v___x_621_, 4);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v___x_621_, 1);
lean_dec(v_unused_637_);
v___x_627_ = v___x_621_;
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_diag_625_);
lean_inc(v_postponed_624_);
lean_inc(v_zetaDeltaFVarIds_623_);
lean_inc(v_mctx_622_);
lean_dec(v___x_621_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_mctx_622_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_zetaDeltaFVarIds_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_postponed_624_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_diag_625_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_st_ref_set(v___y_603_, v___x_631_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec(v___y_643_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_647_, lean_object* v_x_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v_env_655_; lean_object* v_a_657_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_654_ = lean_st_ref_get(v___y_652_);
v_env_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_env_655_);
lean_dec(v___x_654_);
v___x_667_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_647_, v___y_650_, v___y_652_);
lean_dec_ref(v___x_667_);
lean_inc(v___y_652_);
lean_inc(v___y_650_);
v___x_668_ = lean_apply_5(v_x_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, lean_box(0));
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref(v___x_668_);
v___x_670_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_655_, v___y_650_, v___y_652_);
lean_dec(v___y_652_);
lean_dec(v___y_650_);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_678_);
v___x_672_ = v___x_670_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_dec(v___x_670_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_a_669_);
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_669_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_679_; 
v_a_679_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_679_);
lean_dec_ref(v___x_668_);
v_a_657_ = v_a_679_;
goto v___jp_656_;
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v___x_658_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_655_, v___y_650_, v___y_652_);
lean_dec(v___y_652_);
lean_dec(v___y_650_);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v___x_658_, 0);
lean_dec(v_unused_666_);
v___x_660_ = v___x_658_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_dec(v___x_658_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 1);
lean_ctor_set(v___x_660_, 0, v_a_657_);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_657_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_680_, lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_680_, v_x_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_688_, lean_object* v_checkType_689_, uint8_t v_safety_690_, uint8_t v_checkMeta_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; lean_object* v_env_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_697_ = lean_st_ref_get(v_a_695_);
v_env_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc_ref(v_env_698_);
lean_dec(v___x_697_);
v___x_699_ = lean_box(v_checkMeta_691_);
v___x_700_ = lean_box(v_safety_690_);
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_701_, 0, v___x_699_);
lean_closure_set(v___f_701_, 1, v_checkType_689_);
lean_closure_set(v___f_701_, 2, v___x_700_);
lean_closure_set(v___f_701_, 3, v_value_688_);
v___x_702_ = l_Lean_Environment_unlockAsync(v_env_698_);
v___x_703_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_702_, v___f_701_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_704_, lean_object* v_checkType_705_, lean_object* v_safety_706_, lean_object* v_checkMeta_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
uint8_t v_safety_boxed_713_; uint8_t v_checkMeta_boxed_714_; lean_object* v_res_715_; 
v_safety_boxed_713_ = lean_unbox(v_safety_706_);
v_checkMeta_boxed_714_ = lean_unbox(v_checkMeta_707_);
v_res_715_ = l_Lean_Meta_evalExprCore___redArg(v_value_704_, v_checkType_705_, v_safety_boxed_713_, v_checkMeta_boxed_714_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_716_, lean_object* v_value_717_, lean_object* v_checkType_718_, uint8_t v_safety_719_, uint8_t v_checkMeta_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Meta_evalExprCore___redArg(v_value_717_, v_checkType_718_, v_safety_719_, v_checkMeta_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_727_, lean_object* v_value_728_, lean_object* v_checkType_729_, lean_object* v_safety_730_, lean_object* v_checkMeta_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
uint8_t v_safety_boxed_737_; uint8_t v_checkMeta_boxed_738_; lean_object* v_res_739_; 
v_safety_boxed_737_ = lean_unbox(v_safety_730_);
v_checkMeta_boxed_738_ = lean_unbox(v_checkMeta_731_);
v_res_739_ = l_Lean_Meta_evalExprCore(v_00_u03b1_727_, v_value_728_, v_checkType_729_, v_safety_boxed_737_, v_checkMeta_boxed_738_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_754_, lean_object* v_constName_755_, uint8_t v_checkMeta_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_755_, v_checkMeta_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_763_, lean_object* v_constName_764_, lean_object* v_checkMeta_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_checkMeta_boxed_771_; lean_object* v_res_772_; 
v_checkMeta_boxed_771_ = lean_unbox(v_checkMeta_765_);
v_res_772_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_763_, v_constName_764_, v_checkMeta_boxed_771_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_773_, lean_object* v_msg_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_781_, lean_object* v_msg_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_781_, v_msg_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_789_, v___y_791_, v___y_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_803_, lean_object* v_env_804_, lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_804_, v_x_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_812_, lean_object* v_env_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_812_, v_env_813_, v_x_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_821_, lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_829_, v_x_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_836_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_840_, lean_object* v_type_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
v___x_847_ = l_Lean_Meta_whnfD(v_type_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_861_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_861_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_861_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_861_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_Expr_isConstOf(v_a_848_, v_typeName_840_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_del_object(v___x_850_);
v___x_853_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_854_ = l_Lean_indentExpr(v_a_848_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_855_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v_a_848_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
v___x_857_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_857_);
v___x_859_ = v___x_850_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
v_a_862_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_847_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_847_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_870_, lean_object* v_type_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_870_, v_type_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v_typeName_870_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_878_, lean_object* v_value_879_, uint8_t v_safety_880_, uint8_t v_checkMeta_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; 
v___f_887_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_887_, 0, v_typeName_878_);
v___x_888_ = l_Lean_Meta_evalExprCore___redArg(v_value_879_, v___f_887_, v_safety_880_, v_checkMeta_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_889_, lean_object* v_value_890_, lean_object* v_safety_891_, lean_object* v_checkMeta_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
uint8_t v_safety_boxed_898_; uint8_t v_checkMeta_boxed_899_; lean_object* v_res_900_; 
v_safety_boxed_898_ = lean_unbox(v_safety_891_);
v_checkMeta_boxed_899_ = lean_unbox(v_checkMeta_892_);
v_res_900_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_889_, v_value_890_, v_safety_boxed_898_, v_checkMeta_boxed_899_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_901_, lean_object* v_typeName_902_, lean_object* v_value_903_, uint8_t v_safety_904_, uint8_t v_checkMeta_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_902_, v_value_903_, v_safety_904_, v_checkMeta_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_912_, lean_object* v_typeName_913_, lean_object* v_value_914_, lean_object* v_safety_915_, lean_object* v_checkMeta_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
uint8_t v_safety_boxed_922_; uint8_t v_checkMeta_boxed_923_; lean_object* v_res_924_; 
v_safety_boxed_922_ = lean_unbox(v_safety_915_);
v_checkMeta_boxed_923_ = lean_unbox(v_checkMeta_916_);
v_res_924_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_912_, v_typeName_913_, v_value_914_, v_safety_boxed_922_, v_checkMeta_boxed_923_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
return v_res_924_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_930_, lean_object* v_type_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
lean_inc_ref(v_expectedType_930_);
lean_inc_ref(v_type_931_);
v___x_937_ = l_Lean_Meta_isExprDefEq(v_type_931_, v_expectedType_930_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_962_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_962_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
uint8_t v___x_942_; 
v___x_942_ = lean_unbox(v_a_938_);
lean_dec(v_a_938_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_del_object(v___x_940_);
v___x_943_ = lean_box(0);
v___x_944_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_945_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_931_, v_expectedType_930_, v___x_943_, v___x_944_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
v___x_947_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v_a_946_);
v___x_949_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_948_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
v_a_950_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_945_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_945_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_type_931_);
lean_dec_ref(v_expectedType_930_);
v___x_958_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_958_);
v___x_960_ = v___x_940_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_type_931_);
lean_dec_ref(v_expectedType_930_);
v_a_963_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_937_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_937_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_971_, lean_object* v_type_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_971_, v_type_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_979_, lean_object* v_value_980_, uint8_t v_safety_981_, uint8_t v_checkMeta_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___f_988_; lean_object* v___x_989_; 
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_988_, 0, v_expectedType_979_);
v___x_989_ = l_Lean_Meta_evalExprCore___redArg(v_value_980_, v___f_988_, v_safety_981_, v_checkMeta_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_990_, lean_object* v_value_991_, lean_object* v_safety_992_, lean_object* v_checkMeta_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
uint8_t v_safety_boxed_999_; uint8_t v_checkMeta_boxed_1000_; lean_object* v_res_1001_; 
v_safety_boxed_999_ = lean_unbox(v_safety_992_);
v_checkMeta_boxed_1000_ = lean_unbox(v_checkMeta_993_);
v_res_1001_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_990_, v_value_991_, v_safety_boxed_999_, v_checkMeta_boxed_1000_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1002_, lean_object* v_expectedType_1003_, lean_object* v_value_1004_, uint8_t v_safety_1005_, uint8_t v_checkMeta_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1003_, v_value_1004_, v_safety_1005_, v_checkMeta_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_expectedType_1014_, lean_object* v_value_1015_, lean_object* v_safety_1016_, lean_object* v_checkMeta_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
uint8_t v_safety_boxed_1023_; uint8_t v_checkMeta_boxed_1024_; lean_object* v_res_1025_; 
v_safety_boxed_1023_ = lean_unbox(v_safety_1016_);
v_checkMeta_boxed_1024_ = lean_unbox(v_checkMeta_1017_);
v_res_1025_ = l_Lean_Meta_evalExpr(v_00_u03b1_1013_, v_expectedType_1014_, v_value_1015_, v_safety_boxed_1023_, v_checkMeta_boxed_1024_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v_res_1025_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

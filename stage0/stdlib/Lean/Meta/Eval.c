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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
static const lean_array_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "failed to evaluate expression, it contains metavariables"};
static const lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13;
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
lean_dec_ref_known(v___x_49_, 1);
if (lean_obj_tag(v_val_51_) == 1)
{
uint8_t v_v_52_; 
v_v_52_ = lean_ctor_get_uint8(v_val_51_, 0);
lean_dec_ref_known(v_val_51_, 0);
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
lean_dec_ref_known(v___x_63_, 1);
if (lean_obj_tag(v_val_64_) == 3)
{
lean_object* v_v_65_; 
v_v_65_ = lean_ctor_get(v_val_64_, 0);
lean_inc(v_v_65_);
lean_dec_ref_known(v_val_64_, 1);
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
lean_dec_ref_known(v_x_115_, 1);
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
lean_dec(v_constName_147_);
lean_dec_ref(v_env_158_);
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
lean_dec_ref_known(v___x_162_, 1);
v___x_163_ = lean_st_ref_get(v___y_152_);
v_env_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_163_);
v_options_165_ = lean_ctor_get(v___y_151_, 2);
v___x_166_ = l_Lean_Environment_evalConst___redArg(v_env_164_, v_options_165_, v_constName_147_, v_checkMeta_148_);
lean_dec(v_constName_147_);
lean_dec_ref(v_env_164_);
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
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_248_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
lean_ctor_set(v___x_248_, 3, v___x_247_);
lean_ctor_set(v___x_248_, 4, v___x_247_);
lean_ctor_set(v___x_248_, 5, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v_cellCount_253_; lean_object* v___x_254_; 
v_cellCount_253_ = lean_unsigned_to_nat(16u);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v_cellCount_255_; lean_object* v___x_256_; 
v_cellCount_255_ = lean_unsigned_to_nat(16u);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_258_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
lean_ctor_set(v___x_260_, 2, v___x_257_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10));
v___x_264_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9);
v___x_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
lean_ctor_set(v___x_265_, 2, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12));
v___x_268_ = l_Lean_stringToMessageData(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_269_, lean_object* v_checkType_270_, uint8_t v_safety_271_, lean_object* v_value_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___y_279_; uint8_t v___y_280_; uint8_t v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; uint8_t v___y_286_; lean_object* v___y_287_; lean_object* v_fileName_288_; lean_object* v_fileMap_289_; lean_object* v_currRecDepth_290_; lean_object* v_ref_291_; lean_object* v_currNamespace_292_; lean_object* v_openDecls_293_; lean_object* v_initHeartbeats_294_; lean_object* v_maxHeartbeats_295_; lean_object* v_quotContext_296_; lean_object* v_currMacroScope_297_; lean_object* v_cancelTk_x3f_298_; uint8_t v_suppressElabErrors_299_; lean_object* v_inheritedTraceOptions_300_; lean_object* v___y_301_; lean_object* v___y_315_; uint8_t v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; uint8_t v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; uint8_t v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; uint8_t v___y_350_; lean_object* v___y_351_; uint8_t v___y_352_; lean_object* v___y_373_; uint8_t v___y_374_; uint8_t v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_416_; uint8_t v___y_417_; uint8_t v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; uint8_t v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; uint8_t v___y_429_; lean_object* v___y_450_; uint8_t v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; uint8_t v___y_454_; uint8_t v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_493_; uint8_t v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; uint8_t v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v_nextMacroScope_664_; lean_object* v_ngen_665_; lean_object* v_auxDeclNGen_666_; lean_object* v_traceState_667_; lean_object* v_messages_668_; lean_object* v_infoState_669_; lean_object* v_snapshotTasks_670_; lean_object* v___y_671_; lean_object* v___x_690_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_690_ = lean_st_ref_get(v___y_276_);
lean_inc_ref(v_value_272_);
v___x_703_ = l_Lean_Expr_getUsedConstants(v_value_272_);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_array_get_size(v___x_703_);
v___x_706_ = lean_nat_dec_lt(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_dec_ref(v___x_703_);
lean_dec(v___x_690_);
goto v___jp_691_;
}
else
{
if (v___x_706_ == 0)
{
lean_dec_ref(v___x_703_);
lean_dec(v___x_690_);
goto v___jp_691_;
}
else
{
lean_object* v_env_707_; size_t v___x_708_; size_t v___x_709_; uint8_t v___x_710_; 
v_env_707_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_env_707_);
lean_dec(v___x_690_);
v___x_708_ = ((size_t)0ULL);
v___x_709_ = lean_usize_of_nat(v___x_705_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_707_, v___x_703_, v___x_708_, v___x_709_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v_env_707_);
if (v___x_710_ == 0)
{
goto v___jp_691_;
}
else
{
v___y_618_ = v___y_273_;
v___y_619_ = v___y_274_;
v___y_620_ = v___y_275_;
v___y_621_ = v___y_276_;
goto v___jp_617_;
}
}
}
v___jp_278_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_284_, v___y_283_);
v___x_303_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_303_, 0, v_fileName_288_);
lean_ctor_set(v___x_303_, 1, v_fileMap_289_);
lean_ctor_set(v___x_303_, 2, v___y_284_);
lean_ctor_set(v___x_303_, 3, v_currRecDepth_290_);
lean_ctor_set(v___x_303_, 4, v___x_302_);
lean_ctor_set(v___x_303_, 5, v_ref_291_);
lean_ctor_set(v___x_303_, 6, v_currNamespace_292_);
lean_ctor_set(v___x_303_, 7, v_openDecls_293_);
lean_ctor_set(v___x_303_, 8, v_initHeartbeats_294_);
lean_ctor_set(v___x_303_, 9, v_maxHeartbeats_295_);
lean_ctor_set(v___x_303_, 10, v_quotContext_296_);
lean_ctor_set(v___x_303_, 11, v_currMacroScope_297_);
lean_ctor_set(v___x_303_, 12, v_cancelTk_x3f_298_);
lean_ctor_set(v___x_303_, 13, v_inheritedTraceOptions_300_);
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*14, v___y_281_);
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*14 + 1, v_suppressElabErrors_299_);
v___x_304_ = l_Lean_addAndCompile(v___y_285_, v___y_280_, v___y_286_, v___x_303_, v___y_301_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; 
lean_dec_ref_known(v___x_304_, 1);
v___x_305_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_287_, v_checkMeta_269_, v___y_279_, v___y_282_, v___x_303_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref_known(v___x_303_, 14);
lean_dec(v___y_282_);
lean_dec_ref(v___y_279_);
return v___x_305_;
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref_known(v___x_303_, 14);
lean_dec(v___y_301_);
lean_dec(v___y_287_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_279_);
v_a_306_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_304_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
v___jp_314_:
{
lean_object* v_fileName_326_; lean_object* v_fileMap_327_; lean_object* v_currRecDepth_328_; lean_object* v_ref_329_; lean_object* v_currNamespace_330_; lean_object* v_openDecls_331_; lean_object* v_initHeartbeats_332_; lean_object* v_maxHeartbeats_333_; lean_object* v_quotContext_334_; lean_object* v_currMacroScope_335_; lean_object* v_cancelTk_x3f_336_; uint8_t v_suppressElabErrors_337_; lean_object* v_inheritedTraceOptions_338_; 
v_fileName_326_ = lean_ctor_get(v___y_324_, 0);
lean_inc_ref(v_fileName_326_);
v_fileMap_327_ = lean_ctor_get(v___y_324_, 1);
lean_inc_ref(v_fileMap_327_);
v_currRecDepth_328_ = lean_ctor_get(v___y_324_, 3);
lean_inc(v_currRecDepth_328_);
v_ref_329_ = lean_ctor_get(v___y_324_, 5);
lean_inc(v_ref_329_);
v_currNamespace_330_ = lean_ctor_get(v___y_324_, 6);
lean_inc(v_currNamespace_330_);
v_openDecls_331_ = lean_ctor_get(v___y_324_, 7);
lean_inc(v_openDecls_331_);
v_initHeartbeats_332_ = lean_ctor_get(v___y_324_, 8);
lean_inc(v_initHeartbeats_332_);
v_maxHeartbeats_333_ = lean_ctor_get(v___y_324_, 9);
lean_inc(v_maxHeartbeats_333_);
v_quotContext_334_ = lean_ctor_get(v___y_324_, 10);
lean_inc(v_quotContext_334_);
v_currMacroScope_335_ = lean_ctor_get(v___y_324_, 11);
lean_inc(v_currMacroScope_335_);
v_cancelTk_x3f_336_ = lean_ctor_get(v___y_324_, 12);
lean_inc(v_cancelTk_x3f_336_);
v_suppressElabErrors_337_ = lean_ctor_get_uint8(v___y_324_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_338_ = lean_ctor_get(v___y_324_, 13);
lean_inc_ref(v_inheritedTraceOptions_338_);
lean_dec_ref(v___y_324_);
v___y_279_ = v___y_315_;
v___y_280_ = v___y_316_;
v___y_281_ = v___y_317_;
v___y_282_ = v___y_318_;
v___y_283_ = v___y_319_;
v___y_284_ = v___y_320_;
v___y_285_ = v___y_321_;
v___y_286_ = v___y_322_;
v___y_287_ = v___y_323_;
v_fileName_288_ = v_fileName_326_;
v_fileMap_289_ = v_fileMap_327_;
v_currRecDepth_290_ = v_currRecDepth_328_;
v_ref_291_ = v_ref_329_;
v_currNamespace_292_ = v_currNamespace_330_;
v_openDecls_293_ = v_openDecls_331_;
v_initHeartbeats_294_ = v_initHeartbeats_332_;
v_maxHeartbeats_295_ = v_maxHeartbeats_333_;
v_quotContext_296_ = v_quotContext_334_;
v_currMacroScope_297_ = v_currMacroScope_335_;
v_cancelTk_x3f_298_ = v_cancelTk_x3f_336_;
v_suppressElabErrors_299_ = v_suppressElabErrors_337_;
v_inheritedTraceOptions_300_ = v_inheritedTraceOptions_338_;
v___y_301_ = v___y_325_;
goto v___jp_278_;
}
v___jp_339_:
{
if (v___y_352_ == 0)
{
lean_object* v___x_353_; lean_object* v_env_354_; lean_object* v_nextMacroScope_355_; lean_object* v_ngen_356_; lean_object* v_auxDeclNGen_357_; lean_object* v_traceState_358_; lean_object* v_messages_359_; lean_object* v_infoState_360_; lean_object* v_snapshotTasks_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_370_; 
v___x_353_ = lean_st_ref_take(v___y_345_);
v_env_354_ = lean_ctor_get(v___x_353_, 0);
v_nextMacroScope_355_ = lean_ctor_get(v___x_353_, 1);
v_ngen_356_ = lean_ctor_get(v___x_353_, 2);
v_auxDeclNGen_357_ = lean_ctor_get(v___x_353_, 3);
v_traceState_358_ = lean_ctor_get(v___x_353_, 4);
v_messages_359_ = lean_ctor_get(v___x_353_, 6);
v_infoState_360_ = lean_ctor_get(v___x_353_, 7);
v_snapshotTasks_361_ = lean_ctor_get(v___x_353_, 8);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_353_, 5);
lean_dec(v_unused_371_);
v___x_363_ = v___x_353_;
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_snapshotTasks_361_);
lean_inc(v_infoState_360_);
lean_inc(v_messages_359_);
lean_inc(v_traceState_358_);
lean_inc(v_auxDeclNGen_357_);
lean_inc(v_ngen_356_);
lean_inc(v_nextMacroScope_355_);
lean_inc(v_env_354_);
lean_dec(v___x_353_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = l_Lean_Kernel_enableDiag(v_env_354_, v___y_347_);
lean_inc_ref(v___y_351_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 5, v___y_351_);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_nextMacroScope_355_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_ngen_356_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_auxDeclNGen_357_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_traceState_358_);
lean_ctor_set(v_reuseFailAlloc_369_, 5, v___y_351_);
lean_ctor_set(v_reuseFailAlloc_369_, 6, v_messages_359_);
lean_ctor_set(v_reuseFailAlloc_369_, 7, v_infoState_360_);
lean_ctor_set(v_reuseFailAlloc_369_, 8, v_snapshotTasks_361_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; 
v___x_368_ = lean_st_ref_put(v___y_345_, v___x_367_);
v___y_315_ = v___y_340_;
v___y_316_ = v___y_342_;
v___y_317_ = v___y_347_;
v___y_318_ = v___y_348_;
v___y_319_ = v___y_343_;
v___y_320_ = v___y_349_;
v___y_321_ = v___y_344_;
v___y_322_ = v___y_350_;
v___y_323_ = v___y_346_;
v___y_324_ = v___y_341_;
v___y_325_ = v___y_345_;
goto v___jp_314_;
}
}
}
else
{
v___y_315_ = v___y_340_;
v___y_316_ = v___y_342_;
v___y_317_ = v___y_347_;
v___y_318_ = v___y_348_;
v___y_319_ = v___y_343_;
v___y_320_ = v___y_349_;
v___y_321_ = v___y_344_;
v___y_322_ = v___y_350_;
v___y_323_ = v___y_346_;
v___y_324_ = v___y_341_;
v___y_325_ = v___y_345_;
goto v___jp_314_;
}
}
v___jp_372_:
{
lean_object* v___x_386_; lean_object* v_fileName_387_; lean_object* v_fileMap_388_; lean_object* v_currRecDepth_389_; lean_object* v_ref_390_; lean_object* v_currNamespace_391_; lean_object* v_openDecls_392_; lean_object* v_initHeartbeats_393_; lean_object* v_maxHeartbeats_394_; lean_object* v_quotContext_395_; lean_object* v_currMacroScope_396_; lean_object* v_cancelTk_x3f_397_; uint8_t v_suppressElabErrors_398_; lean_object* v_inheritedTraceOptions_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_412_; 
v___x_386_ = lean_st_ref_get(v___y_385_);
v_fileName_387_ = lean_ctor_get(v___y_384_, 0);
v_fileMap_388_ = lean_ctor_get(v___y_384_, 1);
v_currRecDepth_389_ = lean_ctor_get(v___y_384_, 3);
v_ref_390_ = lean_ctor_get(v___y_384_, 5);
v_currNamespace_391_ = lean_ctor_get(v___y_384_, 6);
v_openDecls_392_ = lean_ctor_get(v___y_384_, 7);
v_initHeartbeats_393_ = lean_ctor_get(v___y_384_, 8);
v_maxHeartbeats_394_ = lean_ctor_get(v___y_384_, 9);
v_quotContext_395_ = lean_ctor_get(v___y_384_, 10);
v_currMacroScope_396_ = lean_ctor_get(v___y_384_, 11);
v_cancelTk_x3f_397_ = lean_ctor_get(v___y_384_, 12);
v_suppressElabErrors_398_ = lean_ctor_get_uint8(v___y_384_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_399_ = lean_ctor_get(v___y_384_, 13);
v_isSharedCheck_412_ = !lean_is_exclusive(v___y_384_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; lean_object* v_unused_414_; 
v_unused_413_ = lean_ctor_get(v___y_384_, 4);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v___y_384_, 2);
lean_dec(v_unused_414_);
v___x_401_ = v___y_384_;
v_isShared_402_ = v_isSharedCheck_412_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_inheritedTraceOptions_399_);
lean_inc(v_cancelTk_x3f_397_);
lean_inc(v_currMacroScope_396_);
lean_inc(v_quotContext_395_);
lean_inc(v_maxHeartbeats_394_);
lean_inc(v_initHeartbeats_393_);
lean_inc(v_openDecls_392_);
lean_inc(v_currNamespace_391_);
lean_inc(v_ref_390_);
lean_inc(v_currRecDepth_389_);
lean_inc(v_fileMap_388_);
lean_inc(v_fileName_387_);
lean_dec(v___y_384_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_412_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_env_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v_env_403_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_386_);
v___x_404_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_373_, v___y_378_);
lean_inc_ref(v_inheritedTraceOptions_399_);
lean_inc(v_cancelTk_x3f_397_);
lean_inc(v_currMacroScope_396_);
lean_inc(v_quotContext_395_);
lean_inc(v_maxHeartbeats_394_);
lean_inc(v_initHeartbeats_393_);
lean_inc(v_openDecls_392_);
lean_inc(v_currNamespace_391_);
lean_inc(v_ref_390_);
lean_inc(v_currRecDepth_389_);
lean_inc_ref(v___y_373_);
lean_inc_ref(v_fileMap_388_);
lean_inc_ref(v_fileName_387_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 4, v___x_404_);
lean_ctor_set(v___x_401_, 2, v___y_373_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_fileName_387_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_fileMap_388_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v___y_373_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_currRecDepth_389_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v_ref_390_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_currNamespace_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_openDecls_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_initHeartbeats_393_);
lean_ctor_set(v_reuseFailAlloc_411_, 9, v_maxHeartbeats_394_);
lean_ctor_set(v_reuseFailAlloc_411_, 10, v_quotContext_395_);
lean_ctor_set(v_reuseFailAlloc_411_, 11, v_currMacroScope_396_);
lean_ctor_set(v_reuseFailAlloc_411_, 12, v_cancelTk_x3f_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 13, v_inheritedTraceOptions_399_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, sizeof(void*)*14 + 1, v_suppressElabErrors_398_);
v___x_406_ = v_reuseFailAlloc_411_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; uint8_t v___x_410_; 
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*14, v___y_374_);
v___x_407_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_408_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_373_, v___x_407_, v___y_375_);
v___x_409_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_408_, v___y_381_);
v___x_410_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_403_);
lean_dec_ref(v_env_403_);
if (v___x_410_ == 0)
{
if (v___x_409_ == 0)
{
lean_dec_ref(v___x_406_);
v___y_279_ = v___y_376_;
v___y_280_ = v___y_375_;
v___y_281_ = v___x_409_;
v___y_282_ = v___y_377_;
v___y_283_ = v___y_378_;
v___y_284_ = v___x_408_;
v___y_285_ = v___y_379_;
v___y_286_ = v___y_380_;
v___y_287_ = v___y_382_;
v_fileName_288_ = v_fileName_387_;
v_fileMap_289_ = v_fileMap_388_;
v_currRecDepth_290_ = v_currRecDepth_389_;
v_ref_291_ = v_ref_390_;
v_currNamespace_292_ = v_currNamespace_391_;
v_openDecls_293_ = v_openDecls_392_;
v_initHeartbeats_294_ = v_initHeartbeats_393_;
v_maxHeartbeats_295_ = v_maxHeartbeats_394_;
v_quotContext_296_ = v_quotContext_395_;
v_currMacroScope_297_ = v_currMacroScope_396_;
v_cancelTk_x3f_298_ = v_cancelTk_x3f_397_;
v_suppressElabErrors_299_ = v_suppressElabErrors_398_;
v_inheritedTraceOptions_300_ = v_inheritedTraceOptions_399_;
v___y_301_ = v___y_385_;
goto v___jp_278_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_399_);
lean_dec(v_cancelTk_x3f_397_);
lean_dec(v_currMacroScope_396_);
lean_dec(v_quotContext_395_);
lean_dec(v_maxHeartbeats_394_);
lean_dec(v_initHeartbeats_393_);
lean_dec(v_openDecls_392_);
lean_dec(v_currNamespace_391_);
lean_dec(v_ref_390_);
lean_dec(v_currRecDepth_389_);
lean_dec_ref(v_fileMap_388_);
lean_dec_ref(v_fileName_387_);
v___y_340_ = v___y_376_;
v___y_341_ = v___x_406_;
v___y_342_ = v___y_375_;
v___y_343_ = v___y_378_;
v___y_344_ = v___y_379_;
v___y_345_ = v___y_385_;
v___y_346_ = v___y_382_;
v___y_347_ = v___x_409_;
v___y_348_ = v___y_377_;
v___y_349_ = v___x_408_;
v___y_350_ = v___y_380_;
v___y_351_ = v___y_383_;
v___y_352_ = v___x_410_;
goto v___jp_339_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_399_);
lean_dec(v_cancelTk_x3f_397_);
lean_dec(v_currMacroScope_396_);
lean_dec(v_quotContext_395_);
lean_dec(v_maxHeartbeats_394_);
lean_dec(v_initHeartbeats_393_);
lean_dec(v_openDecls_392_);
lean_dec(v_currNamespace_391_);
lean_dec(v_ref_390_);
lean_dec(v_currRecDepth_389_);
lean_dec_ref(v_fileMap_388_);
lean_dec_ref(v_fileName_387_);
v___y_340_ = v___y_376_;
v___y_341_ = v___x_406_;
v___y_342_ = v___y_375_;
v___y_343_ = v___y_378_;
v___y_344_ = v___y_379_;
v___y_345_ = v___y_385_;
v___y_346_ = v___y_382_;
v___y_347_ = v___x_409_;
v___y_348_ = v___y_377_;
v___y_349_ = v___x_408_;
v___y_350_ = v___y_380_;
v___y_351_ = v___y_383_;
v___y_352_ = v___x_409_;
goto v___jp_339_;
}
}
}
}
v___jp_415_:
{
if (v___y_429_ == 0)
{
lean_object* v___x_430_; lean_object* v_env_431_; lean_object* v_nextMacroScope_432_; lean_object* v_ngen_433_; lean_object* v_auxDeclNGen_434_; lean_object* v_traceState_435_; lean_object* v_messages_436_; lean_object* v_infoState_437_; lean_object* v_snapshotTasks_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_447_; 
v___x_430_ = lean_st_ref_take(v___y_427_);
v_env_431_ = lean_ctor_get(v___x_430_, 0);
v_nextMacroScope_432_ = lean_ctor_get(v___x_430_, 1);
v_ngen_433_ = lean_ctor_get(v___x_430_, 2);
v_auxDeclNGen_434_ = lean_ctor_get(v___x_430_, 3);
v_traceState_435_ = lean_ctor_get(v___x_430_, 4);
v_messages_436_ = lean_ctor_get(v___x_430_, 6);
v_infoState_437_ = lean_ctor_get(v___x_430_, 7);
v_snapshotTasks_438_ = lean_ctor_get(v___x_430_, 8);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_430_, 5);
lean_dec(v_unused_448_);
v___x_440_ = v___x_430_;
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snapshotTasks_438_);
lean_inc(v_infoState_437_);
lean_inc(v_messages_436_);
lean_inc(v_traceState_435_);
lean_inc(v_auxDeclNGen_434_);
lean_inc(v_ngen_433_);
lean_inc(v_nextMacroScope_432_);
lean_inc(v_env_431_);
lean_dec(v___x_430_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = l_Lean_Kernel_enableDiag(v_env_431_, v___y_417_);
lean_inc_ref(v___y_428_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 5, v___y_428_);
lean_ctor_set(v___x_440_, 0, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_nextMacroScope_432_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_ngen_433_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_auxDeclNGen_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_traceState_435_);
lean_ctor_set(v_reuseFailAlloc_446_, 5, v___y_428_);
lean_ctor_set(v_reuseFailAlloc_446_, 6, v_messages_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 7, v_infoState_437_);
lean_ctor_set(v_reuseFailAlloc_446_, 8, v_snapshotTasks_438_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_st_ref_put(v___y_427_, v___x_444_);
v___y_373_ = v___y_423_;
v___y_374_ = v___y_417_;
v___y_375_ = v___y_418_;
v___y_376_ = v___y_416_;
v___y_377_ = v___y_425_;
v___y_378_ = v___y_419_;
v___y_379_ = v___y_420_;
v___y_380_ = v___y_426_;
v___y_381_ = v___y_421_;
v___y_382_ = v___y_422_;
v___y_383_ = v___y_428_;
v___y_384_ = v___y_424_;
v___y_385_ = v___y_427_;
goto v___jp_372_;
}
}
}
else
{
v___y_373_ = v___y_423_;
v___y_374_ = v___y_417_;
v___y_375_ = v___y_418_;
v___y_376_ = v___y_416_;
v___y_377_ = v___y_425_;
v___y_378_ = v___y_419_;
v___y_379_ = v___y_420_;
v___y_380_ = v___y_426_;
v___y_381_ = v___y_421_;
v___y_382_ = v___y_422_;
v___y_383_ = v___y_428_;
v___y_384_ = v___y_424_;
v___y_385_ = v___y_427_;
goto v___jp_372_;
}
}
v___jp_449_:
{
lean_object* v___x_462_; lean_object* v_fileName_463_; lean_object* v_fileMap_464_; lean_object* v_currRecDepth_465_; lean_object* v_ref_466_; lean_object* v_currNamespace_467_; lean_object* v_openDecls_468_; lean_object* v_initHeartbeats_469_; lean_object* v_maxHeartbeats_470_; lean_object* v_quotContext_471_; lean_object* v_currMacroScope_472_; lean_object* v_cancelTk_x3f_473_; uint8_t v_suppressElabErrors_474_; lean_object* v_inheritedTraceOptions_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_489_; 
v___x_462_ = lean_st_ref_get(v___y_461_);
v_fileName_463_ = lean_ctor_get(v___y_460_, 0);
v_fileMap_464_ = lean_ctor_get(v___y_460_, 1);
v_currRecDepth_465_ = lean_ctor_get(v___y_460_, 3);
v_ref_466_ = lean_ctor_get(v___y_460_, 5);
v_currNamespace_467_ = lean_ctor_get(v___y_460_, 6);
v_openDecls_468_ = lean_ctor_get(v___y_460_, 7);
v_initHeartbeats_469_ = lean_ctor_get(v___y_460_, 8);
v_maxHeartbeats_470_ = lean_ctor_get(v___y_460_, 9);
v_quotContext_471_ = lean_ctor_get(v___y_460_, 10);
v_currMacroScope_472_ = lean_ctor_get(v___y_460_, 11);
v_cancelTk_x3f_473_ = lean_ctor_get(v___y_460_, 12);
v_suppressElabErrors_474_ = lean_ctor_get_uint8(v___y_460_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_475_ = lean_ctor_get(v___y_460_, 13);
v_isSharedCheck_489_ = !lean_is_exclusive(v___y_460_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; lean_object* v_unused_491_; 
v_unused_490_ = lean_ctor_get(v___y_460_, 4);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v___y_460_, 2);
lean_dec(v_unused_491_);
v___x_477_ = v___y_460_;
v_isShared_478_ = v_isSharedCheck_489_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_inheritedTraceOptions_475_);
lean_inc(v_cancelTk_x3f_473_);
lean_inc(v_currMacroScope_472_);
lean_inc(v_quotContext_471_);
lean_inc(v_maxHeartbeats_470_);
lean_inc(v_initHeartbeats_469_);
lean_inc(v_openDecls_468_);
lean_inc(v_currNamespace_467_);
lean_inc(v_ref_466_);
lean_inc(v_currRecDepth_465_);
lean_inc(v_fileMap_464_);
lean_inc(v_fileName_463_);
lean_dec(v___y_460_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_489_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_env_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v_env_479_ = lean_ctor_get(v___x_462_, 0);
lean_inc_ref(v_env_479_);
lean_dec(v___x_462_);
v___x_480_ = l_Lean_maxRecDepth;
v___x_481_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_453_, v___x_480_);
lean_inc_ref(v___y_453_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 4, v___x_481_);
lean_ctor_set(v___x_477_, 2, v___y_453_);
v___x_483_ = v___x_477_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_fileName_463_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_fileMap_464_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v___y_453_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_currRecDepth_465_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_488_, 5, v_ref_466_);
lean_ctor_set(v_reuseFailAlloc_488_, 6, v_currNamespace_467_);
lean_ctor_set(v_reuseFailAlloc_488_, 7, v_openDecls_468_);
lean_ctor_set(v_reuseFailAlloc_488_, 8, v_initHeartbeats_469_);
lean_ctor_set(v_reuseFailAlloc_488_, 9, v_maxHeartbeats_470_);
lean_ctor_set(v_reuseFailAlloc_488_, 10, v_quotContext_471_);
lean_ctor_set(v_reuseFailAlloc_488_, 11, v_currMacroScope_472_);
lean_ctor_set(v_reuseFailAlloc_488_, 12, v_cancelTk_x3f_473_);
lean_ctor_set(v_reuseFailAlloc_488_, 13, v_inheritedTraceOptions_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_488_, sizeof(void*)*14 + 1, v_suppressElabErrors_474_);
v___x_483_ = v_reuseFailAlloc_488_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; uint8_t v___x_487_; 
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*14, v___y_455_);
v___x_484_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_485_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_453_, v___x_484_, v___y_454_);
v___x_486_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_485_, v___y_457_);
v___x_487_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_479_);
lean_dec_ref(v_env_479_);
if (v___x_487_ == 0)
{
if (v___x_486_ == 0)
{
v___y_373_ = v___x_485_;
v___y_374_ = v___x_486_;
v___y_375_ = v___y_451_;
v___y_376_ = v___y_450_;
v___y_377_ = v___y_452_;
v___y_378_ = v___x_480_;
v___y_379_ = v___y_456_;
v___y_380_ = v___y_454_;
v___y_381_ = v___y_457_;
v___y_382_ = v___y_458_;
v___y_383_ = v___y_459_;
v___y_384_ = v___x_483_;
v___y_385_ = v___y_461_;
goto v___jp_372_;
}
else
{
v___y_416_ = v___y_450_;
v___y_417_ = v___x_486_;
v___y_418_ = v___y_451_;
v___y_419_ = v___x_480_;
v___y_420_ = v___y_456_;
v___y_421_ = v___y_457_;
v___y_422_ = v___y_458_;
v___y_423_ = v___x_485_;
v___y_424_ = v___x_483_;
v___y_425_ = v___y_452_;
v___y_426_ = v___y_454_;
v___y_427_ = v___y_461_;
v___y_428_ = v___y_459_;
v___y_429_ = v___x_487_;
goto v___jp_415_;
}
}
else
{
v___y_416_ = v___y_450_;
v___y_417_ = v___x_486_;
v___y_418_ = v___y_451_;
v___y_419_ = v___x_480_;
v___y_420_ = v___y_456_;
v___y_421_ = v___y_457_;
v___y_422_ = v___y_458_;
v___y_423_ = v___x_485_;
v___y_424_ = v___x_483_;
v___y_425_ = v___y_452_;
v___y_426_ = v___y_454_;
v___y_427_ = v___y_461_;
v___y_428_ = v___y_459_;
v___y_429_ = v___x_486_;
goto v___jp_415_;
}
}
}
}
v___jp_492_:
{
if (v___y_505_ == 0)
{
lean_object* v___x_506_; lean_object* v_env_507_; lean_object* v_nextMacroScope_508_; lean_object* v_ngen_509_; lean_object* v_auxDeclNGen_510_; lean_object* v_traceState_511_; lean_object* v_messages_512_; lean_object* v_infoState_513_; lean_object* v_snapshotTasks_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_523_; 
v___x_506_ = lean_st_ref_take(v___y_503_);
v_env_507_ = lean_ctor_get(v___x_506_, 0);
v_nextMacroScope_508_ = lean_ctor_get(v___x_506_, 1);
v_ngen_509_ = lean_ctor_get(v___x_506_, 2);
v_auxDeclNGen_510_ = lean_ctor_get(v___x_506_, 3);
v_traceState_511_ = lean_ctor_get(v___x_506_, 4);
v_messages_512_ = lean_ctor_get(v___x_506_, 6);
v_infoState_513_ = lean_ctor_get(v___x_506_, 7);
v_snapshotTasks_514_ = lean_ctor_get(v___x_506_, 8);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_506_, 5);
lean_dec(v_unused_524_);
v___x_516_ = v___x_506_;
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snapshotTasks_514_);
lean_inc(v_infoState_513_);
lean_inc(v_messages_512_);
lean_inc(v_traceState_511_);
lean_inc(v_auxDeclNGen_510_);
lean_inc(v_ngen_509_);
lean_inc(v_nextMacroScope_508_);
lean_inc(v_env_507_);
lean_dec(v___x_506_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_523_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = l_Lean_Kernel_enableDiag(v_env_507_, v___y_497_);
lean_inc_ref(v___y_504_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 5, v___y_504_);
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_nextMacroScope_508_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_ngen_509_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_auxDeclNGen_510_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_traceState_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 5, v___y_504_);
lean_ctor_set(v_reuseFailAlloc_522_, 6, v_messages_512_);
lean_ctor_set(v_reuseFailAlloc_522_, 7, v_infoState_513_);
lean_ctor_set(v_reuseFailAlloc_522_, 8, v_snapshotTasks_514_);
v___x_520_ = v_reuseFailAlloc_522_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_st_ref_put(v___y_503_, v___x_520_);
v___y_450_ = v___y_493_;
v___y_451_ = v___y_494_;
v___y_452_ = v___y_501_;
v___y_453_ = v___y_495_;
v___y_454_ = v___y_502_;
v___y_455_ = v___y_497_;
v___y_456_ = v___y_496_;
v___y_457_ = v___y_498_;
v___y_458_ = v___y_499_;
v___y_459_ = v___y_504_;
v___y_460_ = v___y_500_;
v___y_461_ = v___y_503_;
goto v___jp_449_;
}
}
}
else
{
v___y_450_ = v___y_493_;
v___y_451_ = v___y_494_;
v___y_452_ = v___y_501_;
v___y_453_ = v___y_495_;
v___y_454_ = v___y_502_;
v___y_455_ = v___y_497_;
v___y_456_ = v___y_496_;
v___y_457_ = v___y_498_;
v___y_458_ = v___y_499_;
v___y_459_ = v___y_504_;
v___y_460_ = v___y_500_;
v___y_461_ = v___y_503_;
goto v___jp_449_;
}
}
v___jp_525_:
{
lean_object* v___x_534_; 
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc_ref(v___y_527_);
v___x_534_ = lean_infer_type(v___y_527_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc_n(v_a_535_, 2);
lean_dec_ref_known(v___x_534_, 1);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
v___x_536_ = lean_apply_6(v_checkType_270_, v_a_535_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, lean_box(0));
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; lean_object* v_env_538_; lean_object* v_nextMacroScope_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_traceState_542_; lean_object* v_messages_543_; lean_object* v_infoState_544_; lean_object* v_snapshotTasks_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref_known(v___x_536_, 1);
v___x_537_ = lean_st_ref_take(v___y_533_);
v_env_538_ = lean_ctor_get(v___x_537_, 0);
v_nextMacroScope_539_ = lean_ctor_get(v___x_537_, 1);
v_ngen_540_ = lean_ctor_get(v___x_537_, 2);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_537_, 3);
v_traceState_542_ = lean_ctor_get(v___x_537_, 4);
v_messages_543_ = lean_ctor_get(v___x_537_, 6);
v_infoState_544_ = lean_ctor_get(v___x_537_, 7);
v_snapshotTasks_545_ = lean_ctor_get(v___x_537_, 8);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_537_, 5);
lean_dec(v_unused_600_);
v___x_547_ = v___x_537_;
v_isShared_548_ = v_isSharedCheck_599_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snapshotTasks_545_);
lean_inc(v_infoState_544_);
lean_inc(v_messages_543_);
lean_inc(v_traceState_542_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_nextMacroScope_539_);
lean_inc(v_env_538_);
lean_dec(v___x_537_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_599_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_549_ = lean_array_to_list(v___y_526_);
lean_inc_n(v___y_529_, 3);
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v___y_529_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
lean_ctor_set(v___x_550_, 2, v_a_535_);
lean_inc(v___y_528_);
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v___y_529_);
lean_ctor_set(v___x_551_, 1, v___y_528_);
v___x_552_ = l_Lean_markMeta(v_env_538_, v___y_529_);
v___x_553_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 5, v___x_553_);
lean_ctor_set(v___x_547_, 0, v___x_552_);
v___x_555_ = v___x_547_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_nextMacroScope_539_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_traceState_542_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_messages_543_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_infoState_544_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_snapshotTasks_545_);
v___x_555_ = v_reuseFailAlloc_598_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_mctx_558_; lean_object* v_zetaDeltaFVarIds_559_; lean_object* v_postponed_560_; lean_object* v_diag_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_596_; 
v___x_556_ = lean_st_ref_put(v___y_533_, v___x_555_);
v___x_557_ = lean_st_ref_take(v___y_531_);
v_mctx_558_ = lean_ctor_get(v___x_557_, 0);
v_zetaDeltaFVarIds_559_ = lean_ctor_get(v___x_557_, 2);
v_postponed_560_ = lean_ctor_get(v___x_557_, 3);
v_diag_561_ = lean_ctor_get(v___x_557_, 4);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_557_, 1);
lean_dec(v_unused_597_);
v___x_563_ = v___x_557_;
v_isShared_564_ = v_isSharedCheck_596_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_diag_561_);
lean_inc(v_postponed_560_);
lean_inc(v_zetaDeltaFVarIds_559_);
lean_inc(v_mctx_558_);
lean_dec(v___x_557_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_596_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_mctx_558_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_zetaDeltaFVarIds_559_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_postponed_560_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_diag_561_);
v___x_567_ = v_reuseFailAlloc_595_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_env_570_; lean_object* v_checked_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_568_ = lean_st_ref_put(v___y_531_, v___x_567_);
v___x_569_ = lean_st_ref_get(v___y_533_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_env_570_);
lean_dec(v___x_569_);
v_checked_571_ = lean_ctor_get(v_env_570_, 2);
lean_inc_ref(v_checked_571_);
lean_dec_ref(v_env_570_);
v___x_572_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_573_ = l_Lean_traceBlock___redArg(v___x_572_, v_checked_571_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_574_; lean_object* v_options_575_; lean_object* v_env_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; uint8_t v___x_586_; 
lean_dec_ref_known(v___x_573_, 1);
v___x_574_ = lean_st_ref_get(v___y_533_);
v_options_575_ = lean_ctor_get(v___y_532_, 2);
v_env_576_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_env_576_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_578_, 0, v___x_550_);
lean_ctor_set(v___x_578_, 1, v___y_527_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
lean_ctor_set(v___x_578_, 3, v___x_551_);
lean_ctor_set_uint8(v___x_578_, sizeof(void*)*4, v_safety_271_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___x_580_ = 1;
v___x_581_ = 0;
v___x_582_ = l_Lean_Elab_async;
lean_inc_ref(v_options_575_);
v___x_583_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_575_, v___x_582_, v___x_581_);
v___x_584_ = l_Lean_diagnostics;
v___x_585_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_583_, v___x_584_);
v___x_586_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_576_);
lean_dec_ref(v_env_576_);
if (v___x_586_ == 0)
{
if (v___x_585_ == 0)
{
v___y_450_ = v___y_530_;
v___y_451_ = v___x_580_;
v___y_452_ = v___y_531_;
v___y_453_ = v___x_583_;
v___y_454_ = v___x_581_;
v___y_455_ = v___x_585_;
v___y_456_ = v___x_579_;
v___y_457_ = v___x_584_;
v___y_458_ = v___y_529_;
v___y_459_ = v___x_553_;
v___y_460_ = v___y_532_;
v___y_461_ = v___y_533_;
goto v___jp_449_;
}
else
{
v___y_493_ = v___y_530_;
v___y_494_ = v___x_580_;
v___y_495_ = v___x_583_;
v___y_496_ = v___x_579_;
v___y_497_ = v___x_585_;
v___y_498_ = v___x_584_;
v___y_499_ = v___y_529_;
v___y_500_ = v___y_532_;
v___y_501_ = v___y_531_;
v___y_502_ = v___x_581_;
v___y_503_ = v___y_533_;
v___y_504_ = v___x_553_;
v___y_505_ = v___x_586_;
goto v___jp_492_;
}
}
else
{
v___y_493_ = v___y_530_;
v___y_494_ = v___x_580_;
v___y_495_ = v___x_583_;
v___y_496_ = v___x_579_;
v___y_497_ = v___x_585_;
v___y_498_ = v___x_584_;
v___y_499_ = v___y_529_;
v___y_500_ = v___y_532_;
v___y_501_ = v___y_531_;
v___y_502_ = v___x_581_;
v___y_503_ = v___y_533_;
v___y_504_ = v___x_553_;
v___y_505_ = v___x_585_;
goto v___jp_492_;
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref_known(v___x_551_, 2);
lean_dec_ref_known(v___x_550_, 3);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_527_);
v_a_587_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_573_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_573_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
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
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_a_535_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_526_);
v_a_601_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_536_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_536_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec_ref(v_checkType_270_);
v_a_609_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_534_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_534_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
v___jp_617_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_st_ref_get(v___y_621_);
v___x_623_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_624_ = l_Lean_Core_mkFreshUserName(v___x_623_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_272_, v___y_619_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v_env_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_params_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc_n(v_a_627_, 2);
lean_dec_ref_known(v___x_626_, 1);
v_env_628_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_env_628_);
lean_dec(v___x_622_);
v___x_629_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11);
v___x_630_ = l_Lean_collectLevelParams(v___x_629_, v_a_627_);
v_params_631_ = lean_ctor_get(v___x_630_, 2);
lean_inc_ref(v_params_631_);
lean_dec_ref(v___x_630_);
v___x_632_ = l_Lean_mkPrivateName(v_env_628_, v_a_625_);
lean_dec_ref(v_env_628_);
v___x_633_ = lean_box(0);
v___x_634_ = l_Lean_Expr_hasMVar(v_a_627_);
if (v___x_634_ == 0)
{
v___y_526_ = v_params_631_;
v___y_527_ = v_a_627_;
v___y_528_ = v___x_633_;
v___y_529_ = v___x_632_;
v___y_530_ = v___y_618_;
v___y_531_ = v___y_619_;
v___y_532_ = v___y_620_;
v___y_533_ = v___y_621_;
goto v___jp_525_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13);
lean_inc(v_a_627_);
v___x_636_ = l_Lean_indentExpr(v_a_627_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_637_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref_known(v___x_638_, 1);
v___y_526_ = v_params_631_;
v___y_527_ = v_a_627_;
v___y_528_ = v___x_633_;
v___y_529_ = v___x_632_;
v___y_530_ = v___y_618_;
v___y_531_ = v___y_619_;
v___y_532_ = v___y_620_;
v___y_533_ = v___y_621_;
goto v___jp_525_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___x_632_);
lean_dec_ref(v_params_631_);
lean_dec(v_a_627_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v_checkType_270_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_a_625_);
lean_dec(v___x_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v_checkType_270_);
v_a_647_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_626_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_626_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v___x_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v_value_272_);
lean_dec_ref(v_checkType_270_);
v_a_655_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_624_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_624_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
v___jp_663_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_mctx_676_; lean_object* v_zetaDeltaFVarIds_677_; lean_object* v_postponed_678_; lean_object* v_diag_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_688_; 
v___x_672_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_673_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_673_, 0, v___y_671_);
lean_ctor_set(v___x_673_, 1, v_nextMacroScope_664_);
lean_ctor_set(v___x_673_, 2, v_ngen_665_);
lean_ctor_set(v___x_673_, 3, v_auxDeclNGen_666_);
lean_ctor_set(v___x_673_, 4, v_traceState_667_);
lean_ctor_set(v___x_673_, 5, v___x_672_);
lean_ctor_set(v___x_673_, 6, v_messages_668_);
lean_ctor_set(v___x_673_, 7, v_infoState_669_);
lean_ctor_set(v___x_673_, 8, v_snapshotTasks_670_);
v___x_674_ = lean_st_ref_put(v___y_276_, v___x_673_);
v___x_675_ = lean_st_ref_take(v___y_274_);
v_mctx_676_ = lean_ctor_get(v___x_675_, 0);
v_zetaDeltaFVarIds_677_ = lean_ctor_get(v___x_675_, 2);
v_postponed_678_ = lean_ctor_get(v___x_675_, 3);
v_diag_679_ = lean_ctor_get(v___x_675_, 4);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_675_, 1);
lean_dec(v_unused_689_);
v___x_681_ = v___x_675_;
v_isShared_682_ = v_isSharedCheck_688_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_diag_679_);
lean_inc(v_postponed_678_);
lean_inc(v_zetaDeltaFVarIds_677_);
lean_inc(v_mctx_676_);
lean_dec(v___x_675_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_688_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_683_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_mctx_676_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_zetaDeltaFVarIds_677_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_postponed_678_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_diag_679_);
v___x_685_ = v_reuseFailAlloc_687_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; 
v___x_686_ = lean_st_ref_put(v___y_274_, v___x_685_);
v___y_618_ = v___y_273_;
v___y_619_ = v___y_274_;
v___y_620_ = v___y_275_;
v___y_621_ = v___y_276_;
goto v___jp_617_;
}
}
}
v___jp_691_:
{
lean_object* v___x_692_; lean_object* v_env_693_; lean_object* v_nextMacroScope_694_; lean_object* v_ngen_695_; lean_object* v_auxDeclNGen_696_; lean_object* v_traceState_697_; lean_object* v_messages_698_; lean_object* v_infoState_699_; lean_object* v_snapshotTasks_700_; lean_object* v___x_701_; 
v___x_692_ = lean_st_ref_take(v___y_276_);
v_env_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc_ref_n(v_env_693_, 2);
v_nextMacroScope_694_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_nextMacroScope_694_);
v_ngen_695_ = lean_ctor_get(v___x_692_, 2);
lean_inc_ref(v_ngen_695_);
v_auxDeclNGen_696_ = lean_ctor_get(v___x_692_, 3);
lean_inc_ref(v_auxDeclNGen_696_);
v_traceState_697_ = lean_ctor_get(v___x_692_, 4);
lean_inc_ref(v_traceState_697_);
v_messages_698_ = lean_ctor_get(v___x_692_, 6);
lean_inc_ref(v_messages_698_);
v_infoState_699_ = lean_ctor_get(v___x_692_, 7);
lean_inc_ref(v_infoState_699_);
v_snapshotTasks_700_ = lean_ctor_get(v___x_692_, 8);
lean_inc_ref(v_snapshotTasks_700_);
lean_dec(v___x_692_);
v___x_701_ = l_Lean_Environment_importEnv_x3f(v_env_693_);
if (lean_obj_tag(v___x_701_) == 0)
{
v_nextMacroScope_664_ = v_nextMacroScope_694_;
v_ngen_665_ = v_ngen_695_;
v_auxDeclNGen_666_ = v_auxDeclNGen_696_;
v_traceState_667_ = v_traceState_697_;
v_messages_668_ = v_messages_698_;
v_infoState_669_ = v_infoState_699_;
v_snapshotTasks_670_ = v_snapshotTasks_700_;
v___y_671_ = v_env_693_;
goto v___jp_663_;
}
else
{
lean_object* v_val_702_; 
lean_dec_ref(v_env_693_);
v_val_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v___x_701_, 1);
v_nextMacroScope_664_ = v_nextMacroScope_694_;
v_ngen_665_ = v_ngen_695_;
v_auxDeclNGen_666_ = v_auxDeclNGen_696_;
v_traceState_667_ = v_traceState_697_;
v_messages_668_ = v_messages_698_;
v_infoState_669_ = v_infoState_699_;
v_snapshotTasks_670_ = v_snapshotTasks_700_;
v___y_671_ = v_val_702_;
goto v___jp_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_711_, lean_object* v_checkType_712_, lean_object* v_safety_713_, lean_object* v_value_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v_checkMeta_boxed_720_; uint8_t v_safety_boxed_721_; lean_object* v_res_722_; 
v_checkMeta_boxed_720_ = lean_unbox(v_checkMeta_711_);
v_safety_boxed_721_ = lean_unbox(v_safety_713_);
v_res_722_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_720_, v_checkType_712_, v_safety_boxed_721_, v_value_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; lean_object* v_nextMacroScope_728_; lean_object* v_ngen_729_; lean_object* v_auxDeclNGen_730_; lean_object* v_traceState_731_; lean_object* v_messages_732_; lean_object* v_infoState_733_; lean_object* v_snapshotTasks_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_760_; 
v___x_727_ = lean_st_ref_take(v___y_725_);
v_nextMacroScope_728_ = lean_ctor_get(v___x_727_, 1);
v_ngen_729_ = lean_ctor_get(v___x_727_, 2);
v_auxDeclNGen_730_ = lean_ctor_get(v___x_727_, 3);
v_traceState_731_ = lean_ctor_get(v___x_727_, 4);
v_messages_732_ = lean_ctor_get(v___x_727_, 6);
v_infoState_733_ = lean_ctor_get(v___x_727_, 7);
v_snapshotTasks_734_ = lean_ctor_get(v___x_727_, 8);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; lean_object* v_unused_762_; 
v_unused_761_ = lean_ctor_get(v___x_727_, 5);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v___x_727_, 0);
lean_dec(v_unused_762_);
v___x_736_ = v___x_727_;
v_isShared_737_ = v_isSharedCheck_760_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snapshotTasks_734_);
lean_inc(v_infoState_733_);
lean_inc(v_messages_732_);
lean_inc(v_traceState_731_);
lean_inc(v_auxDeclNGen_730_);
lean_inc(v_ngen_729_);
lean_inc(v_nextMacroScope_728_);
lean_dec(v___x_727_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_760_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 5, v___x_738_);
lean_ctor_set(v___x_736_, 0, v_env_723_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_env_723_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_nextMacroScope_728_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_ngen_729_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_auxDeclNGen_730_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_traceState_731_);
lean_ctor_set(v_reuseFailAlloc_759_, 5, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_759_, 6, v_messages_732_);
lean_ctor_set(v_reuseFailAlloc_759_, 7, v_infoState_733_);
lean_ctor_set(v_reuseFailAlloc_759_, 8, v_snapshotTasks_734_);
v___x_740_ = v_reuseFailAlloc_759_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_mctx_743_; lean_object* v_zetaDeltaFVarIds_744_; lean_object* v_postponed_745_; lean_object* v_diag_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_757_; 
v___x_741_ = lean_st_ref_put(v___y_725_, v___x_740_);
v___x_742_ = lean_st_ref_take(v___y_724_);
v_mctx_743_ = lean_ctor_get(v___x_742_, 0);
v_zetaDeltaFVarIds_744_ = lean_ctor_get(v___x_742_, 2);
v_postponed_745_ = lean_ctor_get(v___x_742_, 3);
v_diag_746_ = lean_ctor_get(v___x_742_, 4);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_742_, 1);
lean_dec(v_unused_758_);
v___x_748_ = v___x_742_;
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_diag_746_);
lean_inc(v_postponed_745_);
lean_inc(v_zetaDeltaFVarIds_744_);
lean_inc(v_mctx_743_);
lean_dec(v___x_742_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_mctx_743_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_zetaDeltaFVarIds_744_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_postponed_745_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_diag_746_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_st_ref_put(v___y_724_, v___x_752_);
v___x_754_ = lean_box(0);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec(v___y_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_768_, lean_object* v_x_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_env_776_; lean_object* v_a_778_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_775_ = lean_st_ref_get(v___y_773_);
v_env_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc_ref(v_env_776_);
lean_dec(v___x_775_);
v___x_788_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_768_, v___y_771_, v___y_773_);
lean_dec_ref(v___x_788_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
v___x_789_ = lean_apply_5(v_x_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, lean_box(0));
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_776_, v___y_771_, v___y_773_);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_799_);
v___x_793_ = v___x_791_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_dec(v___x_791_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_a_790_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_790_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_a_800_; 
v_a_800_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_789_, 1);
v_a_778_ = v_a_800_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v___x_779_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_776_, v___y_771_, v___y_773_);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_779_, 0);
lean_dec(v_unused_787_);
v___x_781_ = v___x_779_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_dec(v___x_779_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 1);
lean_ctor_set(v___x_781_, 0, v_a_778_);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_778_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_801_, v_x_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_809_, lean_object* v_checkType_810_, uint8_t v_safety_811_, uint8_t v_checkMeta_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_env_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_818_ = lean_st_ref_get(v_a_816_);
v_env_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_env_819_);
lean_dec(v___x_818_);
v___x_820_ = lean_box(v_checkMeta_812_);
v___x_821_ = lean_box(v_safety_811_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_822_, 0, v___x_820_);
lean_closure_set(v___f_822_, 1, v_checkType_810_);
lean_closure_set(v___f_822_, 2, v___x_821_);
lean_closure_set(v___f_822_, 3, v_value_809_);
v___x_823_ = l_Lean_Environment_unlockAsync(v_env_819_);
v___x_824_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_823_, v___f_822_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_825_, lean_object* v_checkType_826_, lean_object* v_safety_827_, lean_object* v_checkMeta_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
uint8_t v_safety_boxed_834_; uint8_t v_checkMeta_boxed_835_; lean_object* v_res_836_; 
v_safety_boxed_834_ = lean_unbox(v_safety_827_);
v_checkMeta_boxed_835_ = lean_unbox(v_checkMeta_828_);
v_res_836_ = l_Lean_Meta_evalExprCore___redArg(v_value_825_, v_checkType_826_, v_safety_boxed_834_, v_checkMeta_boxed_835_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_837_, lean_object* v_value_838_, lean_object* v_checkType_839_, uint8_t v_safety_840_, uint8_t v_checkMeta_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_evalExprCore___redArg(v_value_838_, v_checkType_839_, v_safety_840_, v_checkMeta_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_848_, lean_object* v_value_849_, lean_object* v_checkType_850_, lean_object* v_safety_851_, lean_object* v_checkMeta_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
uint8_t v_safety_boxed_858_; uint8_t v_checkMeta_boxed_859_; lean_object* v_res_860_; 
v_safety_boxed_858_ = lean_unbox(v_safety_851_);
v_checkMeta_boxed_859_ = lean_unbox(v_checkMeta_852_);
v_res_860_ = l_Lean_Meta_evalExprCore(v_00_u03b1_848_, v_value_849_, v_checkType_850_, v_safety_boxed_858_, v_checkMeta_boxed_859_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_875_, lean_object* v_constName_876_, uint8_t v_checkMeta_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_876_, v_checkMeta_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_884_, lean_object* v_constName_885_, lean_object* v_checkMeta_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v_checkMeta_boxed_892_; lean_object* v_res_893_; 
v_checkMeta_boxed_892_ = lean_unbox(v_checkMeta_886_);
v_res_893_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_884_, v_constName_885_, v_checkMeta_boxed_892_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_894_, lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_902_, lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_902_, v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_910_, v___y_912_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_924_, lean_object* v_env_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_925_, v_x_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_933_, lean_object* v_env_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_933_, v_env_934_, v_x_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_950_, lean_object* v_x_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_950_, v_x_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_961_, lean_object* v_type_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Meta_whnfD(v_type_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_982_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_982_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
uint8_t v___x_973_; 
v___x_973_ = l_Lean_Expr_isConstOf(v_a_969_, v_typeName_961_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_del_object(v___x_971_);
v___x_974_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_975_ = l_Lean_indentExpr(v_a_969_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_976_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_980_; 
lean_dec(v_a_969_);
v___x_978_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_978_);
v___x_980_ = v___x_971_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_968_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_968_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_991_, lean_object* v_type_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_991_, v_type_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v_typeName_991_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_999_, lean_object* v_value_1000_, uint8_t v_safety_1001_, uint8_t v_checkMeta_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_1009_; 
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1008_, 0, v_typeName_999_);
v___x_1009_ = l_Lean_Meta_evalExprCore___redArg(v_value_1000_, v___f_1008_, v_safety_1001_, v_checkMeta_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1010_, lean_object* v_value_1011_, lean_object* v_safety_1012_, lean_object* v_checkMeta_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_safety_boxed_1019_; uint8_t v_checkMeta_boxed_1020_; lean_object* v_res_1021_; 
v_safety_boxed_1019_ = lean_unbox(v_safety_1012_);
v_checkMeta_boxed_1020_ = lean_unbox(v_checkMeta_1013_);
v_res_1021_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1010_, v_value_1011_, v_safety_boxed_1019_, v_checkMeta_boxed_1020_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1022_, lean_object* v_typeName_1023_, lean_object* v_value_1024_, uint8_t v_safety_1025_, uint8_t v_checkMeta_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1023_, v_value_1024_, v_safety_1025_, v_checkMeta_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_typeName_1034_, lean_object* v_value_1035_, lean_object* v_safety_1036_, lean_object* v_checkMeta_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_safety_boxed_1043_; uint8_t v_checkMeta_boxed_1044_; lean_object* v_res_1045_; 
v_safety_boxed_1043_ = lean_unbox(v_safety_1036_);
v_checkMeta_boxed_1044_ = lean_unbox(v_checkMeta_1037_);
v_res_1045_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1033_, v_typeName_1034_, v_value_1035_, v_safety_boxed_1043_, v_checkMeta_boxed_1044_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1045_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1051_, lean_object* v_type_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
lean_inc_ref(v_expectedType_1051_);
lean_inc_ref(v_type_1052_);
v___x_1058_ = l_Lean_Meta_isExprDefEq(v_type_1052_, v_expectedType_1051_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1083_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_unbox(v_a_1059_);
lean_dec(v_a_1059_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_del_object(v___x_1061_);
v___x_1064_ = lean_box(0);
v___x_1065_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1066_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1052_, v_expectedType_1051_, v___x_1064_, v___x_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_a_1067_);
v___x_1070_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1069_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1070_;
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1066_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1066_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec_ref(v_type_1052_);
lean_dec_ref(v_expectedType_1051_);
v___x_1079_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1079_);
v___x_1081_ = v___x_1061_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
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
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v_type_1052_);
lean_dec_ref(v_expectedType_1051_);
v_a_1084_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1058_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1058_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1092_, lean_object* v_type_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1092_, v_type_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1100_, lean_object* v_value_1101_, uint8_t v_safety_1102_, uint8_t v_checkMeta_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; 
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1109_, 0, v_expectedType_1100_);
v___x_1110_ = l_Lean_Meta_evalExprCore___redArg(v_value_1101_, v___f_1109_, v_safety_1102_, v_checkMeta_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1111_, lean_object* v_value_1112_, lean_object* v_safety_1113_, lean_object* v_checkMeta_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
uint8_t v_safety_boxed_1120_; uint8_t v_checkMeta_boxed_1121_; lean_object* v_res_1122_; 
v_safety_boxed_1120_ = lean_unbox(v_safety_1113_);
v_checkMeta_boxed_1121_ = lean_unbox(v_checkMeta_1114_);
v_res_1122_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1111_, v_value_1112_, v_safety_boxed_1120_, v_checkMeta_boxed_1121_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1123_, lean_object* v_expectedType_1124_, lean_object* v_value_1125_, uint8_t v_safety_1126_, uint8_t v_checkMeta_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1124_, v_value_1125_, v_safety_1126_, v_checkMeta_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_expectedType_1135_, lean_object* v_value_1136_, lean_object* v_safety_1137_, lean_object* v_checkMeta_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
uint8_t v_safety_boxed_1144_; uint8_t v_checkMeta_boxed_1145_; lean_object* v_res_1146_; 
v_safety_boxed_1144_ = lean_unbox(v_safety_1137_);
v_checkMeta_boxed_1145_ = lean_unbox(v_checkMeta_1138_);
v_res_1146_ = l_Lean_Meta_evalExpr(v_00_u03b1_1134_, v_expectedType_1135_, v_value_1136_, v_safety_boxed_1144_, v_checkMeta_boxed_1145_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1146_;
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

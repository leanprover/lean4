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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object* v_opts_45_, lean_object* v_opt_46_){
_start:
{
lean_object* v_name_47_; lean_object* v_defValue_48_; lean_object* v_map_49_; lean_object* v___x_50_; 
v_name_47_ = lean_ctor_get(v_opt_46_, 0);
v_defValue_48_ = lean_ctor_get(v_opt_46_, 1);
v_map_49_ = lean_ctor_get(v_opts_45_, 0);
v___x_50_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_49_, v_name_47_);
if (lean_obj_tag(v___x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = lean_unbox(v_defValue_48_);
return v___x_51_;
}
else
{
lean_object* v_val_52_; 
v_val_52_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_val_52_);
lean_dec_ref_known(v___x_50_, 1);
if (lean_obj_tag(v_val_52_) == 1)
{
uint8_t v_v_53_; 
v_v_53_ = lean_ctor_get_uint8(v_val_52_, 0);
lean_dec_ref_known(v_val_52_, 0);
return v_v_53_;
}
else
{
uint8_t v___x_54_; 
lean_dec(v_val_52_);
v___x_54_ = lean_unbox(v_defValue_48_);
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* v_opts_55_, lean_object* v_opt_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v_opts_55_, v_opt_56_);
lean_dec_ref(v_opt_56_);
lean_dec_ref(v_opts_55_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(lean_object* v_opts_59_, lean_object* v_opt_60_){
_start:
{
lean_object* v_name_61_; lean_object* v_defValue_62_; lean_object* v_map_63_; lean_object* v___x_64_; 
v_name_61_ = lean_ctor_get(v_opt_60_, 0);
v_defValue_62_ = lean_ctor_get(v_opt_60_, 1);
v_map_63_ = lean_ctor_get(v_opts_59_, 0);
v___x_64_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_63_, v_name_61_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_inc(v_defValue_62_);
return v_defValue_62_;
}
else
{
lean_object* v_val_65_; 
v_val_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v___x_64_, 1);
if (lean_obj_tag(v_val_65_) == 3)
{
lean_object* v_v_66_; 
v_v_66_ = lean_ctor_get(v_val_65_, 0);
lean_inc(v_v_66_);
lean_dec_ref_known(v_val_65_, 1);
return v_v_66_;
}
else
{
lean_dec(v_val_65_);
lean_inc(v_defValue_62_);
return v_defValue_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* v_opts_67_, lean_object* v_opt_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v_opts_67_, v_opt_68_);
lean_dec_ref(v_opt_68_);
lean_dec_ref(v_opts_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(lean_object* v_msgData_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; lean_object* v_env_77_; lean_object* v___x_78_; lean_object* v_mctx_79_; lean_object* v_lctx_80_; lean_object* v_options_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_76_ = lean_st_ref_get(v___y_74_);
v_env_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_env_77_);
lean_dec(v___x_76_);
v___x_78_ = lean_st_ref_get(v___y_72_);
v_mctx_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc_ref(v_mctx_79_);
lean_dec(v___x_78_);
v_lctx_80_ = lean_ctor_get(v___y_71_, 2);
v_options_81_ = lean_ctor_get(v___y_73_, 2);
lean_inc_ref(v_options_81_);
lean_inc_ref(v_lctx_80_);
v___x_82_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_82_, 0, v_env_77_);
lean_ctor_set(v___x_82_, 1, v_mctx_79_);
lean_ctor_set(v___x_82_, 2, v_lctx_80_);
lean_ctor_set(v___x_82_, 3, v_options_81_);
v___x_83_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_msgData_70_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8___boxed(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msgData_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(lean_object* v_msg_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_ref_98_; lean_object* v___x_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
v_ref_98_ = lean_ctor_get(v___y_95_, 5);
v___x_99_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_108_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
lean_inc(v_ref_98_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_98_);
lean_ctor_set(v___x_104_, 1, v_a_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 1);
lean_ctor_set(v___x_102_, 0, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(lean_object* v_x_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_a_122_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v_x_116_, 1);
v___x_123_ = l_Lean_stringToMessageData(v_a_122_);
v___x_124_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_123_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v_x_116_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_116_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v_x_116_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v_x_116_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 0);
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg___boxed(lean_object* v_x_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = l_Lean_Elab_abortCommandExceptionId;
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___boxed(lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object* v_constName_148_, uint8_t v_checkMeta_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; lean_object* v_env_156_; uint8_t v___x_157_; 
v___x_155_ = lean_st_ref_get(v___y_153_);
v_env_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc_ref(v_env_156_);
lean_dec(v___x_155_);
lean_inc(v_constName_148_);
v___x_157_ = lean_has_compile_error(v_env_156_, v_constName_148_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v_env_159_; lean_object* v_options_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = lean_st_ref_get(v___y_153_);
v_env_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_env_159_);
lean_dec(v___x_158_);
v_options_160_ = lean_ctor_get(v___y_152_, 2);
v___x_161_ = l_Lean_Environment_evalConst___redArg(v_env_159_, v_options_160_, v_constName_148_, v_checkMeta_149_);
lean_dec(v_constName_148_);
lean_dec_ref(v_env_159_);
v___x_162_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_161_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_164_; lean_object* v_env_165_; lean_object* v_options_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref_known(v___x_163_, 1);
v___x_164_ = lean_st_ref_get(v___y_153_);
v_env_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_env_165_);
lean_dec(v___x_164_);
v_options_166_ = lean_ctor_get(v___y_152_, 2);
v___x_167_ = l_Lean_Environment_evalConst___redArg(v_env_165_, v_options_166_, v_constName_148_, v_checkMeta_149_);
lean_dec(v_constName_148_);
lean_dec_ref(v_env_165_);
v___x_168_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_167_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_168_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_constName_148_);
v_a_169_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_163_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_163_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* v_constName_177_, lean_object* v_checkMeta_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v_checkMeta_boxed_184_; lean_object* v_res_185_; 
v_checkMeta_boxed_184_ = lean_unbox(v_checkMeta_178_);
v_res_185_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_177_, v_checkMeta_boxed_184_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_185_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v___x_186_, lean_object* v_as_187_, size_t v_i_188_, size_t v_stop_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_eq(v_i_188_, v_stop_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_array_uget_borrowed(v_as_187_, v_i_188_);
v___x_192_ = l_Lean_Environment_isImportedConst(v___x_186_, v___x_191_);
v___x_193_ = lean_bool_not(v___x_192_);
if (v___x_193_ == 0)
{
size_t v___x_194_; size_t v___x_195_; 
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_188_, v___x_194_);
v_i_188_ = v___x_195_;
goto _start;
}
else
{
return v___x_193_;
}
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v___x_198_, lean_object* v_as_199_, lean_object* v_i_200_, lean_object* v_stop_201_){
_start:
{
size_t v_i_boxed_202_; size_t v_stop_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_i_boxed_202_ = lean_unbox_usize(v_i_200_);
lean_dec(v_i_200_);
v_stop_boxed_203_ = lean_unbox_usize(v_stop_201_);
lean_dec(v_stop_201_);
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v___x_198_, v_as_199_, v_i_boxed_202_, v_stop_boxed_203_);
lean_dec_ref(v_as_199_);
lean_dec_ref(v___x_198_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_o_209_, lean_object* v_k_210_, uint8_t v_v_211_){
_start:
{
lean_object* v_map_212_; uint8_t v_hasTrace_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_227_; 
v_map_212_ = lean_ctor_get(v_o_209_, 0);
v_hasTrace_213_ = lean_ctor_get_uint8(v_o_209_, sizeof(void*)*1);
v_isSharedCheck_227_ = !lean_is_exclusive(v_o_209_);
if (v_isSharedCheck_227_ == 0)
{
v___x_215_ = v_o_209_;
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_map_212_);
lean_dec(v_o_209_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_217_, 0, v_v_211_);
lean_inc(v_k_210_);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_210_, v___x_217_, v_map_212_);
if (v_hasTrace_213_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_222_; 
v___x_219_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1));
v___x_220_ = l_Lean_Name_isPrefixOf(v___x_219_, v_k_210_);
lean_dec(v_k_210_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_218_);
v___x_222_ = v___x_215_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_218_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_220_);
return v___x_222_;
}
}
else
{
lean_object* v___x_225_; 
lean_dec(v_k_210_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_218_);
v___x_225_ = v___x_215_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_218_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*1, v_hasTrace_213_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object* v_o_228_, lean_object* v_k_229_, lean_object* v_v_230_){
_start:
{
uint8_t v_v_boxed_231_; lean_object* v_res_232_; 
v_v_boxed_231_ = lean_unbox(v_v_230_);
v_res_232_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_o_228_, v_k_229_, v_v_boxed_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_opts_233_, lean_object* v_opt_234_, uint8_t v_val_235_){
_start:
{
lean_object* v_name_236_; lean_object* v___x_237_; 
v_name_236_ = lean_ctor_get(v_opt_234_, 0);
lean_inc(v_name_236_);
lean_dec_ref(v_opt_234_);
v___x_237_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_opts_233_, v_name_236_, v_val_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* v_opts_238_, lean_object* v_opt_239_, lean_object* v_val_240_){
_start:
{
uint8_t v_val_boxed_241_; lean_object* v_res_242_; 
v_val_boxed_241_ = lean_unbox(v_val_240_);
v_res_242_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_opts_238_, v_opt_239_, v_val_boxed_241_);
return v_res_242_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_249_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
lean_ctor_set(v___x_249_, 2, v___x_248_);
lean_ctor_set(v___x_249_, 3, v___x_248_);
lean_ctor_set(v___x_249_, 4, v___x_248_);
lean_ctor_set(v___x_249_, 5, v___x_248_);
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
lean_object* v___y_278_; lean_object* v___y_279_; uint8_t v___y_280_; uint8_t v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; uint8_t v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_323_; uint8_t v___y_324_; uint8_t v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; uint8_t v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; uint8_t v___y_335_; uint8_t v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; uint8_t v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; uint8_t v___y_401_; lean_object* v___y_402_; uint8_t v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; uint8_t v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; uint8_t v___y_414_; uint8_t v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; uint8_t v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; uint8_t v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; uint8_t v___y_491_; uint8_t v___y_492_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v_nextMacroScope_652_; lean_object* v_ngen_653_; lean_object* v_auxDeclNGen_654_; lean_object* v_traceState_655_; lean_object* v_messages_656_; lean_object* v_infoState_657_; lean_object* v_snapshotTasks_658_; lean_object* v___y_659_; lean_object* v___x_678_; uint8_t v___y_680_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_678_ = lean_st_ref_get(v___y_275_);
lean_inc_ref(v_value_271_);
v___x_692_ = l_Lean_Expr_getUsedConstants(v_value_271_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_array_get_size(v___x_692_);
v___x_695_ = lean_nat_dec_lt(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; 
lean_dec_ref(v___x_692_);
lean_dec(v___x_678_);
v___x_696_ = lean_bool_not(v___x_695_);
v___y_680_ = v___x_696_;
goto v___jp_679_;
}
else
{
if (v___x_695_ == 0)
{
uint8_t v___x_697_; 
lean_dec_ref(v___x_692_);
lean_dec(v___x_678_);
v___x_697_ = lean_bool_not(v___x_695_);
v___y_680_ = v___x_697_;
goto v___jp_679_;
}
else
{
lean_object* v_env_698_; size_t v___x_699_; size_t v___x_700_; uint8_t v___x_701_; uint8_t v___x_702_; 
v_env_698_ = lean_ctor_get(v___x_678_, 0);
lean_inc_ref(v_env_698_);
lean_dec(v___x_678_);
v___x_699_ = ((size_t)0ULL);
v___x_700_ = lean_usize_of_nat(v___x_694_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_698_, v___x_692_, v___x_699_, v___x_700_);
lean_dec_ref(v___x_692_);
lean_dec_ref(v_env_698_);
v___x_702_ = lean_bool_not(v___x_701_);
v___y_680_ = v___x_702_;
goto v___jp_679_;
}
}
v___jp_277_:
{
lean_object* v_fileName_289_; lean_object* v_fileMap_290_; lean_object* v_currRecDepth_291_; lean_object* v_ref_292_; lean_object* v_currNamespace_293_; lean_object* v_openDecls_294_; lean_object* v_initHeartbeats_295_; lean_object* v_maxHeartbeats_296_; lean_object* v_quotContext_297_; lean_object* v_currMacroScope_298_; lean_object* v_cancelTk_x3f_299_; uint8_t v_suppressElabErrors_300_; lean_object* v_inheritedTraceOptions_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_319_; 
v_fileName_289_ = lean_ctor_get(v___y_287_, 0);
v_fileMap_290_ = lean_ctor_get(v___y_287_, 1);
v_currRecDepth_291_ = lean_ctor_get(v___y_287_, 3);
v_ref_292_ = lean_ctor_get(v___y_287_, 5);
v_currNamespace_293_ = lean_ctor_get(v___y_287_, 6);
v_openDecls_294_ = lean_ctor_get(v___y_287_, 7);
v_initHeartbeats_295_ = lean_ctor_get(v___y_287_, 8);
v_maxHeartbeats_296_ = lean_ctor_get(v___y_287_, 9);
v_quotContext_297_ = lean_ctor_get(v___y_287_, 10);
v_currMacroScope_298_ = lean_ctor_get(v___y_287_, 11);
v_cancelTk_x3f_299_ = lean_ctor_get(v___y_287_, 12);
v_suppressElabErrors_300_ = lean_ctor_get_uint8(v___y_287_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_301_ = lean_ctor_get(v___y_287_, 13);
v_isSharedCheck_319_ = !lean_is_exclusive(v___y_287_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_320_ = lean_ctor_get(v___y_287_, 4);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v___y_287_, 2);
lean_dec(v_unused_321_);
v___x_303_ = v___y_287_;
v_isShared_304_ = v_isSharedCheck_319_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_inheritedTraceOptions_301_);
lean_inc(v_cancelTk_x3f_299_);
lean_inc(v_currMacroScope_298_);
lean_inc(v_quotContext_297_);
lean_inc(v_maxHeartbeats_296_);
lean_inc(v_initHeartbeats_295_);
lean_inc(v_openDecls_294_);
lean_inc(v_currNamespace_293_);
lean_inc(v_ref_292_);
lean_inc(v_currRecDepth_291_);
lean_inc(v_fileMap_290_);
lean_inc(v_fileName_289_);
lean_dec(v___y_287_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_319_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_286_, v___y_278_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 4, v___x_305_);
lean_ctor_set(v___x_303_, 2, v___y_286_);
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_fileName_289_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_fileMap_290_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v___y_286_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_currRecDepth_291_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_318_, 5, v_ref_292_);
lean_ctor_set(v_reuseFailAlloc_318_, 6, v_currNamespace_293_);
lean_ctor_set(v_reuseFailAlloc_318_, 7, v_openDecls_294_);
lean_ctor_set(v_reuseFailAlloc_318_, 8, v_initHeartbeats_295_);
lean_ctor_set(v_reuseFailAlloc_318_, 9, v_maxHeartbeats_296_);
lean_ctor_set(v_reuseFailAlloc_318_, 10, v_quotContext_297_);
lean_ctor_set(v_reuseFailAlloc_318_, 11, v_currMacroScope_298_);
lean_ctor_set(v_reuseFailAlloc_318_, 12, v_cancelTk_x3f_299_);
lean_ctor_set(v_reuseFailAlloc_318_, 13, v_inheritedTraceOptions_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*14 + 1, v_suppressElabErrors_300_);
v___x_307_ = v_reuseFailAlloc_318_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*14, v___y_281_);
v___x_308_ = l_Lean_addAndCompile(v___y_285_, v___y_280_, v___y_284_, v___x_307_, v___y_288_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_309_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_282_, v_checkMeta_268_, v___y_279_, v___y_283_, v___x_307_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___x_307_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_279_);
return v___x_309_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v___x_307_);
lean_dec(v___y_288_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_279_);
v_a_310_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_308_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
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
}
v___jp_322_:
{
uint8_t v___x_336_; 
v___x_336_ = lean_bool_not(v___y_335_);
if (v___x_336_ == 0)
{
v___y_278_ = v___y_323_;
v___y_279_ = v___y_327_;
v___y_280_ = v___y_328_;
v___y_281_ = v___y_324_;
v___y_282_ = v___y_329_;
v___y_283_ = v___y_331_;
v___y_284_ = v___y_325_;
v___y_285_ = v___y_332_;
v___y_286_ = v___y_333_;
v___y_287_ = v___y_334_;
v___y_288_ = v___y_330_;
goto v___jp_277_;
}
else
{
lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_traceState_342_; lean_object* v_messages_343_; lean_object* v_infoState_344_; lean_object* v_snapshotTasks_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_354_; 
v___x_337_ = lean_st_ref_take(v___y_330_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_337_, 1);
v_ngen_340_ = lean_ctor_get(v___x_337_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_337_, 3);
v_traceState_342_ = lean_ctor_get(v___x_337_, 4);
v_messages_343_ = lean_ctor_get(v___x_337_, 6);
v_infoState_344_ = lean_ctor_get(v___x_337_, 7);
v_snapshotTasks_345_ = lean_ctor_get(v___x_337_, 8);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_337_, 5);
lean_dec(v_unused_355_);
v___x_347_ = v___x_337_;
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snapshotTasks_345_);
lean_inc(v_infoState_344_);
lean_inc(v_messages_343_);
lean_inc(v_traceState_342_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_337_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = l_Lean_Kernel_enableDiag(v_env_338_, v___y_324_);
lean_inc_ref(v___y_326_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 5, v___y_326_);
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_traceState_342_);
lean_ctor_set(v_reuseFailAlloc_353_, 5, v___y_326_);
lean_ctor_set(v_reuseFailAlloc_353_, 6, v_messages_343_);
lean_ctor_set(v_reuseFailAlloc_353_, 7, v_infoState_344_);
lean_ctor_set(v_reuseFailAlloc_353_, 8, v_snapshotTasks_345_);
v___x_351_ = v_reuseFailAlloc_353_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; 
v___x_352_ = lean_st_ref_set(v___y_330_, v___x_351_);
v___y_278_ = v___y_323_;
v___y_279_ = v___y_327_;
v___y_280_ = v___y_328_;
v___y_281_ = v___y_324_;
v___y_282_ = v___y_329_;
v___y_283_ = v___y_331_;
v___y_284_ = v___y_325_;
v___y_285_ = v___y_332_;
v___y_286_ = v___y_333_;
v___y_287_ = v___y_334_;
v___y_288_ = v___y_330_;
goto v___jp_277_;
}
}
}
}
v___jp_356_:
{
lean_object* v___x_370_; lean_object* v_fileName_371_; lean_object* v_fileMap_372_; lean_object* v_currRecDepth_373_; lean_object* v_ref_374_; lean_object* v_currNamespace_375_; lean_object* v_openDecls_376_; lean_object* v_initHeartbeats_377_; lean_object* v_maxHeartbeats_378_; lean_object* v_quotContext_379_; lean_object* v_currMacroScope_380_; lean_object* v_cancelTk_x3f_381_; uint8_t v_suppressElabErrors_382_; lean_object* v_inheritedTraceOptions_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_397_; 
v___x_370_ = lean_st_ref_get(v___y_369_);
v_fileName_371_ = lean_ctor_get(v___y_368_, 0);
v_fileMap_372_ = lean_ctor_get(v___y_368_, 1);
v_currRecDepth_373_ = lean_ctor_get(v___y_368_, 3);
v_ref_374_ = lean_ctor_get(v___y_368_, 5);
v_currNamespace_375_ = lean_ctor_get(v___y_368_, 6);
v_openDecls_376_ = lean_ctor_get(v___y_368_, 7);
v_initHeartbeats_377_ = lean_ctor_get(v___y_368_, 8);
v_maxHeartbeats_378_ = lean_ctor_get(v___y_368_, 9);
v_quotContext_379_ = lean_ctor_get(v___y_368_, 10);
v_currMacroScope_380_ = lean_ctor_get(v___y_368_, 11);
v_cancelTk_x3f_381_ = lean_ctor_get(v___y_368_, 12);
v_suppressElabErrors_382_ = lean_ctor_get_uint8(v___y_368_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_383_ = lean_ctor_get(v___y_368_, 13);
v_isSharedCheck_397_ = !lean_is_exclusive(v___y_368_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_398_ = lean_ctor_get(v___y_368_, 4);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v___y_368_, 2);
lean_dec(v_unused_399_);
v___x_385_ = v___y_368_;
v_isShared_386_ = v_isSharedCheck_397_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_inheritedTraceOptions_383_);
lean_inc(v_cancelTk_x3f_381_);
lean_inc(v_currMacroScope_380_);
lean_inc(v_quotContext_379_);
lean_inc(v_maxHeartbeats_378_);
lean_inc(v_initHeartbeats_377_);
lean_inc(v_openDecls_376_);
lean_inc(v_currNamespace_375_);
lean_inc(v_ref_374_);
lean_inc(v_currRecDepth_373_);
lean_inc(v_fileMap_372_);
lean_inc(v_fileName_371_);
lean_dec(v___y_368_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_397_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_env_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v_env_387_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_370_);
v___x_388_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_367_, v___y_358_);
lean_inc_ref(v___y_367_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 4, v___x_388_);
lean_ctor_set(v___x_385_, 2, v___y_367_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_fileName_371_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_fileMap_372_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v___y_367_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_currRecDepth_373_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v_ref_374_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_currNamespace_375_);
lean_ctor_set(v_reuseFailAlloc_396_, 7, v_openDecls_376_);
lean_ctor_set(v_reuseFailAlloc_396_, 8, v_initHeartbeats_377_);
lean_ctor_set(v_reuseFailAlloc_396_, 9, v_maxHeartbeats_378_);
lean_ctor_set(v_reuseFailAlloc_396_, 10, v_quotContext_379_);
lean_ctor_set(v_reuseFailAlloc_396_, 11, v_currMacroScope_380_);
lean_ctor_set(v_reuseFailAlloc_396_, 12, v_cancelTk_x3f_381_);
lean_ctor_set(v_reuseFailAlloc_396_, 13, v_inheritedTraceOptions_383_);
lean_ctor_set_uint8(v_reuseFailAlloc_396_, sizeof(void*)*14 + 1, v_suppressElabErrors_382_);
v___x_390_ = v_reuseFailAlloc_396_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; uint8_t v___x_394_; 
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*14, v___y_357_);
v___x_391_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_392_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_367_, v___x_391_, v___y_361_);
v___x_393_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_392_, v___y_360_);
v___x_394_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_387_);
lean_dec_ref(v_env_387_);
if (v___x_394_ == 0)
{
if (v___x_393_ == 0)
{
uint8_t v___x_395_; 
v___x_395_ = 1;
v___y_323_ = v___y_358_;
v___y_324_ = v___x_393_;
v___y_325_ = v___y_364_;
v___y_326_ = v___y_366_;
v___y_327_ = v___y_359_;
v___y_328_ = v___y_361_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_369_;
v___y_331_ = v___y_363_;
v___y_332_ = v___y_365_;
v___y_333_ = v___x_392_;
v___y_334_ = v___x_390_;
v___y_335_ = v___x_395_;
goto v___jp_322_;
}
else
{
v___y_323_ = v___y_358_;
v___y_324_ = v___x_393_;
v___y_325_ = v___y_364_;
v___y_326_ = v___y_366_;
v___y_327_ = v___y_359_;
v___y_328_ = v___y_361_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_369_;
v___y_331_ = v___y_363_;
v___y_332_ = v___y_365_;
v___y_333_ = v___x_392_;
v___y_334_ = v___x_390_;
v___y_335_ = v___x_394_;
goto v___jp_322_;
}
}
else
{
v___y_323_ = v___y_358_;
v___y_324_ = v___x_393_;
v___y_325_ = v___y_364_;
v___y_326_ = v___y_366_;
v___y_327_ = v___y_359_;
v___y_328_ = v___y_361_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_369_;
v___y_331_ = v___y_363_;
v___y_332_ = v___y_365_;
v___y_333_ = v___x_392_;
v___y_334_ = v___x_390_;
v___y_335_ = v___x_393_;
goto v___jp_322_;
}
}
}
}
v___jp_400_:
{
uint8_t v___x_415_; 
v___x_415_ = lean_bool_not(v___y_414_);
if (v___x_415_ == 0)
{
v___y_357_ = v___y_401_;
v___y_358_ = v___y_402_;
v___y_359_ = v___y_406_;
v___y_360_ = v___y_407_;
v___y_361_ = v___y_408_;
v___y_362_ = v___y_410_;
v___y_363_ = v___y_411_;
v___y_364_ = v___y_403_;
v___y_365_ = v___y_412_;
v___y_366_ = v___y_404_;
v___y_367_ = v___y_405_;
v___y_368_ = v___y_409_;
v___y_369_ = v___y_413_;
goto v___jp_356_;
}
else
{
lean_object* v___x_416_; lean_object* v_env_417_; lean_object* v_nextMacroScope_418_; lean_object* v_ngen_419_; lean_object* v_auxDeclNGen_420_; lean_object* v_traceState_421_; lean_object* v_messages_422_; lean_object* v_infoState_423_; lean_object* v_snapshotTasks_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v___x_416_ = lean_st_ref_take(v___y_413_);
v_env_417_ = lean_ctor_get(v___x_416_, 0);
v_nextMacroScope_418_ = lean_ctor_get(v___x_416_, 1);
v_ngen_419_ = lean_ctor_get(v___x_416_, 2);
v_auxDeclNGen_420_ = lean_ctor_get(v___x_416_, 3);
v_traceState_421_ = lean_ctor_get(v___x_416_, 4);
v_messages_422_ = lean_ctor_get(v___x_416_, 6);
v_infoState_423_ = lean_ctor_get(v___x_416_, 7);
v_snapshotTasks_424_ = lean_ctor_get(v___x_416_, 8);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v___x_416_, 5);
lean_dec(v_unused_434_);
v___x_426_ = v___x_416_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snapshotTasks_424_);
lean_inc(v_infoState_423_);
lean_inc(v_messages_422_);
lean_inc(v_traceState_421_);
lean_inc(v_auxDeclNGen_420_);
lean_inc(v_ngen_419_);
lean_inc(v_nextMacroScope_418_);
lean_inc(v_env_417_);
lean_dec(v___x_416_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_Kernel_enableDiag(v_env_417_, v___y_401_);
lean_inc_ref(v___y_404_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 5, v___y_404_);
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_nextMacroScope_418_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_ngen_419_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_auxDeclNGen_420_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_traceState_421_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v___y_404_);
lean_ctor_set(v_reuseFailAlloc_432_, 6, v_messages_422_);
lean_ctor_set(v_reuseFailAlloc_432_, 7, v_infoState_423_);
lean_ctor_set(v_reuseFailAlloc_432_, 8, v_snapshotTasks_424_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; 
v___x_431_ = lean_st_ref_set(v___y_413_, v___x_430_);
v___y_357_ = v___y_401_;
v___y_358_ = v___y_402_;
v___y_359_ = v___y_406_;
v___y_360_ = v___y_407_;
v___y_361_ = v___y_408_;
v___y_362_ = v___y_410_;
v___y_363_ = v___y_411_;
v___y_364_ = v___y_403_;
v___y_365_ = v___y_412_;
v___y_366_ = v___y_404_;
v___y_367_ = v___y_405_;
v___y_368_ = v___y_409_;
v___y_369_ = v___y_413_;
goto v___jp_356_;
}
}
}
}
v___jp_435_:
{
lean_object* v___x_448_; lean_object* v_fileName_449_; lean_object* v_fileMap_450_; lean_object* v_currRecDepth_451_; lean_object* v_ref_452_; lean_object* v_currNamespace_453_; lean_object* v_openDecls_454_; lean_object* v_initHeartbeats_455_; lean_object* v_maxHeartbeats_456_; lean_object* v_quotContext_457_; lean_object* v_currMacroScope_458_; lean_object* v_cancelTk_x3f_459_; uint8_t v_suppressElabErrors_460_; lean_object* v_inheritedTraceOptions_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_476_; 
v___x_448_ = lean_st_ref_get(v___y_447_);
v_fileName_449_ = lean_ctor_get(v___y_446_, 0);
v_fileMap_450_ = lean_ctor_get(v___y_446_, 1);
v_currRecDepth_451_ = lean_ctor_get(v___y_446_, 3);
v_ref_452_ = lean_ctor_get(v___y_446_, 5);
v_currNamespace_453_ = lean_ctor_get(v___y_446_, 6);
v_openDecls_454_ = lean_ctor_get(v___y_446_, 7);
v_initHeartbeats_455_ = lean_ctor_get(v___y_446_, 8);
v_maxHeartbeats_456_ = lean_ctor_get(v___y_446_, 9);
v_quotContext_457_ = lean_ctor_get(v___y_446_, 10);
v_currMacroScope_458_ = lean_ctor_get(v___y_446_, 11);
v_cancelTk_x3f_459_ = lean_ctor_get(v___y_446_, 12);
v_suppressElabErrors_460_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_461_ = lean_ctor_get(v___y_446_, 13);
v_isSharedCheck_476_ = !lean_is_exclusive(v___y_446_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_477_ = lean_ctor_get(v___y_446_, 4);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v___y_446_, 2);
lean_dec(v_unused_478_);
v___x_463_ = v___y_446_;
v_isShared_464_ = v_isSharedCheck_476_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_inheritedTraceOptions_461_);
lean_inc(v_cancelTk_x3f_459_);
lean_inc(v_currMacroScope_458_);
lean_inc(v_quotContext_457_);
lean_inc(v_maxHeartbeats_456_);
lean_inc(v_initHeartbeats_455_);
lean_inc(v_openDecls_454_);
lean_inc(v_currNamespace_453_);
lean_inc(v_ref_452_);
lean_inc(v_currRecDepth_451_);
lean_inc(v_fileMap_450_);
lean_inc(v_fileName_449_);
lean_dec(v___y_446_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_476_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_env_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v_env_465_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_env_465_);
lean_dec(v___x_448_);
v___x_466_ = l_Lean_maxRecDepth;
v___x_467_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_440_, v___x_466_);
lean_inc_ref(v___y_440_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 4, v___x_467_);
lean_ctor_set(v___x_463_, 2, v___y_440_);
v___x_469_ = v___x_463_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_fileName_449_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_fileMap_450_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v___y_440_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_currRecDepth_451_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_ref_452_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v_currNamespace_453_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_openDecls_454_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v_initHeartbeats_455_);
lean_ctor_set(v_reuseFailAlloc_475_, 9, v_maxHeartbeats_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 10, v_quotContext_457_);
lean_ctor_set(v_reuseFailAlloc_475_, 11, v_currMacroScope_458_);
lean_ctor_set(v_reuseFailAlloc_475_, 12, v_cancelTk_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_475_, 13, v_inheritedTraceOptions_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_475_, sizeof(void*)*14 + 1, v_suppressElabErrors_460_);
v___x_469_ = v_reuseFailAlloc_475_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; uint8_t v___x_473_; 
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*14, v___y_445_);
v___x_470_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_471_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_440_, v___x_470_, v___y_442_);
v___x_472_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_471_, v___y_438_);
v___x_473_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_465_);
lean_dec_ref(v_env_465_);
if (v___x_473_ == 0)
{
if (v___x_472_ == 0)
{
uint8_t v___x_474_; 
v___x_474_ = 1;
v___y_401_ = v___x_472_;
v___y_402_ = v___x_466_;
v___y_403_ = v___y_442_;
v___y_404_ = v___y_444_;
v___y_405_ = v___x_471_;
v___y_406_ = v___y_437_;
v___y_407_ = v___y_438_;
v___y_408_ = v___y_436_;
v___y_409_ = v___x_469_;
v___y_410_ = v___y_439_;
v___y_411_ = v___y_441_;
v___y_412_ = v___y_443_;
v___y_413_ = v___y_447_;
v___y_414_ = v___x_474_;
goto v___jp_400_;
}
else
{
v___y_401_ = v___x_472_;
v___y_402_ = v___x_466_;
v___y_403_ = v___y_442_;
v___y_404_ = v___y_444_;
v___y_405_ = v___x_471_;
v___y_406_ = v___y_437_;
v___y_407_ = v___y_438_;
v___y_408_ = v___y_436_;
v___y_409_ = v___x_469_;
v___y_410_ = v___y_439_;
v___y_411_ = v___y_441_;
v___y_412_ = v___y_443_;
v___y_413_ = v___y_447_;
v___y_414_ = v___x_473_;
goto v___jp_400_;
}
}
else
{
v___y_401_ = v___x_472_;
v___y_402_ = v___x_466_;
v___y_403_ = v___y_442_;
v___y_404_ = v___y_444_;
v___y_405_ = v___x_471_;
v___y_406_ = v___y_437_;
v___y_407_ = v___y_438_;
v___y_408_ = v___y_436_;
v___y_409_ = v___x_469_;
v___y_410_ = v___y_439_;
v___y_411_ = v___y_441_;
v___y_412_ = v___y_443_;
v___y_413_ = v___y_447_;
v___y_414_ = v___x_472_;
goto v___jp_400_;
}
}
}
}
v___jp_479_:
{
uint8_t v___x_493_; 
v___x_493_ = lean_bool_not(v___y_492_);
if (v___x_493_ == 0)
{
v___y_436_ = v___y_485_;
v___y_437_ = v___y_486_;
v___y_438_ = v___y_487_;
v___y_439_ = v___y_488_;
v___y_440_ = v___y_481_;
v___y_441_ = v___y_489_;
v___y_442_ = v___y_482_;
v___y_443_ = v___y_490_;
v___y_444_ = v___y_483_;
v___y_445_ = v___y_491_;
v___y_446_ = v___y_484_;
v___y_447_ = v___y_480_;
goto v___jp_435_;
}
else
{
lean_object* v___x_494_; lean_object* v_env_495_; lean_object* v_nextMacroScope_496_; lean_object* v_ngen_497_; lean_object* v_auxDeclNGen_498_; lean_object* v_traceState_499_; lean_object* v_messages_500_; lean_object* v_infoState_501_; lean_object* v_snapshotTasks_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_511_; 
v___x_494_ = lean_st_ref_take(v___y_480_);
v_env_495_ = lean_ctor_get(v___x_494_, 0);
v_nextMacroScope_496_ = lean_ctor_get(v___x_494_, 1);
v_ngen_497_ = lean_ctor_get(v___x_494_, 2);
v_auxDeclNGen_498_ = lean_ctor_get(v___x_494_, 3);
v_traceState_499_ = lean_ctor_get(v___x_494_, 4);
v_messages_500_ = lean_ctor_get(v___x_494_, 6);
v_infoState_501_ = lean_ctor_get(v___x_494_, 7);
v_snapshotTasks_502_ = lean_ctor_get(v___x_494_, 8);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v___x_494_, 5);
lean_dec(v_unused_512_);
v___x_504_ = v___x_494_;
v_isShared_505_ = v_isSharedCheck_511_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snapshotTasks_502_);
lean_inc(v_infoState_501_);
lean_inc(v_messages_500_);
lean_inc(v_traceState_499_);
lean_inc(v_auxDeclNGen_498_);
lean_inc(v_ngen_497_);
lean_inc(v_nextMacroScope_496_);
lean_inc(v_env_495_);
lean_dec(v___x_494_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_511_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = l_Lean_Kernel_enableDiag(v_env_495_, v___y_491_);
lean_inc_ref(v___y_483_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 5, v___y_483_);
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_nextMacroScope_496_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_ngen_497_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_auxDeclNGen_498_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_traceState_499_);
lean_ctor_set(v_reuseFailAlloc_510_, 5, v___y_483_);
lean_ctor_set(v_reuseFailAlloc_510_, 6, v_messages_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 7, v_infoState_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 8, v_snapshotTasks_502_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_st_ref_set(v___y_480_, v___x_508_);
v___y_436_ = v___y_485_;
v___y_437_ = v___y_486_;
v___y_438_ = v___y_487_;
v___y_439_ = v___y_488_;
v___y_440_ = v___y_481_;
v___y_441_ = v___y_489_;
v___y_442_ = v___y_482_;
v___y_443_ = v___y_490_;
v___y_444_ = v___y_483_;
v___y_445_ = v___y_491_;
v___y_446_ = v___y_484_;
v___y_447_ = v___y_480_;
goto v___jp_435_;
}
}
}
}
v___jp_513_:
{
lean_object* v___x_522_; 
lean_inc(v___y_521_);
lean_inc_ref(v___y_520_);
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc_ref(v___y_516_);
v___x_522_ = lean_infer_type(v___y_516_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc_n(v_a_523_, 2);
lean_dec_ref_known(v___x_522_, 1);
lean_inc(v___y_521_);
lean_inc_ref(v___y_520_);
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
v___x_524_ = lean_apply_6(v_checkType_269_, v_a_523_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, lean_box(0));
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v___x_525_; lean_object* v_env_526_; lean_object* v_nextMacroScope_527_; lean_object* v_ngen_528_; lean_object* v_auxDeclNGen_529_; lean_object* v_traceState_530_; lean_object* v_messages_531_; lean_object* v_infoState_532_; lean_object* v_snapshotTasks_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref_known(v___x_524_, 1);
v___x_525_ = lean_st_ref_take(v___y_521_);
v_env_526_ = lean_ctor_get(v___x_525_, 0);
v_nextMacroScope_527_ = lean_ctor_get(v___x_525_, 1);
v_ngen_528_ = lean_ctor_get(v___x_525_, 2);
v_auxDeclNGen_529_ = lean_ctor_get(v___x_525_, 3);
v_traceState_530_ = lean_ctor_get(v___x_525_, 4);
v_messages_531_ = lean_ctor_get(v___x_525_, 6);
v_infoState_532_ = lean_ctor_get(v___x_525_, 7);
v_snapshotTasks_533_ = lean_ctor_get(v___x_525_, 8);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_525_, 5);
lean_dec(v_unused_588_);
v___x_535_ = v___x_525_;
v_isShared_536_ = v_isSharedCheck_587_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_snapshotTasks_533_);
lean_inc(v_infoState_532_);
lean_inc(v_messages_531_);
lean_inc(v_traceState_530_);
lean_inc(v_auxDeclNGen_529_);
lean_inc(v_ngen_528_);
lean_inc(v_nextMacroScope_527_);
lean_inc(v_env_526_);
lean_dec(v___x_525_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_587_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_537_ = lean_array_to_list(v___y_517_);
lean_inc_n(v___y_514_, 3);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v___y_514_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_ctor_set(v___x_538_, 2, v_a_523_);
lean_inc(v___y_515_);
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v___y_514_);
lean_ctor_set(v___x_539_, 1, v___y_515_);
v___x_540_ = l_Lean_markMeta(v_env_526_, v___y_514_);
v___x_541_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 5, v___x_541_);
lean_ctor_set(v___x_535_, 0, v___x_540_);
v___x_543_ = v___x_535_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_nextMacroScope_527_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_ngen_528_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_auxDeclNGen_529_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_traceState_530_);
lean_ctor_set(v_reuseFailAlloc_586_, 5, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_586_, 6, v_messages_531_);
lean_ctor_set(v_reuseFailAlloc_586_, 7, v_infoState_532_);
lean_ctor_set(v_reuseFailAlloc_586_, 8, v_snapshotTasks_533_);
v___x_543_ = v_reuseFailAlloc_586_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_mctx_546_; lean_object* v_zetaDeltaFVarIds_547_; lean_object* v_postponed_548_; lean_object* v_diag_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_584_; 
v___x_544_ = lean_st_ref_set(v___y_521_, v___x_543_);
v___x_545_ = lean_st_ref_take(v___y_519_);
v_mctx_546_ = lean_ctor_get(v___x_545_, 0);
v_zetaDeltaFVarIds_547_ = lean_ctor_get(v___x_545_, 2);
v_postponed_548_ = lean_ctor_get(v___x_545_, 3);
v_diag_549_ = lean_ctor_get(v___x_545_, 4);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_545_, 1);
lean_dec(v_unused_585_);
v___x_551_ = v___x_545_;
v_isShared_552_ = v_isSharedCheck_584_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_diag_549_);
lean_inc(v_postponed_548_);
lean_inc(v_zetaDeltaFVarIds_547_);
lean_inc(v_mctx_546_);
lean_dec(v___x_545_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_584_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_mctx_546_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_zetaDeltaFVarIds_547_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_postponed_548_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_diag_549_);
v___x_555_ = v_reuseFailAlloc_583_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_env_558_; lean_object* v_checked_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_556_ = lean_st_ref_set(v___y_519_, v___x_555_);
v___x_557_ = lean_st_ref_get(v___y_521_);
v_env_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc_ref(v_env_558_);
lean_dec(v___x_557_);
v_checked_559_ = lean_ctor_get(v_env_558_, 2);
lean_inc_ref(v_checked_559_);
lean_dec_ref(v_env_558_);
v___x_560_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_561_ = l_Lean_traceBlock___redArg(v___x_560_, v_checked_559_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; lean_object* v_options_563_; lean_object* v_env_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; 
lean_dec_ref_known(v___x_561_, 1);
v___x_562_ = lean_st_ref_get(v___y_521_);
v_options_563_ = lean_ctor_get(v___y_520_, 2);
v_env_564_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_564_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_566_, 0, v___x_538_);
lean_ctor_set(v___x_566_, 1, v___y_516_);
lean_ctor_set(v___x_566_, 2, v___x_565_);
lean_ctor_set(v___x_566_, 3, v___x_539_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*4, v_safety_270_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = 1;
v___x_569_ = 0;
v___x_570_ = l_Lean_Elab_async;
lean_inc_ref(v_options_563_);
v___x_571_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_563_, v___x_570_, v___x_569_);
v___x_572_ = l_Lean_diagnostics;
v___x_573_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_571_, v___x_572_);
v___x_574_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_564_);
lean_dec_ref(v_env_564_);
if (v___x_574_ == 0)
{
if (v___x_573_ == 0)
{
v___y_480_ = v___y_521_;
v___y_481_ = v___x_571_;
v___y_482_ = v___x_569_;
v___y_483_ = v___x_541_;
v___y_484_ = v___y_520_;
v___y_485_ = v___x_568_;
v___y_486_ = v___y_518_;
v___y_487_ = v___x_572_;
v___y_488_ = v___y_514_;
v___y_489_ = v___y_519_;
v___y_490_ = v___x_567_;
v___y_491_ = v___x_573_;
v___y_492_ = v___x_568_;
goto v___jp_479_;
}
else
{
v___y_480_ = v___y_521_;
v___y_481_ = v___x_571_;
v___y_482_ = v___x_569_;
v___y_483_ = v___x_541_;
v___y_484_ = v___y_520_;
v___y_485_ = v___x_568_;
v___y_486_ = v___y_518_;
v___y_487_ = v___x_572_;
v___y_488_ = v___y_514_;
v___y_489_ = v___y_519_;
v___y_490_ = v___x_567_;
v___y_491_ = v___x_573_;
v___y_492_ = v___x_574_;
goto v___jp_479_;
}
}
else
{
v___y_480_ = v___y_521_;
v___y_481_ = v___x_571_;
v___y_482_ = v___x_569_;
v___y_483_ = v___x_541_;
v___y_484_ = v___y_520_;
v___y_485_ = v___x_568_;
v___y_486_ = v___y_518_;
v___y_487_ = v___x_572_;
v___y_488_ = v___y_514_;
v___y_489_ = v___y_519_;
v___y_490_ = v___x_567_;
v___y_491_ = v___x_573_;
v___y_492_ = v___x_573_;
goto v___jp_479_;
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref_known(v___x_539_, 2);
lean_dec_ref_known(v___x_538_, 3);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_514_);
v_a_575_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_561_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_561_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
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
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_a_523_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_514_);
v_a_589_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_524_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_524_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_514_);
lean_dec_ref(v_checkType_269_);
v_a_597_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_522_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_522_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
v___jp_605_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_st_ref_get(v___y_609_);
v___x_611_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_612_ = l_Lean_Core_mkFreshUserName(v___x_611_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_271_, v___y_607_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_env_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_params_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_n(v_a_615_, 2);
lean_dec_ref_known(v___x_614_, 1);
v_env_616_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_616_);
lean_dec(v___x_610_);
v___x_617_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_618_ = l_Lean_collectLevelParams(v___x_617_, v_a_615_);
v_params_619_ = lean_ctor_get(v___x_618_, 2);
lean_inc_ref(v_params_619_);
lean_dec_ref(v___x_618_);
v___x_620_ = l_Lean_mkPrivateName(v_env_616_, v_a_613_);
lean_dec_ref(v_env_616_);
v___x_621_ = lean_box(0);
v___x_622_ = l_Lean_Expr_hasMVar(v_a_615_);
if (v___x_622_ == 0)
{
v___y_514_ = v___x_620_;
v___y_515_ = v___x_621_;
v___y_516_ = v_a_615_;
v___y_517_ = v_params_619_;
v___y_518_ = v___y_606_;
v___y_519_ = v___y_607_;
v___y_520_ = v___y_608_;
v___y_521_ = v___y_609_;
goto v___jp_513_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_615_);
v___x_624_ = l_Lean_indentExpr(v_a_615_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_625_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec_ref_known(v___x_626_, 1);
v___y_514_ = v___x_620_;
v___y_515_ = v___x_621_;
v___y_516_ = v_a_615_;
v___y_517_ = v_params_619_;
v___y_518_ = v___y_606_;
v___y_519_ = v___y_607_;
v___y_520_ = v___y_608_;
v___y_521_ = v___y_609_;
goto v___jp_513_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v___x_620_);
lean_dec_ref(v_params_619_);
lean_dec(v_a_615_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v_checkType_269_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_613_);
lean_dec(v___x_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v_checkType_269_);
v_a_635_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_614_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_614_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v___x_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v_value_271_);
lean_dec_ref(v_checkType_269_);
v_a_643_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_612_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_612_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
v___jp_651_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_mctx_664_; lean_object* v_zetaDeltaFVarIds_665_; lean_object* v_postponed_666_; lean_object* v_diag_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_676_; 
v___x_660_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_661_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_661_, 0, v___y_659_);
lean_ctor_set(v___x_661_, 1, v_nextMacroScope_652_);
lean_ctor_set(v___x_661_, 2, v_ngen_653_);
lean_ctor_set(v___x_661_, 3, v_auxDeclNGen_654_);
lean_ctor_set(v___x_661_, 4, v_traceState_655_);
lean_ctor_set(v___x_661_, 5, v___x_660_);
lean_ctor_set(v___x_661_, 6, v_messages_656_);
lean_ctor_set(v___x_661_, 7, v_infoState_657_);
lean_ctor_set(v___x_661_, 8, v_snapshotTasks_658_);
v___x_662_ = lean_st_ref_set(v___y_275_, v___x_661_);
v___x_663_ = lean_st_ref_take(v___y_273_);
v_mctx_664_ = lean_ctor_get(v___x_663_, 0);
v_zetaDeltaFVarIds_665_ = lean_ctor_get(v___x_663_, 2);
v_postponed_666_ = lean_ctor_get(v___x_663_, 3);
v_diag_667_ = lean_ctor_get(v___x_663_, 4);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_663_, 1);
lean_dec(v_unused_677_);
v___x_669_ = v___x_663_;
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_diag_667_);
lean_inc(v_postponed_666_);
lean_inc(v_zetaDeltaFVarIds_665_);
lean_inc(v_mctx_664_);
lean_dec(v___x_663_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_mctx_664_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_zetaDeltaFVarIds_665_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_postponed_666_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_diag_667_);
v___x_673_ = v_reuseFailAlloc_675_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; 
v___x_674_ = lean_st_ref_set(v___y_273_, v___x_673_);
v___y_606_ = v___y_272_;
v___y_607_ = v___y_273_;
v___y_608_ = v___y_274_;
v___y_609_ = v___y_275_;
goto v___jp_605_;
}
}
}
v___jp_679_:
{
if (v___y_680_ == 0)
{
v___y_606_ = v___y_272_;
v___y_607_ = v___y_273_;
v___y_608_ = v___y_274_;
v___y_609_ = v___y_275_;
goto v___jp_605_;
}
else
{
lean_object* v___x_681_; lean_object* v_env_682_; lean_object* v_nextMacroScope_683_; lean_object* v_ngen_684_; lean_object* v_auxDeclNGen_685_; lean_object* v_traceState_686_; lean_object* v_messages_687_; lean_object* v_infoState_688_; lean_object* v_snapshotTasks_689_; lean_object* v___x_690_; 
v___x_681_ = lean_st_ref_take(v___y_275_);
v_env_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref_n(v_env_682_, 2);
v_nextMacroScope_683_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_nextMacroScope_683_);
v_ngen_684_ = lean_ctor_get(v___x_681_, 2);
lean_inc_ref(v_ngen_684_);
v_auxDeclNGen_685_ = lean_ctor_get(v___x_681_, 3);
lean_inc_ref(v_auxDeclNGen_685_);
v_traceState_686_ = lean_ctor_get(v___x_681_, 4);
lean_inc_ref(v_traceState_686_);
v_messages_687_ = lean_ctor_get(v___x_681_, 6);
lean_inc_ref(v_messages_687_);
v_infoState_688_ = lean_ctor_get(v___x_681_, 7);
lean_inc_ref(v_infoState_688_);
v_snapshotTasks_689_ = lean_ctor_get(v___x_681_, 8);
lean_inc_ref(v_snapshotTasks_689_);
lean_dec(v___x_681_);
v___x_690_ = l_Lean_Environment_importEnv_x3f(v_env_682_);
if (lean_obj_tag(v___x_690_) == 0)
{
v_nextMacroScope_652_ = v_nextMacroScope_683_;
v_ngen_653_ = v_ngen_684_;
v_auxDeclNGen_654_ = v_auxDeclNGen_685_;
v_traceState_655_ = v_traceState_686_;
v_messages_656_ = v_messages_687_;
v_infoState_657_ = v_infoState_688_;
v_snapshotTasks_658_ = v_snapshotTasks_689_;
v___y_659_ = v_env_682_;
goto v___jp_651_;
}
else
{
lean_object* v_val_691_; 
lean_dec_ref(v_env_682_);
v_val_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v___x_690_, 1);
v_nextMacroScope_652_ = v_nextMacroScope_683_;
v_ngen_653_ = v_ngen_684_;
v_auxDeclNGen_654_ = v_auxDeclNGen_685_;
v_traceState_655_ = v_traceState_686_;
v_messages_656_ = v_messages_687_;
v_infoState_657_ = v_infoState_688_;
v_snapshotTasks_658_ = v_snapshotTasks_689_;
v___y_659_ = v_val_691_;
goto v___jp_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_703_, lean_object* v_checkType_704_, lean_object* v_safety_705_, lean_object* v_value_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
uint8_t v_checkMeta_boxed_712_; uint8_t v_safety_boxed_713_; lean_object* v_res_714_; 
v_checkMeta_boxed_712_ = lean_unbox(v_checkMeta_703_);
v_safety_boxed_713_ = lean_unbox(v_safety_705_);
v_res_714_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_712_, v_checkType_704_, v_safety_boxed_713_, v_value_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_nextMacroScope_720_; lean_object* v_ngen_721_; lean_object* v_auxDeclNGen_722_; lean_object* v_traceState_723_; lean_object* v_messages_724_; lean_object* v_infoState_725_; lean_object* v_snapshotTasks_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_752_; 
v___x_719_ = lean_st_ref_take(v___y_717_);
v_nextMacroScope_720_ = lean_ctor_get(v___x_719_, 1);
v_ngen_721_ = lean_ctor_get(v___x_719_, 2);
v_auxDeclNGen_722_ = lean_ctor_get(v___x_719_, 3);
v_traceState_723_ = lean_ctor_get(v___x_719_, 4);
v_messages_724_ = lean_ctor_get(v___x_719_, 6);
v_infoState_725_ = lean_ctor_get(v___x_719_, 7);
v_snapshotTasks_726_ = lean_ctor_get(v___x_719_, 8);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_753_ = lean_ctor_get(v___x_719_, 5);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_754_);
v___x_728_ = v___x_719_;
v_isShared_729_ = v_isSharedCheck_752_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snapshotTasks_726_);
lean_inc(v_infoState_725_);
lean_inc(v_messages_724_);
lean_inc(v_traceState_723_);
lean_inc(v_auxDeclNGen_722_);
lean_inc(v_ngen_721_);
lean_inc(v_nextMacroScope_720_);
lean_dec(v___x_719_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_752_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 5, v___x_730_);
lean_ctor_set(v___x_728_, 0, v_env_715_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_env_715_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_nextMacroScope_720_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_ngen_721_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_auxDeclNGen_722_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_traceState_723_);
lean_ctor_set(v_reuseFailAlloc_751_, 5, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_751_, 6, v_messages_724_);
lean_ctor_set(v_reuseFailAlloc_751_, 7, v_infoState_725_);
lean_ctor_set(v_reuseFailAlloc_751_, 8, v_snapshotTasks_726_);
v___x_732_ = v_reuseFailAlloc_751_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_mctx_735_; lean_object* v_zetaDeltaFVarIds_736_; lean_object* v_postponed_737_; lean_object* v_diag_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_749_; 
v___x_733_ = lean_st_ref_set(v___y_717_, v___x_732_);
v___x_734_ = lean_st_ref_take(v___y_716_);
v_mctx_735_ = lean_ctor_get(v___x_734_, 0);
v_zetaDeltaFVarIds_736_ = lean_ctor_get(v___x_734_, 2);
v_postponed_737_ = lean_ctor_get(v___x_734_, 3);
v_diag_738_ = lean_ctor_get(v___x_734_, 4);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_734_, 1);
lean_dec(v_unused_750_);
v___x_740_ = v___x_734_;
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_diag_738_);
lean_inc(v_postponed_737_);
lean_inc(v_zetaDeltaFVarIds_736_);
lean_inc(v_mctx_735_);
lean_dec(v___x_734_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_mctx_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_zetaDeltaFVarIds_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_postponed_737_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_diag_738_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_st_ref_set(v___y_716_, v___x_744_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_env_768_; lean_object* v_a_770_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_767_ = lean_st_ref_get(v___y_765_);
v_env_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_ref(v_env_768_);
lean_dec(v___x_767_);
v___x_780_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_760_, v___y_763_, v___y_765_);
lean_dec_ref(v___x_780_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
v___x_781_ = lean_apply_5(v_x_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, lean_box(0));
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_768_, v___y_763_, v___y_765_);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_791_);
v___x_785_ = v___x_783_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_dec(v___x_783_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_a_782_);
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_782_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_781_, 1);
v_a_770_ = v_a_792_;
goto v___jp_769_;
}
v___jp_769_:
{
lean_object* v___x_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v___x_771_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_768_, v___y_763_, v___y_765_);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v___x_771_, 0);
lean_dec(v_unused_779_);
v___x_773_ = v___x_771_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_dec(v___x_771_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 1);
lean_ctor_set(v___x_773_, 0, v_a_770_);
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_770_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_793_, lean_object* v_x_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_793_, v_x_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_801_, lean_object* v_checkType_802_, uint8_t v_safety_803_, uint8_t v_checkMeta_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_810_ = lean_st_ref_get(v_a_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = lean_box(v_checkMeta_804_);
v___x_813_ = lean_box(v_safety_803_);
v___f_814_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_814_, 0, v___x_812_);
lean_closure_set(v___f_814_, 1, v_checkType_802_);
lean_closure_set(v___f_814_, 2, v___x_813_);
lean_closure_set(v___f_814_, 3, v_value_801_);
v___x_815_ = l_Lean_Environment_unlockAsync(v_env_811_);
v___x_816_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_815_, v___f_814_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_817_, lean_object* v_checkType_818_, lean_object* v_safety_819_, lean_object* v_checkMeta_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
uint8_t v_safety_boxed_826_; uint8_t v_checkMeta_boxed_827_; lean_object* v_res_828_; 
v_safety_boxed_826_ = lean_unbox(v_safety_819_);
v_checkMeta_boxed_827_ = lean_unbox(v_checkMeta_820_);
v_res_828_ = l_Lean_Meta_evalExprCore___redArg(v_value_817_, v_checkType_818_, v_safety_boxed_826_, v_checkMeta_boxed_827_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_829_, lean_object* v_value_830_, lean_object* v_checkType_831_, uint8_t v_safety_832_, uint8_t v_checkMeta_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_evalExprCore___redArg(v_value_830_, v_checkType_831_, v_safety_832_, v_checkMeta_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_840_, lean_object* v_value_841_, lean_object* v_checkType_842_, lean_object* v_safety_843_, lean_object* v_checkMeta_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
uint8_t v_safety_boxed_850_; uint8_t v_checkMeta_boxed_851_; lean_object* v_res_852_; 
v_safety_boxed_850_ = lean_unbox(v_safety_843_);
v_checkMeta_boxed_851_ = lean_unbox(v_checkMeta_844_);
v_res_852_ = l_Lean_Meta_evalExprCore(v_00_u03b1_840_, v_value_841_, v_checkType_842_, v_safety_boxed_850_, v_checkMeta_boxed_851_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_867_, lean_object* v_constName_868_, uint8_t v_checkMeta_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_868_, v_checkMeta_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_876_, lean_object* v_constName_877_, lean_object* v_checkMeta_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_checkMeta_boxed_884_; lean_object* v_res_885_; 
v_checkMeta_boxed_884_ = lean_unbox(v_checkMeta_878_);
v_res_885_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_876_, v_constName_877_, v_checkMeta_boxed_884_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_886_, lean_object* v_msg_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_894_, lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_894_, v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_902_, v___y_904_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_916_, lean_object* v_env_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_917_, v_x_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_925_, lean_object* v_env_926_, lean_object* v_x_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_925_, v_env_926_, v_x_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
return v_res_949_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_953_, lean_object* v_type_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_whnfD(v_type_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_974_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_974_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_974_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_974_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; 
v___x_965_ = l_Lean_Expr_isConstOf(v_a_961_, v_typeName_953_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_del_object(v___x_963_);
v___x_966_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_967_ = l_Lean_indentExpr(v_a_961_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_968_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v_a_961_);
v___x_970_ = lean_box(0);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_970_);
v___x_972_ = v___x_963_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_a_975_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_960_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_960_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_983_, lean_object* v_type_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_983_, v_type_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v_typeName_983_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_991_, lean_object* v_value_992_, uint8_t v_safety_993_, uint8_t v_checkMeta_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___f_1000_; lean_object* v___x_1001_; 
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1000_, 0, v_typeName_991_);
v___x_1001_ = l_Lean_Meta_evalExprCore___redArg(v_value_992_, v___f_1000_, v_safety_993_, v_checkMeta_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1002_, lean_object* v_value_1003_, lean_object* v_safety_1004_, lean_object* v_checkMeta_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
uint8_t v_safety_boxed_1011_; uint8_t v_checkMeta_boxed_1012_; lean_object* v_res_1013_; 
v_safety_boxed_1011_ = lean_unbox(v_safety_1004_);
v_checkMeta_boxed_1012_ = lean_unbox(v_checkMeta_1005_);
v_res_1013_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1002_, v_value_1003_, v_safety_boxed_1011_, v_checkMeta_boxed_1012_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1014_, lean_object* v_typeName_1015_, lean_object* v_value_1016_, uint8_t v_safety_1017_, uint8_t v_checkMeta_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1015_, v_value_1016_, v_safety_1017_, v_checkMeta_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_typeName_1026_, lean_object* v_value_1027_, lean_object* v_safety_1028_, lean_object* v_checkMeta_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
uint8_t v_safety_boxed_1035_; uint8_t v_checkMeta_boxed_1036_; lean_object* v_res_1037_; 
v_safety_boxed_1035_ = lean_unbox(v_safety_1028_);
v_checkMeta_boxed_1036_ = lean_unbox(v_checkMeta_1029_);
v_res_1037_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1025_, v_typeName_1026_, v_value_1027_, v_safety_boxed_1035_, v_checkMeta_boxed_1036_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
return v_res_1037_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1043_, lean_object* v_type_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
lean_inc_ref(v_expectedType_1043_);
lean_inc_ref(v_type_1044_);
v___x_1050_ = l_Lean_Meta_isExprDefEq(v_type_1044_, v_expectedType_1043_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1075_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1075_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1075_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_unbox(v_a_1051_);
lean_dec(v_a_1051_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_del_object(v___x_1053_);
v___x_1056_ = lean_box(0);
v___x_1057_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1058_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1044_, v_expectedType_1043_, v___x_1056_, v___x_1057_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v_a_1059_);
v___x_1062_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1061_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1062_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1058_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1058_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_dec_ref(v_type_1044_);
lean_dec_ref(v_expectedType_1043_);
v___x_1071_ = lean_box(0);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1071_);
v___x_1073_ = v___x_1053_;
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
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_type_1044_);
lean_dec_ref(v_expectedType_1043_);
v_a_1076_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1050_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1050_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1084_, lean_object* v_type_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1084_, v_type_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1092_, lean_object* v_value_1093_, uint8_t v_safety_1094_, uint8_t v_checkMeta_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; 
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1101_, 0, v_expectedType_1092_);
v___x_1102_ = l_Lean_Meta_evalExprCore___redArg(v_value_1093_, v___f_1101_, v_safety_1094_, v_checkMeta_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1103_, lean_object* v_value_1104_, lean_object* v_safety_1105_, lean_object* v_checkMeta_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
uint8_t v_safety_boxed_1112_; uint8_t v_checkMeta_boxed_1113_; lean_object* v_res_1114_; 
v_safety_boxed_1112_ = lean_unbox(v_safety_1105_);
v_checkMeta_boxed_1113_ = lean_unbox(v_checkMeta_1106_);
v_res_1114_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1103_, v_value_1104_, v_safety_boxed_1112_, v_checkMeta_boxed_1113_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1115_, lean_object* v_expectedType_1116_, lean_object* v_value_1117_, uint8_t v_safety_1118_, uint8_t v_checkMeta_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1116_, v_value_1117_, v_safety_1118_, v_checkMeta_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1126_, lean_object* v_expectedType_1127_, lean_object* v_value_1128_, lean_object* v_safety_1129_, lean_object* v_checkMeta_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
uint8_t v_safety_boxed_1136_; uint8_t v_checkMeta_boxed_1137_; lean_object* v_res_1138_; 
v_safety_boxed_1136_ = lean_unbox(v_safety_1129_);
v_checkMeta_boxed_1137_ = lean_unbox(v_checkMeta_1130_);
v_res_1138_ = l_Lean_Meta_evalExpr(v_00_u03b1_1126_, v_expectedType_1127_, v_value_1128_, v_safety_boxed_1136_, v_checkMeta_boxed_1137_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1138_;
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

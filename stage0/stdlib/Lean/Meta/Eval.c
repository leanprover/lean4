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
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
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
lean_dec_ref(v___x_162_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_267_, lean_object* v_checkType_268_, uint8_t v_safety_269_, lean_object* v_value_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___y_277_; lean_object* v___y_278_; uint8_t v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; uint8_t v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v_fileName_285_; lean_object* v_fileMap_286_; lean_object* v_currRecDepth_287_; lean_object* v_ref_288_; lean_object* v_currNamespace_289_; lean_object* v_openDecls_290_; lean_object* v_initHeartbeats_291_; lean_object* v_maxHeartbeats_292_; lean_object* v_quotContext_293_; lean_object* v_currMacroScope_294_; lean_object* v_cancelTk_x3f_295_; uint8_t v_suppressElabErrors_296_; lean_object* v_inheritedTraceOptions_297_; lean_object* v___y_298_; lean_object* v___y_312_; lean_object* v___y_313_; uint8_t v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_336_; lean_object* v___y_337_; uint8_t v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; uint8_t v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; uint8_t v___y_347_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; uint8_t v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; uint8_t v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; uint8_t v___y_421_; uint8_t v___y_422_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; lean_object* v___y_448_; uint8_t v___y_449_; lean_object* v___y_450_; uint8_t v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; uint8_t v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; uint8_t v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; uint8_t v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v_nextMacroScope_657_; lean_object* v_ngen_658_; lean_object* v_auxDeclNGen_659_; lean_object* v_traceState_660_; lean_object* v_messages_661_; lean_object* v_infoState_662_; lean_object* v_snapshotTasks_663_; lean_object* v___y_664_; lean_object* v___x_683_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_683_ = lean_st_ref_get(v___y_274_);
lean_inc_ref(v_value_270_);
v___x_696_ = l_Lean_Expr_getUsedConstants(v_value_270_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_array_get_size(v___x_696_);
v___x_699_ = lean_nat_dec_lt(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec_ref(v___x_696_);
lean_dec(v___x_683_);
goto v___jp_684_;
}
else
{
if (v___x_699_ == 0)
{
lean_dec_ref(v___x_696_);
lean_dec(v___x_683_);
goto v___jp_684_;
}
else
{
lean_object* v_env_700_; size_t v___x_701_; size_t v___x_702_; uint8_t v___x_703_; 
v_env_700_ = lean_ctor_get(v___x_683_, 0);
lean_inc_ref(v_env_700_);
lean_dec(v___x_683_);
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_698_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_700_, v___x_696_, v___x_701_, v___x_702_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v_env_700_);
if (v___x_703_ == 0)
{
goto v___jp_684_;
}
else
{
v___y_611_ = v___y_271_;
v___y_612_ = v___y_272_;
v___y_613_ = v___y_273_;
v___y_614_ = v___y_274_;
goto v___jp_610_;
}
}
}
v___jp_276_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_284_, v___y_281_);
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
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*14, v___y_279_);
lean_ctor_set_uint8(v___x_300_, sizeof(void*)*14 + 1, v_suppressElabErrors_296_);
v___x_301_ = l_Lean_addAndCompile(v___y_283_, v___y_282_, v___x_300_, v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v___x_302_; 
lean_dec_ref(v___x_301_);
v___x_302_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_277_, v_checkMeta_267_, v___y_278_, v___y_280_, v___x_300_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___x_300_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_278_);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v___x_300_);
lean_dec(v___y_298_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_278_);
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
if (v___y_347_ == 0)
{
lean_object* v___x_348_; lean_object* v_env_349_; lean_object* v_nextMacroScope_350_; lean_object* v_ngen_351_; lean_object* v_auxDeclNGen_352_; lean_object* v_traceState_353_; lean_object* v_messages_354_; lean_object* v_infoState_355_; lean_object* v_snapshotTasks_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
v___x_348_ = lean_st_ref_take(v___y_343_);
v_env_349_ = lean_ctor_get(v___x_348_, 0);
v_nextMacroScope_350_ = lean_ctor_get(v___x_348_, 1);
v_ngen_351_ = lean_ctor_get(v___x_348_, 2);
v_auxDeclNGen_352_ = lean_ctor_get(v___x_348_, 3);
v_traceState_353_ = lean_ctor_get(v___x_348_, 4);
v_messages_354_ = lean_ctor_get(v___x_348_, 6);
v_infoState_355_ = lean_ctor_get(v___x_348_, 7);
v_snapshotTasks_356_ = lean_ctor_get(v___x_348_, 8);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_348_, 5);
lean_dec(v_unused_366_);
v___x_358_ = v___x_348_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snapshotTasks_356_);
lean_inc(v_infoState_355_);
lean_inc(v_messages_354_);
lean_inc(v_traceState_353_);
lean_inc(v_auxDeclNGen_352_);
lean_inc(v_ngen_351_);
lean_inc(v_nextMacroScope_350_);
lean_inc(v_env_349_);
lean_dec(v___x_348_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = l_Lean_Kernel_enableDiag(v_env_349_, v___y_338_);
lean_inc_ref(v___y_339_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 5, v___y_339_);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_nextMacroScope_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_ngen_351_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_auxDeclNGen_352_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_traceState_353_);
lean_ctor_set(v_reuseFailAlloc_364_, 5, v___y_339_);
lean_ctor_set(v_reuseFailAlloc_364_, 6, v_messages_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 7, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 8, v_snapshotTasks_356_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_st_ref_set(v___y_343_, v___x_362_);
v___y_312_ = v___y_336_;
v___y_313_ = v___y_337_;
v___y_314_ = v___y_338_;
v___y_315_ = v___y_342_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_344_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_345_;
v___y_320_ = v___y_340_;
v___y_321_ = v___y_343_;
goto v___jp_311_;
}
}
}
else
{
v___y_312_ = v___y_336_;
v___y_313_ = v___y_337_;
v___y_314_ = v___y_338_;
v___y_315_ = v___y_342_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_344_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_345_;
v___y_320_ = v___y_340_;
v___y_321_ = v___y_343_;
goto v___jp_311_;
}
}
v___jp_367_:
{
lean_object* v___x_380_; lean_object* v_fileName_381_; lean_object* v_fileMap_382_; lean_object* v_currRecDepth_383_; lean_object* v_ref_384_; lean_object* v_currNamespace_385_; lean_object* v_openDecls_386_; lean_object* v_initHeartbeats_387_; lean_object* v_maxHeartbeats_388_; lean_object* v_quotContext_389_; lean_object* v_currMacroScope_390_; lean_object* v_cancelTk_x3f_391_; uint8_t v_suppressElabErrors_392_; lean_object* v_inheritedTraceOptions_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_406_; 
v___x_380_ = lean_st_ref_get(v___y_379_);
v_fileName_381_ = lean_ctor_get(v___y_378_, 0);
v_fileMap_382_ = lean_ctor_get(v___y_378_, 1);
v_currRecDepth_383_ = lean_ctor_get(v___y_378_, 3);
v_ref_384_ = lean_ctor_get(v___y_378_, 5);
v_currNamespace_385_ = lean_ctor_get(v___y_378_, 6);
v_openDecls_386_ = lean_ctor_get(v___y_378_, 7);
v_initHeartbeats_387_ = lean_ctor_get(v___y_378_, 8);
v_maxHeartbeats_388_ = lean_ctor_get(v___y_378_, 9);
v_quotContext_389_ = lean_ctor_get(v___y_378_, 10);
v_currMacroScope_390_ = lean_ctor_get(v___y_378_, 11);
v_cancelTk_x3f_391_ = lean_ctor_get(v___y_378_, 12);
v_suppressElabErrors_392_ = lean_ctor_get_uint8(v___y_378_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_393_ = lean_ctor_get(v___y_378_, 13);
v_isSharedCheck_406_ = !lean_is_exclusive(v___y_378_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_407_ = lean_ctor_get(v___y_378_, 4);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v___y_378_, 2);
lean_dec(v_unused_408_);
v___x_395_ = v___y_378_;
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_inheritedTraceOptions_393_);
lean_inc(v_cancelTk_x3f_391_);
lean_inc(v_currMacroScope_390_);
lean_inc(v_quotContext_389_);
lean_inc(v_maxHeartbeats_388_);
lean_inc(v_initHeartbeats_387_);
lean_inc(v_openDecls_386_);
lean_inc(v_currNamespace_385_);
lean_inc(v_ref_384_);
lean_inc(v_currRecDepth_383_);
lean_inc(v_fileMap_382_);
lean_inc(v_fileName_381_);
lean_dec(v___y_378_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_406_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_env_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v_env_397_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_397_);
lean_dec(v___x_380_);
v___x_398_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_370_, v___y_374_);
lean_inc_ref(v_inheritedTraceOptions_393_);
lean_inc(v_cancelTk_x3f_391_);
lean_inc(v_currMacroScope_390_);
lean_inc(v_quotContext_389_);
lean_inc(v_maxHeartbeats_388_);
lean_inc(v_initHeartbeats_387_);
lean_inc(v_openDecls_386_);
lean_inc(v_currNamespace_385_);
lean_inc(v_ref_384_);
lean_inc(v_currRecDepth_383_);
lean_inc_ref(v___y_370_);
lean_inc_ref(v_fileMap_382_);
lean_inc_ref(v_fileName_381_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 4, v___x_398_);
lean_ctor_set(v___x_395_, 2, v___y_370_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_fileName_381_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_fileMap_382_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v___y_370_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_currRecDepth_383_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v_ref_384_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_currNamespace_385_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_openDecls_386_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v_initHeartbeats_387_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_maxHeartbeats_388_);
lean_ctor_set(v_reuseFailAlloc_405_, 10, v_quotContext_389_);
lean_ctor_set(v_reuseFailAlloc_405_, 11, v_currMacroScope_390_);
lean_ctor_set(v_reuseFailAlloc_405_, 12, v_cancelTk_x3f_391_);
lean_ctor_set(v_reuseFailAlloc_405_, 13, v_inheritedTraceOptions_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*14 + 1, v_suppressElabErrors_392_);
v___x_400_ = v_reuseFailAlloc_405_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; uint8_t v___x_404_; 
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*14, v___y_377_);
v___x_401_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_402_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_370_, v___x_401_, v___y_375_);
v___x_403_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_402_, v___y_368_);
v___x_404_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_397_);
lean_dec_ref(v_env_397_);
if (v___x_404_ == 0)
{
if (v___x_403_ == 0)
{
lean_dec_ref(v___x_400_);
v___y_277_ = v___y_369_;
v___y_278_ = v___y_371_;
v___y_279_ = v___x_403_;
v___y_280_ = v___y_373_;
v___y_281_ = v___y_374_;
v___y_282_ = v___y_375_;
v___y_283_ = v___y_376_;
v___y_284_ = v___x_402_;
v_fileName_285_ = v_fileName_381_;
v_fileMap_286_ = v_fileMap_382_;
v_currRecDepth_287_ = v_currRecDepth_383_;
v_ref_288_ = v_ref_384_;
v_currNamespace_289_ = v_currNamespace_385_;
v_openDecls_290_ = v_openDecls_386_;
v_initHeartbeats_291_ = v_initHeartbeats_387_;
v_maxHeartbeats_292_ = v_maxHeartbeats_388_;
v_quotContext_293_ = v_quotContext_389_;
v_currMacroScope_294_ = v_currMacroScope_390_;
v_cancelTk_x3f_295_ = v_cancelTk_x3f_391_;
v_suppressElabErrors_296_ = v_suppressElabErrors_392_;
v_inheritedTraceOptions_297_ = v_inheritedTraceOptions_393_;
v___y_298_ = v___y_379_;
goto v___jp_276_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_393_);
lean_dec(v_cancelTk_x3f_391_);
lean_dec(v_currMacroScope_390_);
lean_dec(v_quotContext_389_);
lean_dec(v_maxHeartbeats_388_);
lean_dec(v_initHeartbeats_387_);
lean_dec(v_openDecls_386_);
lean_dec(v_currNamespace_385_);
lean_dec(v_ref_384_);
lean_dec(v_currRecDepth_383_);
lean_dec_ref(v_fileMap_382_);
lean_dec_ref(v_fileName_381_);
v___y_336_ = v___y_369_;
v___y_337_ = v___y_371_;
v___y_338_ = v___x_403_;
v___y_339_ = v___y_372_;
v___y_340_ = v___x_400_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_373_;
v___y_343_ = v___y_379_;
v___y_344_ = v___y_375_;
v___y_345_ = v___x_402_;
v___y_346_ = v___y_376_;
v___y_347_ = v___x_404_;
goto v___jp_335_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_393_);
lean_dec(v_cancelTk_x3f_391_);
lean_dec(v_currMacroScope_390_);
lean_dec(v_quotContext_389_);
lean_dec(v_maxHeartbeats_388_);
lean_dec(v_initHeartbeats_387_);
lean_dec(v_openDecls_386_);
lean_dec(v_currNamespace_385_);
lean_dec(v_ref_384_);
lean_dec(v_currRecDepth_383_);
lean_dec_ref(v_fileMap_382_);
lean_dec_ref(v_fileName_381_);
v___y_336_ = v___y_369_;
v___y_337_ = v___y_371_;
v___y_338_ = v___x_403_;
v___y_339_ = v___y_372_;
v___y_340_ = v___x_400_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_373_;
v___y_343_ = v___y_379_;
v___y_344_ = v___y_375_;
v___y_345_ = v___x_402_;
v___y_346_ = v___y_376_;
v___y_347_ = v___x_403_;
goto v___jp_335_;
}
}
}
}
v___jp_409_:
{
if (v___y_422_ == 0)
{
lean_object* v___x_423_; lean_object* v_env_424_; lean_object* v_nextMacroScope_425_; lean_object* v_ngen_426_; lean_object* v_auxDeclNGen_427_; lean_object* v_traceState_428_; lean_object* v_messages_429_; lean_object* v_infoState_430_; lean_object* v_snapshotTasks_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_440_; 
v___x_423_ = lean_st_ref_take(v___y_412_);
v_env_424_ = lean_ctor_get(v___x_423_, 0);
v_nextMacroScope_425_ = lean_ctor_get(v___x_423_, 1);
v_ngen_426_ = lean_ctor_get(v___x_423_, 2);
v_auxDeclNGen_427_ = lean_ctor_get(v___x_423_, 3);
v_traceState_428_ = lean_ctor_get(v___x_423_, 4);
v_messages_429_ = lean_ctor_get(v___x_423_, 6);
v_infoState_430_ = lean_ctor_get(v___x_423_, 7);
v_snapshotTasks_431_ = lean_ctor_get(v___x_423_, 8);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_423_, 5);
lean_dec(v_unused_441_);
v___x_433_ = v___x_423_;
v_isShared_434_ = v_isSharedCheck_440_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snapshotTasks_431_);
lean_inc(v_infoState_430_);
lean_inc(v_messages_429_);
lean_inc(v_traceState_428_);
lean_inc(v_auxDeclNGen_427_);
lean_inc(v_ngen_426_);
lean_inc(v_nextMacroScope_425_);
lean_inc(v_env_424_);
lean_dec(v___x_423_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_440_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = l_Lean_Kernel_enableDiag(v_env_424_, v___y_414_);
lean_inc_ref(v___y_418_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 5, v___y_418_);
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_nextMacroScope_425_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_ngen_426_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_auxDeclNGen_427_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_traceState_428_);
lean_ctor_set(v_reuseFailAlloc_439_, 5, v___y_418_);
lean_ctor_set(v_reuseFailAlloc_439_, 6, v_messages_429_);
lean_ctor_set(v_reuseFailAlloc_439_, 7, v_infoState_430_);
lean_ctor_set(v_reuseFailAlloc_439_, 8, v_snapshotTasks_431_);
v___x_437_ = v_reuseFailAlloc_439_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; 
v___x_438_ = lean_st_ref_set(v___y_412_, v___x_437_);
v___y_368_ = v___y_415_;
v___y_369_ = v___y_410_;
v___y_370_ = v___y_416_;
v___y_371_ = v___y_411_;
v___y_372_ = v___y_418_;
v___y_373_ = v___y_419_;
v___y_374_ = v___y_420_;
v___y_375_ = v___y_421_;
v___y_376_ = v___y_413_;
v___y_377_ = v___y_414_;
v___y_378_ = v___y_417_;
v___y_379_ = v___y_412_;
goto v___jp_367_;
}
}
}
else
{
v___y_368_ = v___y_415_;
v___y_369_ = v___y_410_;
v___y_370_ = v___y_416_;
v___y_371_ = v___y_411_;
v___y_372_ = v___y_418_;
v___y_373_ = v___y_419_;
v___y_374_ = v___y_420_;
v___y_375_ = v___y_421_;
v___y_376_ = v___y_413_;
v___y_377_ = v___y_414_;
v___y_378_ = v___y_417_;
v___y_379_ = v___y_412_;
goto v___jp_367_;
}
}
v___jp_442_:
{
lean_object* v___x_455_; lean_object* v_fileName_456_; lean_object* v_fileMap_457_; lean_object* v_currRecDepth_458_; lean_object* v_ref_459_; lean_object* v_currNamespace_460_; lean_object* v_openDecls_461_; lean_object* v_initHeartbeats_462_; lean_object* v_maxHeartbeats_463_; lean_object* v_quotContext_464_; lean_object* v_currMacroScope_465_; lean_object* v_cancelTk_x3f_466_; uint8_t v_suppressElabErrors_467_; lean_object* v_inheritedTraceOptions_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_482_; 
v___x_455_ = lean_st_ref_get(v___y_454_);
v_fileName_456_ = lean_ctor_get(v___y_453_, 0);
v_fileMap_457_ = lean_ctor_get(v___y_453_, 1);
v_currRecDepth_458_ = lean_ctor_get(v___y_453_, 3);
v_ref_459_ = lean_ctor_get(v___y_453_, 5);
v_currNamespace_460_ = lean_ctor_get(v___y_453_, 6);
v_openDecls_461_ = lean_ctor_get(v___y_453_, 7);
v_initHeartbeats_462_ = lean_ctor_get(v___y_453_, 8);
v_maxHeartbeats_463_ = lean_ctor_get(v___y_453_, 9);
v_quotContext_464_ = lean_ctor_get(v___y_453_, 10);
v_currMacroScope_465_ = lean_ctor_get(v___y_453_, 11);
v_cancelTk_x3f_466_ = lean_ctor_get(v___y_453_, 12);
v_suppressElabErrors_467_ = lean_ctor_get_uint8(v___y_453_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_468_ = lean_ctor_get(v___y_453_, 13);
v_isSharedCheck_482_ = !lean_is_exclusive(v___y_453_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; lean_object* v_unused_484_; 
v_unused_483_ = lean_ctor_get(v___y_453_, 4);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v___y_453_, 2);
lean_dec(v_unused_484_);
v___x_470_ = v___y_453_;
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_inheritedTraceOptions_468_);
lean_inc(v_cancelTk_x3f_466_);
lean_inc(v_currMacroScope_465_);
lean_inc(v_quotContext_464_);
lean_inc(v_maxHeartbeats_463_);
lean_inc(v_initHeartbeats_462_);
lean_inc(v_openDecls_461_);
lean_inc(v_currNamespace_460_);
lean_inc(v_ref_459_);
lean_inc(v_currRecDepth_458_);
lean_inc(v_fileMap_457_);
lean_inc(v_fileName_456_);
lean_dec(v___y_453_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_env_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v_env_472_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_env_472_);
lean_dec(v___x_455_);
v___x_473_ = l_Lean_maxRecDepth;
v___x_474_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_446_, v___x_473_);
lean_inc_ref(v___y_446_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 4, v___x_474_);
lean_ctor_set(v___x_470_, 2, v___y_446_);
v___x_476_ = v___x_470_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_fileName_456_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_fileMap_457_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v___y_446_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_currRecDepth_458_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v_ref_459_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_currNamespace_460_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_openDecls_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_initHeartbeats_462_);
lean_ctor_set(v_reuseFailAlloc_481_, 9, v_maxHeartbeats_463_);
lean_ctor_set(v_reuseFailAlloc_481_, 10, v_quotContext_464_);
lean_ctor_set(v_reuseFailAlloc_481_, 11, v_currMacroScope_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 12, v_cancelTk_x3f_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 13, v_inheritedTraceOptions_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*14 + 1, v_suppressElabErrors_467_);
v___x_476_ = v_reuseFailAlloc_481_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; uint8_t v___x_480_; 
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*14, v___y_447_);
v___x_477_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_478_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_446_, v___x_477_, v___y_449_);
v___x_479_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_478_, v___y_443_);
v___x_480_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_472_);
lean_dec_ref(v_env_472_);
if (v___x_480_ == 0)
{
if (v___x_479_ == 0)
{
v___y_368_ = v___y_443_;
v___y_369_ = v___y_444_;
v___y_370_ = v___x_478_;
v___y_371_ = v___y_445_;
v___y_372_ = v___y_448_;
v___y_373_ = v___y_450_;
v___y_374_ = v___x_473_;
v___y_375_ = v___y_451_;
v___y_376_ = v___y_452_;
v___y_377_ = v___x_479_;
v___y_378_ = v___x_476_;
v___y_379_ = v___y_454_;
goto v___jp_367_;
}
else
{
v___y_410_ = v___y_444_;
v___y_411_ = v___y_445_;
v___y_412_ = v___y_454_;
v___y_413_ = v___y_452_;
v___y_414_ = v___x_479_;
v___y_415_ = v___y_443_;
v___y_416_ = v___x_478_;
v___y_417_ = v___x_476_;
v___y_418_ = v___y_448_;
v___y_419_ = v___y_450_;
v___y_420_ = v___x_473_;
v___y_421_ = v___y_451_;
v___y_422_ = v___x_480_;
goto v___jp_409_;
}
}
else
{
v___y_410_ = v___y_444_;
v___y_411_ = v___y_445_;
v___y_412_ = v___y_454_;
v___y_413_ = v___y_452_;
v___y_414_ = v___x_479_;
v___y_415_ = v___y_443_;
v___y_416_ = v___x_478_;
v___y_417_ = v___x_476_;
v___y_418_ = v___y_448_;
v___y_419_ = v___y_450_;
v___y_420_ = v___x_473_;
v___y_421_ = v___y_451_;
v___y_422_ = v___x_479_;
goto v___jp_409_;
}
}
}
}
v___jp_485_:
{
if (v___y_498_ == 0)
{
lean_object* v___x_499_; lean_object* v_env_500_; lean_object* v_nextMacroScope_501_; lean_object* v_ngen_502_; lean_object* v_auxDeclNGen_503_; lean_object* v_traceState_504_; lean_object* v_messages_505_; lean_object* v_infoState_506_; lean_object* v_snapshotTasks_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_516_; 
v___x_499_ = lean_st_ref_take(v___y_497_);
v_env_500_ = lean_ctor_get(v___x_499_, 0);
v_nextMacroScope_501_ = lean_ctor_get(v___x_499_, 1);
v_ngen_502_ = lean_ctor_get(v___x_499_, 2);
v_auxDeclNGen_503_ = lean_ctor_get(v___x_499_, 3);
v_traceState_504_ = lean_ctor_get(v___x_499_, 4);
v_messages_505_ = lean_ctor_get(v___x_499_, 6);
v_infoState_506_ = lean_ctor_get(v___x_499_, 7);
v_snapshotTasks_507_ = lean_ctor_get(v___x_499_, 8);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_499_, 5);
lean_dec(v_unused_517_);
v___x_509_ = v___x_499_;
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snapshotTasks_507_);
lean_inc(v_infoState_506_);
lean_inc(v_messages_505_);
lean_inc(v_traceState_504_);
lean_inc(v_auxDeclNGen_503_);
lean_inc(v_ngen_502_);
lean_inc(v_nextMacroScope_501_);
lean_inc(v_env_500_);
lean_dec(v___x_499_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_Kernel_enableDiag(v_env_500_, v___y_493_);
lean_inc_ref(v___y_494_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 5, v___y_494_);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_ngen_502_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_auxDeclNGen_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_traceState_504_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v___y_494_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_messages_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_infoState_506_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_snapshotTasks_507_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_st_ref_set(v___y_497_, v___x_513_);
v___y_443_ = v___y_492_;
v___y_444_ = v___y_486_;
v___y_445_ = v___y_487_;
v___y_446_ = v___y_488_;
v___y_447_ = v___y_493_;
v___y_448_ = v___y_494_;
v___y_449_ = v___y_489_;
v___y_450_ = v___y_495_;
v___y_451_ = v___y_496_;
v___y_452_ = v___y_491_;
v___y_453_ = v___y_490_;
v___y_454_ = v___y_497_;
goto v___jp_442_;
}
}
}
else
{
v___y_443_ = v___y_492_;
v___y_444_ = v___y_486_;
v___y_445_ = v___y_487_;
v___y_446_ = v___y_488_;
v___y_447_ = v___y_493_;
v___y_448_ = v___y_494_;
v___y_449_ = v___y_489_;
v___y_450_ = v___y_495_;
v___y_451_ = v___y_496_;
v___y_452_ = v___y_491_;
v___y_453_ = v___y_490_;
v___y_454_ = v___y_497_;
goto v___jp_442_;
}
}
v___jp_518_:
{
lean_object* v___x_527_; 
lean_inc(v___y_526_);
lean_inc_ref(v___y_525_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc_ref(v___y_521_);
v___x_527_ = lean_infer_type(v___y_521_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_n(v_a_528_, 2);
lean_dec_ref(v___x_527_);
lean_inc(v___y_526_);
lean_inc_ref(v___y_525_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
v___x_529_ = lean_apply_6(v_checkType_268_, v_a_528_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, lean_box(0));
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; lean_object* v_env_531_; lean_object* v_nextMacroScope_532_; lean_object* v_ngen_533_; lean_object* v_auxDeclNGen_534_; lean_object* v_traceState_535_; lean_object* v_messages_536_; lean_object* v_infoState_537_; lean_object* v_snapshotTasks_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___x_529_);
v___x_530_ = lean_st_ref_take(v___y_526_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
v_nextMacroScope_532_ = lean_ctor_get(v___x_530_, 1);
v_ngen_533_ = lean_ctor_get(v___x_530_, 2);
v_auxDeclNGen_534_ = lean_ctor_get(v___x_530_, 3);
v_traceState_535_ = lean_ctor_get(v___x_530_, 4);
v_messages_536_ = lean_ctor_get(v___x_530_, 6);
v_infoState_537_ = lean_ctor_get(v___x_530_, 7);
v_snapshotTasks_538_ = lean_ctor_get(v___x_530_, 8);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_530_, 5);
lean_dec(v_unused_593_);
v___x_540_ = v___x_530_;
v_isShared_541_ = v_isSharedCheck_592_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snapshotTasks_538_);
lean_inc(v_infoState_537_);
lean_inc(v_messages_536_);
lean_inc(v_traceState_535_);
lean_inc(v_auxDeclNGen_534_);
lean_inc(v_ngen_533_);
lean_inc(v_nextMacroScope_532_);
lean_inc(v_env_531_);
lean_dec(v___x_530_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_592_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_542_ = lean_array_to_list(v___y_522_);
lean_inc_n(v___y_519_, 3);
v___x_543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_543_, 0, v___y_519_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
lean_ctor_set(v___x_543_, 2, v_a_528_);
lean_inc(v___y_520_);
v___x_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_544_, 0, v___y_519_);
lean_ctor_set(v___x_544_, 1, v___y_520_);
v___x_545_ = l_Lean_markMeta(v_env_531_, v___y_519_);
v___x_546_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 5, v___x_546_);
lean_ctor_set(v___x_540_, 0, v___x_545_);
v___x_548_ = v___x_540_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_nextMacroScope_532_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_ngen_533_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_auxDeclNGen_534_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_traceState_535_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_messages_536_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v_infoState_537_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_snapshotTasks_538_);
v___x_548_ = v_reuseFailAlloc_591_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_mctx_551_; lean_object* v_zetaDeltaFVarIds_552_; lean_object* v_postponed_553_; lean_object* v_diag_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_589_; 
v___x_549_ = lean_st_ref_set(v___y_526_, v___x_548_);
v___x_550_ = lean_st_ref_take(v___y_524_);
v_mctx_551_ = lean_ctor_get(v___x_550_, 0);
v_zetaDeltaFVarIds_552_ = lean_ctor_get(v___x_550_, 2);
v_postponed_553_ = lean_ctor_get(v___x_550_, 3);
v_diag_554_ = lean_ctor_get(v___x_550_, 4);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v___x_550_, 1);
lean_dec(v_unused_590_);
v___x_556_ = v___x_550_;
v_isShared_557_ = v_isSharedCheck_589_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_diag_554_);
lean_inc(v_postponed_553_);
lean_inc(v_zetaDeltaFVarIds_552_);
lean_inc(v_mctx_551_);
lean_dec(v___x_550_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_589_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_mctx_551_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_zetaDeltaFVarIds_552_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_postponed_553_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_diag_554_);
v___x_560_ = v_reuseFailAlloc_588_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_env_563_; lean_object* v_checked_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_561_ = lean_st_ref_set(v___y_524_, v___x_560_);
v___x_562_ = lean_st_ref_get(v___y_526_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_563_);
lean_dec(v___x_562_);
v_checked_564_ = lean_ctor_get(v_env_563_, 2);
lean_inc_ref(v_checked_564_);
lean_dec_ref(v_env_563_);
v___x_565_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_566_ = l_Lean_traceBlock___redArg(v___x_565_, v_checked_564_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_567_; lean_object* v_options_568_; lean_object* v_env_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; uint8_t v___x_579_; 
lean_dec_ref(v___x_566_);
v___x_567_ = lean_st_ref_get(v___y_526_);
v_options_568_ = lean_ctor_get(v___y_525_, 2);
v_env_569_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_569_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_571_, 0, v___x_543_);
lean_ctor_set(v___x_571_, 1, v___y_521_);
lean_ctor_set(v___x_571_, 2, v___x_570_);
lean_ctor_set(v___x_571_, 3, v___x_544_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*4, v_safety_269_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___x_573_ = 1;
v___x_574_ = l_Lean_Elab_async;
v___x_575_ = 0;
lean_inc_ref(v_options_568_);
v___x_576_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_568_, v___x_574_, v___x_575_);
v___x_577_ = l_Lean_diagnostics;
v___x_578_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_576_, v___x_577_);
v___x_579_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_569_);
lean_dec_ref(v_env_569_);
if (v___x_579_ == 0)
{
if (v___x_578_ == 0)
{
v___y_443_ = v___x_577_;
v___y_444_ = v___y_519_;
v___y_445_ = v___y_523_;
v___y_446_ = v___x_576_;
v___y_447_ = v___x_578_;
v___y_448_ = v___x_546_;
v___y_449_ = v___x_575_;
v___y_450_ = v___y_524_;
v___y_451_ = v___x_573_;
v___y_452_ = v___x_572_;
v___y_453_ = v___y_525_;
v___y_454_ = v___y_526_;
goto v___jp_442_;
}
else
{
v___y_486_ = v___y_519_;
v___y_487_ = v___y_523_;
v___y_488_ = v___x_576_;
v___y_489_ = v___x_575_;
v___y_490_ = v___y_525_;
v___y_491_ = v___x_572_;
v___y_492_ = v___x_577_;
v___y_493_ = v___x_578_;
v___y_494_ = v___x_546_;
v___y_495_ = v___y_524_;
v___y_496_ = v___x_573_;
v___y_497_ = v___y_526_;
v___y_498_ = v___x_579_;
goto v___jp_485_;
}
}
else
{
v___y_486_ = v___y_519_;
v___y_487_ = v___y_523_;
v___y_488_ = v___x_576_;
v___y_489_ = v___x_575_;
v___y_490_ = v___y_525_;
v___y_491_ = v___x_572_;
v___y_492_ = v___x_577_;
v___y_493_ = v___x_578_;
v___y_494_ = v___x_546_;
v___y_495_ = v___y_524_;
v___y_496_ = v___x_573_;
v___y_497_ = v___y_526_;
v___y_498_ = v___x_578_;
goto v___jp_485_;
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v___x_544_);
lean_dec_ref(v___x_543_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_519_);
v_a_580_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_566_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_566_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
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
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_a_528_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_519_);
v_a_594_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_529_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_529_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_519_);
lean_dec_ref(v_checkType_268_);
v_a_602_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_527_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_527_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
v___jp_610_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_st_ref_get(v___y_614_);
v___x_616_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_617_ = l_Lean_Core_mkFreshUserName(v___x_616_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref(v___x_617_);
v___x_619_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_270_, v___y_612_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_env_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_params_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_n(v_a_620_, 2);
lean_dec_ref(v___x_619_);
v_env_621_ = lean_ctor_get(v___x_615_, 0);
lean_inc_ref(v_env_621_);
lean_dec(v___x_615_);
v___x_622_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_623_ = l_Lean_collectLevelParams(v___x_622_, v_a_620_);
v_params_624_ = lean_ctor_get(v___x_623_, 2);
lean_inc_ref(v_params_624_);
lean_dec_ref(v___x_623_);
v___x_625_ = l_Lean_mkPrivateName(v_env_621_, v_a_618_);
lean_dec_ref(v_env_621_);
v___x_626_ = lean_box(0);
v___x_627_ = l_Lean_Expr_hasMVar(v_a_620_);
if (v___x_627_ == 0)
{
v___y_519_ = v___x_625_;
v___y_520_ = v___x_626_;
v___y_521_ = v_a_620_;
v___y_522_ = v_params_624_;
v___y_523_ = v___y_611_;
v___y_524_ = v___y_612_;
v___y_525_ = v___y_613_;
v___y_526_ = v___y_614_;
goto v___jp_518_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_620_);
v___x_629_ = l_Lean_indentExpr(v_a_620_);
v___x_630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_630_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_dec_ref(v___x_631_);
v___y_519_ = v___x_625_;
v___y_520_ = v___x_626_;
v___y_521_ = v_a_620_;
v___y_522_ = v_params_624_;
v___y_523_ = v___y_611_;
v___y_524_ = v___y_612_;
v___y_525_ = v___y_613_;
v___y_526_ = v___y_614_;
goto v___jp_518_;
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v___x_625_);
lean_dec_ref(v_params_624_);
lean_dec(v_a_620_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v_checkType_268_);
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_618_);
lean_dec(v___x_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v_checkType_268_);
v_a_640_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_619_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_619_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v___x_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v_value_270_);
lean_dec_ref(v_checkType_268_);
v_a_648_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_617_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_617_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
v___jp_656_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_mctx_669_; lean_object* v_zetaDeltaFVarIds_670_; lean_object* v_postponed_671_; lean_object* v_diag_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_681_; 
v___x_665_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_666_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_666_, 0, v___y_664_);
lean_ctor_set(v___x_666_, 1, v_nextMacroScope_657_);
lean_ctor_set(v___x_666_, 2, v_ngen_658_);
lean_ctor_set(v___x_666_, 3, v_auxDeclNGen_659_);
lean_ctor_set(v___x_666_, 4, v_traceState_660_);
lean_ctor_set(v___x_666_, 5, v___x_665_);
lean_ctor_set(v___x_666_, 6, v_messages_661_);
lean_ctor_set(v___x_666_, 7, v_infoState_662_);
lean_ctor_set(v___x_666_, 8, v_snapshotTasks_663_);
v___x_667_ = lean_st_ref_set(v___y_274_, v___x_666_);
v___x_668_ = lean_st_ref_take(v___y_272_);
v_mctx_669_ = lean_ctor_get(v___x_668_, 0);
v_zetaDeltaFVarIds_670_ = lean_ctor_get(v___x_668_, 2);
v_postponed_671_ = lean_ctor_get(v___x_668_, 3);
v_diag_672_ = lean_ctor_get(v___x_668_, 4);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_668_, 1);
lean_dec(v_unused_682_);
v___x_674_ = v___x_668_;
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_diag_672_);
lean_inc(v_postponed_671_);
lean_inc(v_zetaDeltaFVarIds_670_);
lean_inc(v_mctx_669_);
lean_dec(v___x_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_mctx_669_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_zetaDeltaFVarIds_670_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_postponed_671_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_diag_672_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
v___x_679_ = lean_st_ref_set(v___y_272_, v___x_678_);
v___y_611_ = v___y_271_;
v___y_612_ = v___y_272_;
v___y_613_ = v___y_273_;
v___y_614_ = v___y_274_;
goto v___jp_610_;
}
}
}
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v_env_686_; lean_object* v_nextMacroScope_687_; lean_object* v_ngen_688_; lean_object* v_auxDeclNGen_689_; lean_object* v_traceState_690_; lean_object* v_messages_691_; lean_object* v_infoState_692_; lean_object* v_snapshotTasks_693_; lean_object* v___x_694_; 
v___x_685_ = lean_st_ref_take(v___y_274_);
v_env_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref_n(v_env_686_, 2);
v_nextMacroScope_687_ = lean_ctor_get(v___x_685_, 1);
lean_inc(v_nextMacroScope_687_);
v_ngen_688_ = lean_ctor_get(v___x_685_, 2);
lean_inc_ref(v_ngen_688_);
v_auxDeclNGen_689_ = lean_ctor_get(v___x_685_, 3);
lean_inc_ref(v_auxDeclNGen_689_);
v_traceState_690_ = lean_ctor_get(v___x_685_, 4);
lean_inc_ref(v_traceState_690_);
v_messages_691_ = lean_ctor_get(v___x_685_, 6);
lean_inc_ref(v_messages_691_);
v_infoState_692_ = lean_ctor_get(v___x_685_, 7);
lean_inc_ref(v_infoState_692_);
v_snapshotTasks_693_ = lean_ctor_get(v___x_685_, 8);
lean_inc_ref(v_snapshotTasks_693_);
lean_dec(v___x_685_);
v___x_694_ = l_Lean_Environment_importEnv_x3f(v_env_686_);
if (lean_obj_tag(v___x_694_) == 0)
{
v_nextMacroScope_657_ = v_nextMacroScope_687_;
v_ngen_658_ = v_ngen_688_;
v_auxDeclNGen_659_ = v_auxDeclNGen_689_;
v_traceState_660_ = v_traceState_690_;
v_messages_661_ = v_messages_691_;
v_infoState_662_ = v_infoState_692_;
v_snapshotTasks_663_ = v_snapshotTasks_693_;
v___y_664_ = v_env_686_;
goto v___jp_656_;
}
else
{
lean_object* v_val_695_; 
lean_dec_ref(v_env_686_);
v_val_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_val_695_);
lean_dec_ref(v___x_694_);
v_nextMacroScope_657_ = v_nextMacroScope_687_;
v_ngen_658_ = v_ngen_688_;
v_auxDeclNGen_659_ = v_auxDeclNGen_689_;
v_traceState_660_ = v_traceState_690_;
v_messages_661_ = v_messages_691_;
v_infoState_662_ = v_infoState_692_;
v_snapshotTasks_663_ = v_snapshotTasks_693_;
v___y_664_ = v_val_695_;
goto v___jp_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_704_, lean_object* v_checkType_705_, lean_object* v_safety_706_, lean_object* v_value_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v_checkMeta_boxed_713_; uint8_t v_safety_boxed_714_; lean_object* v_res_715_; 
v_checkMeta_boxed_713_ = lean_unbox(v_checkMeta_704_);
v_safety_boxed_714_ = lean_unbox(v_safety_706_);
v_res_715_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_713_, v_checkType_705_, v_safety_boxed_714_, v_value_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v_nextMacroScope_721_; lean_object* v_ngen_722_; lean_object* v_auxDeclNGen_723_; lean_object* v_traceState_724_; lean_object* v_messages_725_; lean_object* v_infoState_726_; lean_object* v_snapshotTasks_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_753_; 
v___x_720_ = lean_st_ref_take(v___y_718_);
v_nextMacroScope_721_ = lean_ctor_get(v___x_720_, 1);
v_ngen_722_ = lean_ctor_get(v___x_720_, 2);
v_auxDeclNGen_723_ = lean_ctor_get(v___x_720_, 3);
v_traceState_724_ = lean_ctor_get(v___x_720_, 4);
v_messages_725_ = lean_ctor_get(v___x_720_, 6);
v_infoState_726_ = lean_ctor_get(v___x_720_, 7);
v_snapshotTasks_727_ = lean_ctor_get(v___x_720_, 8);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; lean_object* v_unused_755_; 
v_unused_754_ = lean_ctor_get(v___x_720_, 5);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v___x_720_, 0);
lean_dec(v_unused_755_);
v___x_729_ = v___x_720_;
v_isShared_730_ = v_isSharedCheck_753_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snapshotTasks_727_);
lean_inc(v_infoState_726_);
lean_inc(v_messages_725_);
lean_inc(v_traceState_724_);
lean_inc(v_auxDeclNGen_723_);
lean_inc(v_ngen_722_);
lean_inc(v_nextMacroScope_721_);
lean_dec(v___x_720_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_753_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 5, v___x_731_);
lean_ctor_set(v___x_729_, 0, v_env_716_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_env_716_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_nextMacroScope_721_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_ngen_722_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_auxDeclNGen_723_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_traceState_724_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_752_, 6, v_messages_725_);
lean_ctor_set(v_reuseFailAlloc_752_, 7, v_infoState_726_);
lean_ctor_set(v_reuseFailAlloc_752_, 8, v_snapshotTasks_727_);
v___x_733_ = v_reuseFailAlloc_752_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_mctx_736_; lean_object* v_zetaDeltaFVarIds_737_; lean_object* v_postponed_738_; lean_object* v_diag_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_750_; 
v___x_734_ = lean_st_ref_set(v___y_718_, v___x_733_);
v___x_735_ = lean_st_ref_take(v___y_717_);
v_mctx_736_ = lean_ctor_get(v___x_735_, 0);
v_zetaDeltaFVarIds_737_ = lean_ctor_get(v___x_735_, 2);
v_postponed_738_ = lean_ctor_get(v___x_735_, 3);
v_diag_739_ = lean_ctor_get(v___x_735_, 4);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_735_, 1);
lean_dec(v_unused_751_);
v___x_741_ = v___x_735_;
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_diag_739_);
lean_inc(v_postponed_738_);
lean_inc(v_zetaDeltaFVarIds_737_);
lean_inc(v_mctx_736_);
lean_dec(v___x_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_mctx_736_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_zetaDeltaFVarIds_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_postponed_738_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_diag_739_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_st_ref_set(v___y_717_, v___x_745_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec(v___y_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_761_, lean_object* v_x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v_env_769_; lean_object* v_a_771_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_768_ = lean_st_ref_get(v___y_766_);
v_env_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc_ref(v_env_769_);
lean_dec(v___x_768_);
v___x_781_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_761_, v___y_764_, v___y_766_);
lean_dec_ref(v___x_781_);
lean_inc(v___y_766_);
lean_inc_ref(v___y_765_);
lean_inc(v___y_764_);
lean_inc_ref(v___y_763_);
v___x_782_ = lean_apply_5(v_x_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, lean_box(0));
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_769_, v___y_764_, v___y_766_);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_792_);
v___x_786_ = v___x_784_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_dec(v___x_784_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_a_783_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_783_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_793_; 
v_a_793_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_793_);
lean_dec_ref(v___x_782_);
v_a_771_ = v_a_793_;
goto v___jp_770_;
}
v___jp_770_:
{
lean_object* v___x_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v___x_772_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_769_, v___y_764_, v___y_766_);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_772_, 0);
lean_dec(v_unused_780_);
v___x_774_ = v___x_772_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_dec(v___x_772_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 1);
lean_ctor_set(v___x_774_, 0, v_a_771_);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_771_);
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
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_794_, lean_object* v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_794_, v_x_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_802_, lean_object* v_checkType_803_, uint8_t v_safety_804_, uint8_t v_checkMeta_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; lean_object* v_env_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_811_ = lean_st_ref_get(v_a_809_);
v_env_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref(v_env_812_);
lean_dec(v___x_811_);
v___x_813_ = lean_box(v_checkMeta_805_);
v___x_814_ = lean_box(v_safety_804_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_815_, 0, v___x_813_);
lean_closure_set(v___f_815_, 1, v_checkType_803_);
lean_closure_set(v___f_815_, 2, v___x_814_);
lean_closure_set(v___f_815_, 3, v_value_802_);
v___x_816_ = l_Lean_Environment_unlockAsync(v_env_812_);
v___x_817_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_816_, v___f_815_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_818_, lean_object* v_checkType_819_, lean_object* v_safety_820_, lean_object* v_checkMeta_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
uint8_t v_safety_boxed_827_; uint8_t v_checkMeta_boxed_828_; lean_object* v_res_829_; 
v_safety_boxed_827_ = lean_unbox(v_safety_820_);
v_checkMeta_boxed_828_ = lean_unbox(v_checkMeta_821_);
v_res_829_ = l_Lean_Meta_evalExprCore___redArg(v_value_818_, v_checkType_819_, v_safety_boxed_827_, v_checkMeta_boxed_828_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_830_, lean_object* v_value_831_, lean_object* v_checkType_832_, uint8_t v_safety_833_, uint8_t v_checkMeta_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Meta_evalExprCore___redArg(v_value_831_, v_checkType_832_, v_safety_833_, v_checkMeta_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_841_, lean_object* v_value_842_, lean_object* v_checkType_843_, lean_object* v_safety_844_, lean_object* v_checkMeta_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
uint8_t v_safety_boxed_851_; uint8_t v_checkMeta_boxed_852_; lean_object* v_res_853_; 
v_safety_boxed_851_ = lean_unbox(v_safety_844_);
v_checkMeta_boxed_852_ = lean_unbox(v_checkMeta_845_);
v_res_853_ = l_Lean_Meta_evalExprCore(v_00_u03b1_841_, v_value_842_, v_checkType_843_, v_safety_boxed_851_, v_checkMeta_boxed_852_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_868_, lean_object* v_constName_869_, uint8_t v_checkMeta_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_869_, v_checkMeta_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_877_, lean_object* v_constName_878_, lean_object* v_checkMeta_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v_checkMeta_boxed_885_; lean_object* v_res_886_; 
v_checkMeta_boxed_885_ = lean_unbox(v_checkMeta_879_);
v_res_886_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_877_, v_constName_878_, v_checkMeta_boxed_885_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_887_, lean_object* v_msg_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_895_, lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_895_, v_msg_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_903_, v___y_905_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_917_, lean_object* v_env_918_, lean_object* v_x_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_918_, v_x_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_926_, lean_object* v_env_927_, lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_926_, v_env_927_, v_x_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_935_, lean_object* v_x_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_943_, v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_954_, lean_object* v_type_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_whnfD(v_type_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_975_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_975_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_975_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_975_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_Expr_isConstOf(v_a_962_, v_typeName_954_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_del_object(v___x_964_);
v___x_967_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_968_ = l_Lean_indentExpr(v_a_962_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_969_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec(v_a_962_);
v___x_971_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_971_);
v___x_973_ = v___x_964_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_a_976_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_961_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_961_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_984_, lean_object* v_type_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_984_, v_type_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_typeName_984_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_992_, lean_object* v_value_993_, uint8_t v_safety_994_, uint8_t v_checkMeta_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___f_1001_; lean_object* v___x_1002_; 
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1001_, 0, v_typeName_992_);
v___x_1002_ = l_Lean_Meta_evalExprCore___redArg(v_value_993_, v___f_1001_, v_safety_994_, v_checkMeta_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1003_, lean_object* v_value_1004_, lean_object* v_safety_1005_, lean_object* v_checkMeta_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_safety_boxed_1012_; uint8_t v_checkMeta_boxed_1013_; lean_object* v_res_1014_; 
v_safety_boxed_1012_ = lean_unbox(v_safety_1005_);
v_checkMeta_boxed_1013_ = lean_unbox(v_checkMeta_1006_);
v_res_1014_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1003_, v_value_1004_, v_safety_boxed_1012_, v_checkMeta_boxed_1013_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1015_, lean_object* v_typeName_1016_, lean_object* v_value_1017_, uint8_t v_safety_1018_, uint8_t v_checkMeta_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1016_, v_value_1017_, v_safety_1018_, v_checkMeta_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_typeName_1027_, lean_object* v_value_1028_, lean_object* v_safety_1029_, lean_object* v_checkMeta_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
uint8_t v_safety_boxed_1036_; uint8_t v_checkMeta_boxed_1037_; lean_object* v_res_1038_; 
v_safety_boxed_1036_ = lean_unbox(v_safety_1029_);
v_checkMeta_boxed_1037_ = lean_unbox(v_checkMeta_1030_);
v_res_1038_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1026_, v_typeName_1027_, v_value_1028_, v_safety_boxed_1036_, v_checkMeta_boxed_1037_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1038_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1044_, lean_object* v_type_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
lean_inc_ref(v_expectedType_1044_);
lean_inc_ref(v_type_1045_);
v___x_1051_ = l_Lean_Meta_isExprDefEq(v_type_1045_, v_expectedType_1044_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1076_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1076_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1076_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_unbox(v_a_1052_);
lean_dec(v_a_1052_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_del_object(v___x_1054_);
v___x_1057_ = lean_box(0);
v___x_1058_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1059_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1045_, v_expectedType_1044_, v___x_1057_, v___x_1058_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref(v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_a_1060_);
v___x_1063_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1062_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1063_;
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1059_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1059_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
lean_dec_ref(v_type_1045_);
lean_dec_ref(v_expectedType_1044_);
v___x_1072_ = lean_box(0);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1072_);
v___x_1074_ = v___x_1054_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v_type_1045_);
lean_dec_ref(v_expectedType_1044_);
v_a_1077_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1051_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1051_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1085_, lean_object* v_type_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1085_, v_type_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1093_, lean_object* v_value_1094_, uint8_t v_safety_1095_, uint8_t v_checkMeta_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___f_1102_; lean_object* v___x_1103_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1102_, 0, v_expectedType_1093_);
v___x_1103_ = l_Lean_Meta_evalExprCore___redArg(v_value_1094_, v___f_1102_, v_safety_1095_, v_checkMeta_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1104_, lean_object* v_value_1105_, lean_object* v_safety_1106_, lean_object* v_checkMeta_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
uint8_t v_safety_boxed_1113_; uint8_t v_checkMeta_boxed_1114_; lean_object* v_res_1115_; 
v_safety_boxed_1113_ = lean_unbox(v_safety_1106_);
v_checkMeta_boxed_1114_ = lean_unbox(v_checkMeta_1107_);
v_res_1115_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1104_, v_value_1105_, v_safety_boxed_1113_, v_checkMeta_boxed_1114_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1116_, lean_object* v_expectedType_1117_, lean_object* v_value_1118_, uint8_t v_safety_1119_, uint8_t v_checkMeta_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1117_, v_value_1118_, v_safety_1119_, v_checkMeta_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_expectedType_1128_, lean_object* v_value_1129_, lean_object* v_safety_1130_, lean_object* v_checkMeta_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
uint8_t v_safety_boxed_1137_; uint8_t v_checkMeta_boxed_1138_; lean_object* v_res_1139_; 
v_safety_boxed_1137_ = lean_unbox(v_safety_1130_);
v_checkMeta_boxed_1138_ = lean_unbox(v_checkMeta_1131_);
v_res_1139_ = l_Lean_Meta_evalExpr(v_00_u03b1_1127_, v_expectedType_1128_, v_value_1129_, v_safety_boxed_1137_, v_checkMeta_boxed_1138_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
return v_res_1139_;
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

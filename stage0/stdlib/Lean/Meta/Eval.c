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
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_options_80_ = lean_ctor_get(v___y_72_, 1);
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
v_ref_97_ = lean_ctor_get(v___y_94_, 4);
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
v_options_159_ = lean_ctor_get(v___y_151_, 1);
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
v_options_165_ = lean_ctor_get(v___y_151_, 1);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v_as_187_, size_t v_i_188_, size_t v_stop_189_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_188_, v_stop_189_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_array_uget_borrowed(v_as_187_, v_i_188_);
v___x_196_ = l_Lean_Environment_isImportedConst(v___x_185_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_nat_dec_lt(v___x_197_, v___x_186_);
if (v___x_198_ == 0)
{
goto v___jp_190_;
}
else
{
return v___x_198_;
}
}
else
{
goto v___jp_190_;
}
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
v___jp_190_:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_188_, v___x_191_);
v_i_188_ = v___x_192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v_as_202_, lean_object* v_i_203_, lean_object* v_stop_204_){
_start:
{
size_t v_i_boxed_205_; size_t v_stop_boxed_206_; uint8_t v_res_207_; lean_object* v_r_208_; 
v_i_boxed_205_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_stop_boxed_206_ = lean_unbox_usize(v_stop_204_);
lean_dec(v_stop_204_);
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v___x_200_, v___x_201_, v_as_202_, v_i_boxed_205_, v_stop_boxed_206_);
lean_dec_ref(v_as_202_);
lean_dec(v___x_201_);
lean_dec_ref(v___x_200_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_o_212_, lean_object* v_k_213_, uint8_t v_v_214_){
_start:
{
lean_object* v_map_215_; uint8_t v_hasTrace_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_230_; 
v_map_215_ = lean_ctor_get(v_o_212_, 0);
v_hasTrace_216_ = lean_ctor_get_uint8(v_o_212_, sizeof(void*)*1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_o_212_);
if (v_isSharedCheck_230_ == 0)
{
v___x_218_ = v_o_212_;
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_map_215_);
lean_dec(v_o_212_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_220_, 0, v_v_214_);
lean_inc(v_k_213_);
v___x_221_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_213_, v___x_220_, v_map_215_);
if (v_hasTrace_216_ == 0)
{
lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_225_; 
v___x_222_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1));
v___x_223_ = l_Lean_Name_isPrefixOf(v___x_222_, v_k_213_);
lean_dec(v_k_213_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_225_ = v___x_218_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_221_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_223_);
return v___x_225_;
}
}
else
{
lean_object* v___x_228_; 
lean_dec(v_k_213_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_228_ = v___x_218_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*1, v_hasTrace_216_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object* v_o_231_, lean_object* v_k_232_, lean_object* v_v_233_){
_start:
{
uint8_t v_v_boxed_234_; lean_object* v_res_235_; 
v_v_boxed_234_ = lean_unbox(v_v_233_);
v_res_235_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_o_231_, v_k_232_, v_v_boxed_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_opts_236_, lean_object* v_opt_237_, uint8_t v_val_238_){
_start:
{
lean_object* v_name_239_; lean_object* v___x_240_; 
v_name_239_ = lean_ctor_get(v_opt_237_, 0);
lean_inc(v_name_239_);
lean_dec_ref(v_opt_237_);
v___x_240_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_opts_236_, v_name_239_, v_val_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* v_opts_241_, lean_object* v_opt_242_, lean_object* v_val_243_){
_start:
{
uint8_t v_val_boxed_244_; lean_object* v_res_245_; 
v_val_boxed_244_ = lean_unbox(v_val_243_);
v_res_245_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_opts_241_, v_opt_242_, v_val_boxed_244_);
return v_res_245_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_252_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set(v___x_252_, 2, v___x_251_);
lean_ctor_set(v___x_252_, 3, v___x_251_);
lean_ctor_set(v___x_252_, 4, v___x_251_);
lean_ctor_set(v___x_252_, 5, v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = lean_unsigned_to_nat(16u);
v___x_259_ = lean_mk_array(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9));
v___x_266_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
lean_ctor_set(v___x_267_, 2, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11));
v___x_270_ = l_Lean_stringToMessageData(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_271_, lean_object* v_checkType_272_, uint8_t v_safety_273_, lean_object* v_value_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___y_281_; uint8_t v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; uint8_t v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v_toCold_290_; lean_object* v_currRecDepth_291_; lean_object* v_ref_292_; lean_object* v_currNamespace_293_; lean_object* v_openDecls_294_; lean_object* v_initHeartbeats_295_; lean_object* v_maxHeartbeats_296_; lean_object* v_currMacroScope_297_; uint8_t v_suppressElabErrors_298_; lean_object* v___y_299_; lean_object* v___y_313_; uint8_t v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; uint8_t v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; uint8_t v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; uint8_t v___y_346_; uint8_t v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; uint8_t v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; uint8_t v___y_410_; lean_object* v___y_411_; uint8_t v___y_412_; uint8_t v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; uint8_t v___y_419_; uint8_t v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; uint8_t v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; uint8_t v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; uint8_t v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; uint8_t v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; uint8_t v___y_491_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v_nextMacroScope_650_; lean_object* v_ngen_651_; lean_object* v_auxDeclNGen_652_; lean_object* v_traceState_653_; lean_object* v_messages_654_; lean_object* v_infoState_655_; lean_object* v_snapshotTasks_656_; lean_object* v___y_657_; lean_object* v___x_676_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_676_ = lean_st_ref_get(v___y_278_);
lean_inc_ref(v_value_274_);
v___x_689_ = l_Lean_Expr_getUsedConstants(v_value_274_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v___x_689_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec_ref(v___x_689_);
lean_dec(v___x_676_);
goto v___jp_677_;
}
else
{
if (v___x_692_ == 0)
{
lean_dec_ref(v___x_689_);
lean_dec(v___x_676_);
goto v___jp_677_;
}
else
{
lean_object* v_env_693_; size_t v___x_694_; size_t v___x_695_; uint8_t v___x_696_; 
v_env_693_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_env_693_);
lean_dec(v___x_676_);
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_691_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_693_, v___x_691_, v___x_689_, v___x_694_, v___x_695_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v_env_693_);
if (v___x_696_ == 0)
{
goto v___jp_677_;
}
else
{
v___y_604_ = v___y_275_;
v___y_605_ = v___y_276_;
v___y_606_ = v___y_277_;
v___y_607_ = v___y_278_;
goto v___jp_603_;
}
}
}
v___jp_280_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_281_, v___y_286_);
v___x_301_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_301_, 0, v_toCold_290_);
lean_ctor_set(v___x_301_, 1, v___y_281_);
lean_ctor_set(v___x_301_, 2, v_currRecDepth_291_);
lean_ctor_set(v___x_301_, 3, v___x_300_);
lean_ctor_set(v___x_301_, 4, v_ref_292_);
lean_ctor_set(v___x_301_, 5, v_currNamespace_293_);
lean_ctor_set(v___x_301_, 6, v_openDecls_294_);
lean_ctor_set(v___x_301_, 7, v_initHeartbeats_295_);
lean_ctor_set(v___x_301_, 8, v_maxHeartbeats_296_);
lean_ctor_set(v___x_301_, 9, v_currMacroScope_297_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*10, v___y_285_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*10 + 1, v_suppressElabErrors_298_);
v___x_302_ = l_Lean_addAndCompile(v___y_289_, v___y_287_, v___y_282_, v___x_301_, v___y_299_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
lean_dec_ref_known(v___x_302_, 1);
v___x_303_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_288_, v_checkMeta_271_, v___y_283_, v___y_284_, v___x_301_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref_known(v___x_301_, 10);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v___x_303_;
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec_ref_known(v___x_301_, 10);
lean_dec(v___y_299_);
lean_dec(v___y_288_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
v_a_304_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
v___jp_312_:
{
lean_object* v_toCold_324_; lean_object* v_currRecDepth_325_; lean_object* v_ref_326_; lean_object* v_currNamespace_327_; lean_object* v_openDecls_328_; lean_object* v_initHeartbeats_329_; lean_object* v_maxHeartbeats_330_; lean_object* v_currMacroScope_331_; uint8_t v_suppressElabErrors_332_; 
v_toCold_324_ = lean_ctor_get(v___y_322_, 0);
lean_inc_ref(v_toCold_324_);
v_currRecDepth_325_ = lean_ctor_get(v___y_322_, 2);
lean_inc(v_currRecDepth_325_);
v_ref_326_ = lean_ctor_get(v___y_322_, 4);
lean_inc(v_ref_326_);
v_currNamespace_327_ = lean_ctor_get(v___y_322_, 5);
lean_inc(v_currNamespace_327_);
v_openDecls_328_ = lean_ctor_get(v___y_322_, 6);
lean_inc(v_openDecls_328_);
v_initHeartbeats_329_ = lean_ctor_get(v___y_322_, 7);
lean_inc(v_initHeartbeats_329_);
v_maxHeartbeats_330_ = lean_ctor_get(v___y_322_, 8);
lean_inc(v_maxHeartbeats_330_);
v_currMacroScope_331_ = lean_ctor_get(v___y_322_, 9);
lean_inc(v_currMacroScope_331_);
v_suppressElabErrors_332_ = lean_ctor_get_uint8(v___y_322_, sizeof(void*)*10 + 1);
lean_dec_ref(v___y_322_);
v___y_281_ = v___y_313_;
v___y_282_ = v___y_314_;
v___y_283_ = v___y_315_;
v___y_284_ = v___y_316_;
v___y_285_ = v___y_317_;
v___y_286_ = v___y_318_;
v___y_287_ = v___y_319_;
v___y_288_ = v___y_320_;
v___y_289_ = v___y_321_;
v_toCold_290_ = v_toCold_324_;
v_currRecDepth_291_ = v_currRecDepth_325_;
v_ref_292_ = v_ref_326_;
v_currNamespace_293_ = v_currNamespace_327_;
v_openDecls_294_ = v_openDecls_328_;
v_initHeartbeats_295_ = v_initHeartbeats_329_;
v_maxHeartbeats_296_ = v_maxHeartbeats_330_;
v_currMacroScope_297_ = v_currMacroScope_331_;
v_suppressElabErrors_298_ = v_suppressElabErrors_332_;
v___y_299_ = v___y_323_;
goto v___jp_280_;
}
v___jp_333_:
{
if (v___y_346_ == 0)
{
lean_object* v___x_347_; lean_object* v_env_348_; lean_object* v_nextMacroScope_349_; lean_object* v_ngen_350_; lean_object* v_auxDeclNGen_351_; lean_object* v_traceState_352_; lean_object* v_messages_353_; lean_object* v_infoState_354_; lean_object* v_snapshotTasks_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_364_; 
v___x_347_ = lean_st_ref_take(v___y_340_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
v_nextMacroScope_349_ = lean_ctor_get(v___x_347_, 1);
v_ngen_350_ = lean_ctor_get(v___x_347_, 2);
v_auxDeclNGen_351_ = lean_ctor_get(v___x_347_, 3);
v_traceState_352_ = lean_ctor_get(v___x_347_, 4);
v_messages_353_ = lean_ctor_get(v___x_347_, 6);
v_infoState_354_ = lean_ctor_get(v___x_347_, 7);
v_snapshotTasks_355_ = lean_ctor_get(v___x_347_, 8);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_347_, 5);
lean_dec(v_unused_365_);
v___x_357_ = v___x_347_;
v_isShared_358_ = v_isSharedCheck_364_;
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
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = l_Lean_Kernel_enableDiag(v_env_348_, v___y_343_);
lean_inc_ref(v___y_338_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 5, v___y_338_);
lean_ctor_set(v___x_357_, 0, v___x_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_ngen_350_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_auxDeclNGen_351_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v_traceState_352_);
lean_ctor_set(v_reuseFailAlloc_363_, 5, v___y_338_);
lean_ctor_set(v_reuseFailAlloc_363_, 6, v_messages_353_);
lean_ctor_set(v_reuseFailAlloc_363_, 7, v_infoState_354_);
lean_ctor_set(v_reuseFailAlloc_363_, 8, v_snapshotTasks_355_);
v___x_361_ = v_reuseFailAlloc_363_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_st_ref_put(v___y_340_, v___x_361_);
v___y_313_ = v___y_341_;
v___y_314_ = v___y_342_;
v___y_315_ = v___y_334_;
v___y_316_ = v___y_335_;
v___y_317_ = v___y_343_;
v___y_318_ = v___y_336_;
v___y_319_ = v___y_337_;
v___y_320_ = v___y_344_;
v___y_321_ = v___y_345_;
v___y_322_ = v___y_339_;
v___y_323_ = v___y_340_;
goto v___jp_312_;
}
}
}
else
{
v___y_313_ = v___y_341_;
v___y_314_ = v___y_342_;
v___y_315_ = v___y_334_;
v___y_316_ = v___y_335_;
v___y_317_ = v___y_343_;
v___y_318_ = v___y_336_;
v___y_319_ = v___y_337_;
v___y_320_ = v___y_344_;
v___y_321_ = v___y_345_;
v___y_322_ = v___y_339_;
v___y_323_ = v___y_340_;
goto v___jp_312_;
}
}
v___jp_366_:
{
lean_object* v___x_380_; lean_object* v_toCold_381_; lean_object* v_currRecDepth_382_; lean_object* v_ref_383_; lean_object* v_currNamespace_384_; lean_object* v_openDecls_385_; lean_object* v_initHeartbeats_386_; lean_object* v_maxHeartbeats_387_; lean_object* v_currMacroScope_388_; uint8_t v_suppressElabErrors_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_402_; 
v___x_380_ = lean_st_ref_get(v___y_379_);
v_toCold_381_ = lean_ctor_get(v___y_378_, 0);
v_currRecDepth_382_ = lean_ctor_get(v___y_378_, 2);
v_ref_383_ = lean_ctor_get(v___y_378_, 4);
v_currNamespace_384_ = lean_ctor_get(v___y_378_, 5);
v_openDecls_385_ = lean_ctor_get(v___y_378_, 6);
v_initHeartbeats_386_ = lean_ctor_get(v___y_378_, 7);
v_maxHeartbeats_387_ = lean_ctor_get(v___y_378_, 8);
v_currMacroScope_388_ = lean_ctor_get(v___y_378_, 9);
v_suppressElabErrors_389_ = lean_ctor_get_uint8(v___y_378_, sizeof(void*)*10 + 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v___y_378_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_403_ = lean_ctor_get(v___y_378_, 3);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v___y_378_, 1);
lean_dec(v_unused_404_);
v___x_391_ = v___y_378_;
v_isShared_392_ = v_isSharedCheck_402_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_currMacroScope_388_);
lean_inc(v_maxHeartbeats_387_);
lean_inc(v_initHeartbeats_386_);
lean_inc(v_openDecls_385_);
lean_inc(v_currNamespace_384_);
lean_inc(v_ref_383_);
lean_inc(v_currRecDepth_382_);
lean_inc(v_toCold_381_);
lean_dec(v___y_378_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_402_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_env_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v_env_393_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_393_);
lean_dec(v___x_380_);
v___x_394_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_377_, v___y_370_);
lean_inc(v_currMacroScope_388_);
lean_inc(v_maxHeartbeats_387_);
lean_inc(v_initHeartbeats_386_);
lean_inc(v_openDecls_385_);
lean_inc(v_currNamespace_384_);
lean_inc(v_ref_383_);
lean_inc(v_currRecDepth_382_);
lean_inc_ref(v___y_377_);
lean_inc_ref(v_toCold_381_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 3, v___x_394_);
lean_ctor_set(v___x_391_, 1, v___y_377_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_toCold_381_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___y_377_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_currRecDepth_382_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v_ref_383_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v_currNamespace_384_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_openDecls_385_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_initHeartbeats_386_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_maxHeartbeats_387_);
lean_ctor_set(v_reuseFailAlloc_401_, 9, v_currMacroScope_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_401_, sizeof(void*)*10 + 1, v_suppressElabErrors_389_);
v___x_396_ = v_reuseFailAlloc_401_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; uint8_t v___x_400_; 
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*10, v___y_376_);
v___x_397_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_398_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_377_, v___x_397_, v___y_372_);
v___x_399_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_398_, v___y_371_);
v___x_400_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_393_);
lean_dec_ref(v_env_393_);
if (v___x_399_ == 0)
{
if (v___x_400_ == 0)
{
lean_dec_ref(v___x_396_);
v___y_281_ = v___x_398_;
v___y_282_ = v___y_367_;
v___y_283_ = v___y_368_;
v___y_284_ = v___y_369_;
v___y_285_ = v___x_399_;
v___y_286_ = v___y_370_;
v___y_287_ = v___y_372_;
v___y_288_ = v___y_375_;
v___y_289_ = v___y_374_;
v_toCold_290_ = v_toCold_381_;
v_currRecDepth_291_ = v_currRecDepth_382_;
v_ref_292_ = v_ref_383_;
v_currNamespace_293_ = v_currNamespace_384_;
v_openDecls_294_ = v_openDecls_385_;
v_initHeartbeats_295_ = v_initHeartbeats_386_;
v_maxHeartbeats_296_ = v_maxHeartbeats_387_;
v_currMacroScope_297_ = v_currMacroScope_388_;
v_suppressElabErrors_298_ = v_suppressElabErrors_389_;
v___y_299_ = v___y_379_;
goto v___jp_280_;
}
else
{
lean_dec(v_currMacroScope_388_);
lean_dec(v_maxHeartbeats_387_);
lean_dec(v_initHeartbeats_386_);
lean_dec(v_openDecls_385_);
lean_dec(v_currNamespace_384_);
lean_dec(v_ref_383_);
lean_dec(v_currRecDepth_382_);
lean_dec_ref(v_toCold_381_);
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_372_;
v___y_338_ = v___y_373_;
v___y_339_ = v___x_396_;
v___y_340_ = v___y_379_;
v___y_341_ = v___x_398_;
v___y_342_ = v___y_367_;
v___y_343_ = v___x_399_;
v___y_344_ = v___y_375_;
v___y_345_ = v___y_374_;
v___y_346_ = v___x_399_;
goto v___jp_333_;
}
}
else
{
lean_dec(v_currMacroScope_388_);
lean_dec(v_maxHeartbeats_387_);
lean_dec(v_initHeartbeats_386_);
lean_dec(v_openDecls_385_);
lean_dec(v_currNamespace_384_);
lean_dec(v_ref_383_);
lean_dec(v_currRecDepth_382_);
lean_dec_ref(v_toCold_381_);
v___y_334_ = v___y_368_;
v___y_335_ = v___y_369_;
v___y_336_ = v___y_370_;
v___y_337_ = v___y_372_;
v___y_338_ = v___y_373_;
v___y_339_ = v___x_396_;
v___y_340_ = v___y_379_;
v___y_341_ = v___x_398_;
v___y_342_ = v___y_367_;
v___y_343_ = v___x_399_;
v___y_344_ = v___y_375_;
v___y_345_ = v___y_374_;
v___y_346_ = v___x_400_;
goto v___jp_333_;
}
}
}
}
v___jp_405_:
{
if (v___y_419_ == 0)
{
lean_object* v___x_420_; lean_object* v_env_421_; lean_object* v_nextMacroScope_422_; lean_object* v_ngen_423_; lean_object* v_auxDeclNGen_424_; lean_object* v_traceState_425_; lean_object* v_messages_426_; lean_object* v_infoState_427_; lean_object* v_snapshotTasks_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_437_; 
v___x_420_ = lean_st_ref_take(v___y_414_);
v_env_421_ = lean_ctor_get(v___x_420_, 0);
v_nextMacroScope_422_ = lean_ctor_get(v___x_420_, 1);
v_ngen_423_ = lean_ctor_get(v___x_420_, 2);
v_auxDeclNGen_424_ = lean_ctor_get(v___x_420_, 3);
v_traceState_425_ = lean_ctor_get(v___x_420_, 4);
v_messages_426_ = lean_ctor_get(v___x_420_, 6);
v_infoState_427_ = lean_ctor_get(v___x_420_, 7);
v_snapshotTasks_428_ = lean_ctor_get(v___x_420_, 8);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_420_, 5);
lean_dec(v_unused_438_);
v___x_430_ = v___x_420_;
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snapshotTasks_428_);
lean_inc(v_infoState_427_);
lean_inc(v_messages_426_);
lean_inc(v_traceState_425_);
lean_inc(v_auxDeclNGen_424_);
lean_inc(v_ngen_423_);
lean_inc(v_nextMacroScope_422_);
lean_inc(v_env_421_);
lean_dec(v___x_420_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = l_Lean_Kernel_enableDiag(v_env_421_, v___y_412_);
lean_inc_ref(v___y_411_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 5, v___y_411_);
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_nextMacroScope_422_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_ngen_423_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_auxDeclNGen_424_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_traceState_425_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v___y_411_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v_messages_426_);
lean_ctor_set(v_reuseFailAlloc_436_, 7, v_infoState_427_);
lean_ctor_set(v_reuseFailAlloc_436_, 8, v_snapshotTasks_428_);
v___x_434_ = v_reuseFailAlloc_436_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_st_ref_put(v___y_414_, v___x_434_);
v___y_367_ = v___y_413_;
v___y_368_ = v___y_406_;
v___y_369_ = v___y_407_;
v___y_370_ = v___y_408_;
v___y_371_ = v___y_409_;
v___y_372_ = v___y_410_;
v___y_373_ = v___y_411_;
v___y_374_ = v___y_416_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_412_;
v___y_377_ = v___y_418_;
v___y_378_ = v___y_415_;
v___y_379_ = v___y_414_;
goto v___jp_366_;
}
}
}
else
{
v___y_367_ = v___y_413_;
v___y_368_ = v___y_406_;
v___y_369_ = v___y_407_;
v___y_370_ = v___y_408_;
v___y_371_ = v___y_409_;
v___y_372_ = v___y_410_;
v___y_373_ = v___y_411_;
v___y_374_ = v___y_416_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_412_;
v___y_377_ = v___y_418_;
v___y_378_ = v___y_415_;
v___y_379_ = v___y_414_;
goto v___jp_366_;
}
}
v___jp_439_:
{
lean_object* v___x_452_; lean_object* v_toCold_453_; lean_object* v_currRecDepth_454_; lean_object* v_ref_455_; lean_object* v_currNamespace_456_; lean_object* v_openDecls_457_; lean_object* v_initHeartbeats_458_; lean_object* v_maxHeartbeats_459_; lean_object* v_currMacroScope_460_; uint8_t v_suppressElabErrors_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_475_; 
v___x_452_ = lean_st_ref_get(v___y_451_);
v_toCold_453_ = lean_ctor_get(v___y_450_, 0);
v_currRecDepth_454_ = lean_ctor_get(v___y_450_, 2);
v_ref_455_ = lean_ctor_get(v___y_450_, 4);
v_currNamespace_456_ = lean_ctor_get(v___y_450_, 5);
v_openDecls_457_ = lean_ctor_get(v___y_450_, 6);
v_initHeartbeats_458_ = lean_ctor_get(v___y_450_, 7);
v_maxHeartbeats_459_ = lean_ctor_get(v___y_450_, 8);
v_currMacroScope_460_ = lean_ctor_get(v___y_450_, 9);
v_suppressElabErrors_461_ = lean_ctor_get_uint8(v___y_450_, sizeof(void*)*10 + 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___y_450_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; lean_object* v_unused_477_; 
v_unused_476_ = lean_ctor_get(v___y_450_, 3);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v___y_450_, 1);
lean_dec(v_unused_477_);
v___x_463_ = v___y_450_;
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_currMacroScope_460_);
lean_inc(v_maxHeartbeats_459_);
lean_inc(v_initHeartbeats_458_);
lean_inc(v_openDecls_457_);
lean_inc(v_currNamespace_456_);
lean_inc(v_ref_455_);
lean_inc(v_currRecDepth_454_);
lean_inc(v_toCold_453_);
lean_dec(v___y_450_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_env_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v_env_465_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref(v_env_465_);
lean_dec(v___x_452_);
v___x_466_ = l_Lean_maxRecDepth;
v___x_467_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_449_, v___x_466_);
lean_inc_ref(v___y_449_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 3, v___x_467_);
lean_ctor_set(v___x_463_, 1, v___y_449_);
v___x_469_ = v___x_463_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_toCold_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___y_449_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_currRecDepth_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_ref_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_currNamespace_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_openDecls_457_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_initHeartbeats_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_maxHeartbeats_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_currMacroScope_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*10 + 1, v_suppressElabErrors_461_);
v___x_469_ = v_reuseFailAlloc_474_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; uint8_t v___x_473_; 
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*10, v___y_448_);
v___x_470_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_471_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_449_, v___x_470_, v___y_440_);
v___x_472_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_471_, v___y_443_);
v___x_473_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_465_);
lean_dec_ref(v_env_465_);
if (v___x_472_ == 0)
{
if (v___x_473_ == 0)
{
v___y_367_ = v___y_440_;
v___y_368_ = v___y_441_;
v___y_369_ = v___y_442_;
v___y_370_ = v___x_466_;
v___y_371_ = v___y_443_;
v___y_372_ = v___y_444_;
v___y_373_ = v___y_445_;
v___y_374_ = v___y_447_;
v___y_375_ = v___y_446_;
v___y_376_ = v___x_472_;
v___y_377_ = v___x_471_;
v___y_378_ = v___x_469_;
v___y_379_ = v___y_451_;
goto v___jp_366_;
}
else
{
v___y_406_ = v___y_441_;
v___y_407_ = v___y_442_;
v___y_408_ = v___x_466_;
v___y_409_ = v___y_443_;
v___y_410_ = v___y_444_;
v___y_411_ = v___y_445_;
v___y_412_ = v___x_472_;
v___y_413_ = v___y_440_;
v___y_414_ = v___y_451_;
v___y_415_ = v___x_469_;
v___y_416_ = v___y_447_;
v___y_417_ = v___y_446_;
v___y_418_ = v___x_471_;
v___y_419_ = v___x_472_;
goto v___jp_405_;
}
}
else
{
v___y_406_ = v___y_441_;
v___y_407_ = v___y_442_;
v___y_408_ = v___x_466_;
v___y_409_ = v___y_443_;
v___y_410_ = v___y_444_;
v___y_411_ = v___y_445_;
v___y_412_ = v___x_472_;
v___y_413_ = v___y_440_;
v___y_414_ = v___y_451_;
v___y_415_ = v___x_469_;
v___y_416_ = v___y_447_;
v___y_417_ = v___y_446_;
v___y_418_ = v___x_471_;
v___y_419_ = v___x_473_;
goto v___jp_405_;
}
}
}
}
v___jp_478_:
{
if (v___y_491_ == 0)
{
lean_object* v___x_492_; lean_object* v_env_493_; lean_object* v_nextMacroScope_494_; lean_object* v_ngen_495_; lean_object* v_auxDeclNGen_496_; lean_object* v_traceState_497_; lean_object* v_messages_498_; lean_object* v_infoState_499_; lean_object* v_snapshotTasks_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_509_; 
v___x_492_ = lean_st_ref_take(v___y_485_);
v_env_493_ = lean_ctor_get(v___x_492_, 0);
v_nextMacroScope_494_ = lean_ctor_get(v___x_492_, 1);
v_ngen_495_ = lean_ctor_get(v___x_492_, 2);
v_auxDeclNGen_496_ = lean_ctor_get(v___x_492_, 3);
v_traceState_497_ = lean_ctor_get(v___x_492_, 4);
v_messages_498_ = lean_ctor_get(v___x_492_, 6);
v_infoState_499_ = lean_ctor_get(v___x_492_, 7);
v_snapshotTasks_500_ = lean_ctor_get(v___x_492_, 8);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_492_, 5);
lean_dec(v_unused_510_);
v___x_502_ = v___x_492_;
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_snapshotTasks_500_);
lean_inc(v_infoState_499_);
lean_inc(v_messages_498_);
lean_inc(v_traceState_497_);
lean_inc(v_auxDeclNGen_496_);
lean_inc(v_ngen_495_);
lean_inc(v_nextMacroScope_494_);
lean_inc(v_env_493_);
lean_dec(v___x_492_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = l_Lean_Kernel_enableDiag(v_env_493_, v___y_486_);
lean_inc_ref(v___y_484_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 5, v___y_484_);
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_nextMacroScope_494_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_ngen_495_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_auxDeclNGen_496_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_traceState_497_);
lean_ctor_set(v_reuseFailAlloc_508_, 5, v___y_484_);
lean_ctor_set(v_reuseFailAlloc_508_, 6, v_messages_498_);
lean_ctor_set(v_reuseFailAlloc_508_, 7, v_infoState_499_);
lean_ctor_set(v_reuseFailAlloc_508_, 8, v_snapshotTasks_500_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = lean_st_ref_put(v___y_485_, v___x_506_);
v___y_440_ = v___y_487_;
v___y_441_ = v___y_480_;
v___y_442_ = v___y_481_;
v___y_443_ = v___y_482_;
v___y_444_ = v___y_483_;
v___y_445_ = v___y_484_;
v___y_446_ = v___y_488_;
v___y_447_ = v___y_489_;
v___y_448_ = v___y_486_;
v___y_449_ = v___y_490_;
v___y_450_ = v___y_479_;
v___y_451_ = v___y_485_;
goto v___jp_439_;
}
}
}
else
{
v___y_440_ = v___y_487_;
v___y_441_ = v___y_480_;
v___y_442_ = v___y_481_;
v___y_443_ = v___y_482_;
v___y_444_ = v___y_483_;
v___y_445_ = v___y_484_;
v___y_446_ = v___y_488_;
v___y_447_ = v___y_489_;
v___y_448_ = v___y_486_;
v___y_449_ = v___y_490_;
v___y_450_ = v___y_479_;
v___y_451_ = v___y_485_;
goto v___jp_439_;
}
}
v___jp_511_:
{
lean_object* v___x_520_; 
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc_ref(v___y_513_);
v___x_520_ = lean_infer_type(v___y_513_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_n(v_a_521_, 2);
lean_dec_ref_known(v___x_520_, 1);
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
v___x_522_ = lean_apply_6(v_checkType_272_, v_a_521_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, lean_box(0));
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v_nextMacroScope_525_; lean_object* v_ngen_526_; lean_object* v_auxDeclNGen_527_; lean_object* v_traceState_528_; lean_object* v_messages_529_; lean_object* v_infoState_530_; lean_object* v_snapshotTasks_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref_known(v___x_522_, 1);
v___x_523_ = lean_st_ref_take(v___y_519_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
v_nextMacroScope_525_ = lean_ctor_get(v___x_523_, 1);
v_ngen_526_ = lean_ctor_get(v___x_523_, 2);
v_auxDeclNGen_527_ = lean_ctor_get(v___x_523_, 3);
v_traceState_528_ = lean_ctor_get(v___x_523_, 4);
v_messages_529_ = lean_ctor_get(v___x_523_, 6);
v_infoState_530_ = lean_ctor_get(v___x_523_, 7);
v_snapshotTasks_531_ = lean_ctor_get(v___x_523_, 8);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v___x_523_, 5);
lean_dec(v_unused_586_);
v___x_533_ = v___x_523_;
v_isShared_534_ = v_isSharedCheck_585_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snapshotTasks_531_);
lean_inc(v_infoState_530_);
lean_inc(v_messages_529_);
lean_inc(v_traceState_528_);
lean_inc(v_auxDeclNGen_527_);
lean_inc(v_ngen_526_);
lean_inc(v_nextMacroScope_525_);
lean_inc(v_env_524_);
lean_dec(v___x_523_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_585_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_535_ = lean_array_to_list(v___y_512_);
lean_inc_n(v___y_515_, 3);
v___x_536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_536_, 0, v___y_515_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_ctor_set(v___x_536_, 2, v_a_521_);
lean_inc(v___y_514_);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___y_515_);
lean_ctor_set(v___x_537_, 1, v___y_514_);
v___x_538_ = l_Lean_markMeta(v_env_524_, v___y_515_);
v___x_539_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 5, v___x_539_);
lean_ctor_set(v___x_533_, 0, v___x_538_);
v___x_541_ = v___x_533_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_nextMacroScope_525_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_ngen_526_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_auxDeclNGen_527_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_traceState_528_);
lean_ctor_set(v_reuseFailAlloc_584_, 5, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_584_, 6, v_messages_529_);
lean_ctor_set(v_reuseFailAlloc_584_, 7, v_infoState_530_);
lean_ctor_set(v_reuseFailAlloc_584_, 8, v_snapshotTasks_531_);
v___x_541_ = v_reuseFailAlloc_584_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_mctx_544_; lean_object* v_zetaDeltaFVarIds_545_; lean_object* v_postponed_546_; lean_object* v_diag_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_582_; 
v___x_542_ = lean_st_ref_put(v___y_519_, v___x_541_);
v___x_543_ = lean_st_ref_take(v___y_517_);
v_mctx_544_ = lean_ctor_get(v___x_543_, 0);
v_zetaDeltaFVarIds_545_ = lean_ctor_get(v___x_543_, 2);
v_postponed_546_ = lean_ctor_get(v___x_543_, 3);
v_diag_547_ = lean_ctor_get(v___x_543_, 4);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_543_, 1);
lean_dec(v_unused_583_);
v___x_549_ = v___x_543_;
v_isShared_550_ = v_isSharedCheck_582_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_diag_547_);
lean_inc(v_postponed_546_);
lean_inc(v_zetaDeltaFVarIds_545_);
lean_inc(v_mctx_544_);
lean_dec(v___x_543_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_582_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_mctx_544_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_zetaDeltaFVarIds_545_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_postponed_546_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_diag_547_);
v___x_553_ = v_reuseFailAlloc_581_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_env_556_; lean_object* v_checked_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_554_ = lean_st_ref_put(v___y_517_, v___x_553_);
v___x_555_ = lean_st_ref_get(v___y_519_);
v_env_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc_ref(v_env_556_);
lean_dec(v___x_555_);
v_checked_557_ = lean_ctor_get(v_env_556_, 2);
lean_inc_ref(v_checked_557_);
lean_dec_ref(v_env_556_);
v___x_558_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_559_ = l_Lean_traceBlock___redArg(v___x_558_, v_checked_557_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_560_; lean_object* v_options_561_; lean_object* v_env_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; uint8_t v___x_572_; 
lean_dec_ref_known(v___x_559_, 1);
v___x_560_ = lean_st_ref_get(v___y_519_);
v_options_561_ = lean_ctor_get(v___y_518_, 1);
v_env_562_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_564_, 0, v___x_536_);
lean_ctor_set(v___x_564_, 1, v___y_513_);
lean_ctor_set(v___x_564_, 2, v___x_563_);
lean_ctor_set(v___x_564_, 3, v___x_537_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*4, v_safety_273_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = 1;
v___x_567_ = 0;
v___x_568_ = l_Lean_Elab_async;
lean_inc_ref(v_options_561_);
v___x_569_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_561_, v___x_568_, v___x_567_);
v___x_570_ = l_Lean_diagnostics;
v___x_571_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_569_, v___x_570_);
v___x_572_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_562_);
lean_dec_ref(v_env_562_);
if (v___x_571_ == 0)
{
if (v___x_572_ == 0)
{
v___y_440_ = v___x_567_;
v___y_441_ = v___y_516_;
v___y_442_ = v___y_517_;
v___y_443_ = v___x_570_;
v___y_444_ = v___x_566_;
v___y_445_ = v___x_539_;
v___y_446_ = v___y_515_;
v___y_447_ = v___x_565_;
v___y_448_ = v___x_571_;
v___y_449_ = v___x_569_;
v___y_450_ = v___y_518_;
v___y_451_ = v___y_519_;
goto v___jp_439_;
}
else
{
v___y_479_ = v___y_518_;
v___y_480_ = v___y_516_;
v___y_481_ = v___y_517_;
v___y_482_ = v___x_570_;
v___y_483_ = v___x_566_;
v___y_484_ = v___x_539_;
v___y_485_ = v___y_519_;
v___y_486_ = v___x_571_;
v___y_487_ = v___x_567_;
v___y_488_ = v___y_515_;
v___y_489_ = v___x_565_;
v___y_490_ = v___x_569_;
v___y_491_ = v___x_571_;
goto v___jp_478_;
}
}
else
{
v___y_479_ = v___y_518_;
v___y_480_ = v___y_516_;
v___y_481_ = v___y_517_;
v___y_482_ = v___x_570_;
v___y_483_ = v___x_566_;
v___y_484_ = v___x_539_;
v___y_485_ = v___y_519_;
v___y_486_ = v___x_571_;
v___y_487_ = v___x_567_;
v___y_488_ = v___y_515_;
v___y_489_ = v___x_565_;
v___y_490_ = v___x_569_;
v___y_491_ = v___x_572_;
goto v___jp_478_;
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref_known(v___x_537_, 2);
lean_dec_ref_known(v___x_536_, 3);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_513_);
v_a_573_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_559_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_559_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
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
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v_a_521_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_512_);
v_a_587_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_522_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_522_);
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
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_checkType_272_);
v_a_595_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_520_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_520_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
v___jp_603_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_st_ref_get(v___y_607_);
v___x_609_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_610_ = l_Lean_Core_mkFreshUserName(v___x_609_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_274_, v___y_605_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v_env_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_params_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc_n(v_a_613_, 2);
lean_dec_ref_known(v___x_612_, 1);
v_env_614_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_608_);
v___x_615_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_616_ = l_Lean_collectLevelParams(v___x_615_, v_a_613_);
v_params_617_ = lean_ctor_get(v___x_616_, 2);
lean_inc_ref(v_params_617_);
lean_dec_ref(v___x_616_);
v___x_618_ = l_Lean_mkPrivateName(v_env_614_, v_a_611_);
lean_dec_ref(v_env_614_);
v___x_619_ = lean_box(0);
v___x_620_ = l_Lean_Expr_hasMVar(v_a_613_);
if (v___x_620_ == 0)
{
v___y_512_ = v_params_617_;
v___y_513_ = v_a_613_;
v___y_514_ = v___x_619_;
v___y_515_ = v___x_618_;
v___y_516_ = v___y_604_;
v___y_517_ = v___y_605_;
v___y_518_ = v___y_606_;
v___y_519_ = v___y_607_;
goto v___jp_511_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_613_);
v___x_622_ = l_Lean_indentExpr(v_a_613_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_623_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec_ref_known(v___x_624_, 1);
v___y_512_ = v_params_617_;
v___y_513_ = v_a_613_;
v___y_514_ = v___x_619_;
v___y_515_ = v___x_618_;
v___y_516_ = v___y_604_;
v___y_517_ = v___y_605_;
v___y_518_ = v___y_606_;
v___y_519_ = v___y_607_;
goto v___jp_511_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v___x_618_);
lean_dec_ref(v_params_617_);
lean_dec(v_a_613_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec_ref(v_checkType_272_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_611_);
lean_dec(v___x_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec_ref(v_checkType_272_);
v_a_633_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_612_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_612_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v___x_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec_ref(v_value_274_);
lean_dec_ref(v_checkType_272_);
v_a_641_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_610_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_610_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
v___jp_649_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_mctx_662_; lean_object* v_zetaDeltaFVarIds_663_; lean_object* v_postponed_664_; lean_object* v_diag_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_674_; 
v___x_658_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_659_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_659_, 0, v___y_657_);
lean_ctor_set(v___x_659_, 1, v_nextMacroScope_650_);
lean_ctor_set(v___x_659_, 2, v_ngen_651_);
lean_ctor_set(v___x_659_, 3, v_auxDeclNGen_652_);
lean_ctor_set(v___x_659_, 4, v_traceState_653_);
lean_ctor_set(v___x_659_, 5, v___x_658_);
lean_ctor_set(v___x_659_, 6, v_messages_654_);
lean_ctor_set(v___x_659_, 7, v_infoState_655_);
lean_ctor_set(v___x_659_, 8, v_snapshotTasks_656_);
v___x_660_ = lean_st_ref_put(v___y_278_, v___x_659_);
v___x_661_ = lean_st_ref_take(v___y_276_);
v_mctx_662_ = lean_ctor_get(v___x_661_, 0);
v_zetaDeltaFVarIds_663_ = lean_ctor_get(v___x_661_, 2);
v_postponed_664_ = lean_ctor_get(v___x_661_, 3);
v_diag_665_ = lean_ctor_get(v___x_661_, 4);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_661_, 1);
lean_dec(v_unused_675_);
v___x_667_ = v___x_661_;
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_diag_665_);
lean_inc(v_postponed_664_);
lean_inc(v_zetaDeltaFVarIds_663_);
lean_inc(v_mctx_662_);
lean_dec(v___x_661_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_mctx_662_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_zetaDeltaFVarIds_663_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v_postponed_664_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v_diag_665_);
v___x_671_ = v_reuseFailAlloc_673_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_st_ref_put(v___y_276_, v___x_671_);
v___y_604_ = v___y_275_;
v___y_605_ = v___y_276_;
v___y_606_ = v___y_277_;
v___y_607_ = v___y_278_;
goto v___jp_603_;
}
}
}
v___jp_677_:
{
lean_object* v___x_678_; lean_object* v_env_679_; lean_object* v_nextMacroScope_680_; lean_object* v_ngen_681_; lean_object* v_auxDeclNGen_682_; lean_object* v_traceState_683_; lean_object* v_messages_684_; lean_object* v_infoState_685_; lean_object* v_snapshotTasks_686_; lean_object* v___x_687_; 
v___x_678_ = lean_st_ref_take(v___y_278_);
v_env_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc_ref_n(v_env_679_, 2);
v_nextMacroScope_680_ = lean_ctor_get(v___x_678_, 1);
lean_inc(v_nextMacroScope_680_);
v_ngen_681_ = lean_ctor_get(v___x_678_, 2);
lean_inc_ref(v_ngen_681_);
v_auxDeclNGen_682_ = lean_ctor_get(v___x_678_, 3);
lean_inc_ref(v_auxDeclNGen_682_);
v_traceState_683_ = lean_ctor_get(v___x_678_, 4);
lean_inc_ref(v_traceState_683_);
v_messages_684_ = lean_ctor_get(v___x_678_, 6);
lean_inc_ref(v_messages_684_);
v_infoState_685_ = lean_ctor_get(v___x_678_, 7);
lean_inc_ref(v_infoState_685_);
v_snapshotTasks_686_ = lean_ctor_get(v___x_678_, 8);
lean_inc_ref(v_snapshotTasks_686_);
lean_dec(v___x_678_);
v___x_687_ = l_Lean_Environment_importEnv_x3f(v_env_679_);
if (lean_obj_tag(v___x_687_) == 0)
{
v_nextMacroScope_650_ = v_nextMacroScope_680_;
v_ngen_651_ = v_ngen_681_;
v_auxDeclNGen_652_ = v_auxDeclNGen_682_;
v_traceState_653_ = v_traceState_683_;
v_messages_654_ = v_messages_684_;
v_infoState_655_ = v_infoState_685_;
v_snapshotTasks_656_ = v_snapshotTasks_686_;
v___y_657_ = v_env_679_;
goto v___jp_649_;
}
else
{
lean_object* v_val_688_; 
lean_dec_ref(v_env_679_);
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v___x_687_, 1);
v_nextMacroScope_650_ = v_nextMacroScope_680_;
v_ngen_651_ = v_ngen_681_;
v_auxDeclNGen_652_ = v_auxDeclNGen_682_;
v_traceState_653_ = v_traceState_683_;
v_messages_654_ = v_messages_684_;
v_infoState_655_ = v_infoState_685_;
v_snapshotTasks_656_ = v_snapshotTasks_686_;
v___y_657_ = v_val_688_;
goto v___jp_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_697_, lean_object* v_checkType_698_, lean_object* v_safety_699_, lean_object* v_value_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
uint8_t v_checkMeta_boxed_706_; uint8_t v_safety_boxed_707_; lean_object* v_res_708_; 
v_checkMeta_boxed_706_ = lean_unbox(v_checkMeta_697_);
v_safety_boxed_707_ = lean_unbox(v_safety_699_);
v_res_708_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_706_, v_checkType_698_, v_safety_boxed_707_, v_value_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; lean_object* v_nextMacroScope_714_; lean_object* v_ngen_715_; lean_object* v_auxDeclNGen_716_; lean_object* v_traceState_717_; lean_object* v_messages_718_; lean_object* v_infoState_719_; lean_object* v_snapshotTasks_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_746_; 
v___x_713_ = lean_st_ref_take(v___y_711_);
v_nextMacroScope_714_ = lean_ctor_get(v___x_713_, 1);
v_ngen_715_ = lean_ctor_get(v___x_713_, 2);
v_auxDeclNGen_716_ = lean_ctor_get(v___x_713_, 3);
v_traceState_717_ = lean_ctor_get(v___x_713_, 4);
v_messages_718_ = lean_ctor_get(v___x_713_, 6);
v_infoState_719_ = lean_ctor_get(v___x_713_, 7);
v_snapshotTasks_720_ = lean_ctor_get(v___x_713_, 8);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; lean_object* v_unused_748_; 
v_unused_747_ = lean_ctor_get(v___x_713_, 5);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_748_);
v___x_722_ = v___x_713_;
v_isShared_723_ = v_isSharedCheck_746_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_snapshotTasks_720_);
lean_inc(v_infoState_719_);
lean_inc(v_messages_718_);
lean_inc(v_traceState_717_);
lean_inc(v_auxDeclNGen_716_);
lean_inc(v_ngen_715_);
lean_inc(v_nextMacroScope_714_);
lean_dec(v___x_713_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_746_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 5, v___x_724_);
lean_ctor_set(v___x_722_, 0, v_env_709_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_env_709_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_nextMacroScope_714_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_ngen_715_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_auxDeclNGen_716_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_traceState_717_);
lean_ctor_set(v_reuseFailAlloc_745_, 5, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_745_, 6, v_messages_718_);
lean_ctor_set(v_reuseFailAlloc_745_, 7, v_infoState_719_);
lean_ctor_set(v_reuseFailAlloc_745_, 8, v_snapshotTasks_720_);
v___x_726_ = v_reuseFailAlloc_745_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_mctx_729_; lean_object* v_zetaDeltaFVarIds_730_; lean_object* v_postponed_731_; lean_object* v_diag_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_743_; 
v___x_727_ = lean_st_ref_put(v___y_711_, v___x_726_);
v___x_728_ = lean_st_ref_take(v___y_710_);
v_mctx_729_ = lean_ctor_get(v___x_728_, 0);
v_zetaDeltaFVarIds_730_ = lean_ctor_get(v___x_728_, 2);
v_postponed_731_ = lean_ctor_get(v___x_728_, 3);
v_diag_732_ = lean_ctor_get(v___x_728_, 4);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_728_, 1);
lean_dec(v_unused_744_);
v___x_734_ = v___x_728_;
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_diag_732_);
lean_inc(v_postponed_731_);
lean_inc(v_zetaDeltaFVarIds_730_);
lean_inc(v_mctx_729_);
lean_dec(v___x_728_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_mctx_729_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_zetaDeltaFVarIds_730_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_postponed_731_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v_diag_732_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_st_ref_put(v___y_710_, v___x_738_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec(v___y_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_754_, lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v_env_762_; lean_object* v_a_764_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_761_ = lean_st_ref_get(v___y_759_);
v_env_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_env_762_);
lean_dec(v___x_761_);
v___x_774_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_754_, v___y_757_, v___y_759_);
lean_dec_ref(v___x_774_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc_ref(v___y_756_);
v___x_775_ = lean_apply_5(v_x_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, lean_box(0));
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_762_, v___y_757_, v___y_759_);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v___x_777_, 0);
lean_dec(v_unused_785_);
v___x_779_ = v___x_777_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_dec(v___x_777_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_a_776_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_776_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_775_, 1);
v_a_764_ = v_a_786_;
goto v___jp_763_;
}
v___jp_763_:
{
lean_object* v___x_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v___x_765_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_762_, v___y_757_, v___y_759_);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_773_);
v___x_767_ = v___x_765_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_dec(v___x_765_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 1);
lean_ctor_set(v___x_767_, 0, v_a_764_);
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_764_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_787_, lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_787_, v_x_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_795_, lean_object* v_checkType_796_, uint8_t v_safety_797_, uint8_t v_checkMeta_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_804_; lean_object* v_env_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_804_ = lean_st_ref_get(v_a_802_);
v_env_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_env_805_);
lean_dec(v___x_804_);
v___x_806_ = lean_box(v_checkMeta_798_);
v___x_807_ = lean_box(v_safety_797_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_808_, 0, v___x_806_);
lean_closure_set(v___f_808_, 1, v_checkType_796_);
lean_closure_set(v___f_808_, 2, v___x_807_);
lean_closure_set(v___f_808_, 3, v_value_795_);
v___x_809_ = l_Lean_Environment_unlockAsync(v_env_805_);
v___x_810_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_809_, v___f_808_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_811_, lean_object* v_checkType_812_, lean_object* v_safety_813_, lean_object* v_checkMeta_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
uint8_t v_safety_boxed_820_; uint8_t v_checkMeta_boxed_821_; lean_object* v_res_822_; 
v_safety_boxed_820_ = lean_unbox(v_safety_813_);
v_checkMeta_boxed_821_ = lean_unbox(v_checkMeta_814_);
v_res_822_ = l_Lean_Meta_evalExprCore___redArg(v_value_811_, v_checkType_812_, v_safety_boxed_820_, v_checkMeta_boxed_821_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_823_, lean_object* v_value_824_, lean_object* v_checkType_825_, uint8_t v_safety_826_, uint8_t v_checkMeta_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Meta_evalExprCore___redArg(v_value_824_, v_checkType_825_, v_safety_826_, v_checkMeta_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_834_, lean_object* v_value_835_, lean_object* v_checkType_836_, lean_object* v_safety_837_, lean_object* v_checkMeta_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
uint8_t v_safety_boxed_844_; uint8_t v_checkMeta_boxed_845_; lean_object* v_res_846_; 
v_safety_boxed_844_ = lean_unbox(v_safety_837_);
v_checkMeta_boxed_845_ = lean_unbox(v_checkMeta_838_);
v_res_846_ = l_Lean_Meta_evalExprCore(v_00_u03b1_834_, v_value_835_, v_checkType_836_, v_safety_boxed_844_, v_checkMeta_boxed_845_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_861_, lean_object* v_constName_862_, uint8_t v_checkMeta_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_862_, v_checkMeta_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_870_, lean_object* v_constName_871_, lean_object* v_checkMeta_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v_checkMeta_boxed_878_; lean_object* v_res_879_; 
v_checkMeta_boxed_878_ = lean_unbox(v_checkMeta_872_);
v_res_879_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_870_, v_constName_871_, v_checkMeta_boxed_878_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_880_, lean_object* v_msg_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_888_, v_msg_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_896_, v___y_898_, v___y_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_910_, lean_object* v_env_911_, lean_object* v_x_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_911_, v_x_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_919_, lean_object* v_env_920_, lean_object* v_x_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_919_, v_env_920_, v_x_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_936_, lean_object* v_x_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_936_, v_x_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_947_, lean_object* v_type_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Meta_whnfD(v_type_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_968_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_968_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_968_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_968_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v___x_959_; 
v___x_959_ = l_Lean_Expr_isConstOf(v_a_955_, v_typeName_947_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_del_object(v___x_957_);
v___x_960_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_961_ = l_Lean_indentExpr(v_a_955_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_962_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_a_955_);
v___x_964_ = lean_box(0);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_964_);
v___x_966_ = v___x_957_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_969_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_954_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_954_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_977_, lean_object* v_type_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_977_, v_type_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v_typeName_977_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_985_, lean_object* v_value_986_, uint8_t v_safety_987_, uint8_t v_checkMeta_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___f_994_; lean_object* v___x_995_; 
v___f_994_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_994_, 0, v_typeName_985_);
v___x_995_ = l_Lean_Meta_evalExprCore___redArg(v_value_986_, v___f_994_, v_safety_987_, v_checkMeta_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_996_, lean_object* v_value_997_, lean_object* v_safety_998_, lean_object* v_checkMeta_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
uint8_t v_safety_boxed_1005_; uint8_t v_checkMeta_boxed_1006_; lean_object* v_res_1007_; 
v_safety_boxed_1005_ = lean_unbox(v_safety_998_);
v_checkMeta_boxed_1006_ = lean_unbox(v_checkMeta_999_);
v_res_1007_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_996_, v_value_997_, v_safety_boxed_1005_, v_checkMeta_boxed_1006_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1008_, lean_object* v_typeName_1009_, lean_object* v_value_1010_, uint8_t v_safety_1011_, uint8_t v_checkMeta_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1009_, v_value_1010_, v_safety_1011_, v_checkMeta_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1019_, lean_object* v_typeName_1020_, lean_object* v_value_1021_, lean_object* v_safety_1022_, lean_object* v_checkMeta_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
uint8_t v_safety_boxed_1029_; uint8_t v_checkMeta_boxed_1030_; lean_object* v_res_1031_; 
v_safety_boxed_1029_ = lean_unbox(v_safety_1022_);
v_checkMeta_boxed_1030_ = lean_unbox(v_checkMeta_1023_);
v_res_1031_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1019_, v_typeName_1020_, v_value_1021_, v_safety_boxed_1029_, v_checkMeta_boxed_1030_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1031_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1037_, lean_object* v_type_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
lean_inc_ref(v_expectedType_1037_);
lean_inc_ref(v_type_1038_);
v___x_1044_ = l_Lean_Meta_isExprDefEq(v_type_1038_, v_expectedType_1037_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1069_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1069_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1069_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_unbox(v_a_1045_);
lean_dec(v_a_1045_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_del_object(v___x_1047_);
v___x_1050_ = lean_box(0);
v___x_1051_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1052_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1038_, v_expectedType_1037_, v___x_1050_, v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v_a_1053_);
v___x_1056_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1055_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1056_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1052_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1052_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec_ref(v_type_1038_);
lean_dec_ref(v_expectedType_1037_);
v___x_1065_ = lean_box(0);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1065_);
v___x_1067_ = v___x_1047_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v_type_1038_);
lean_dec_ref(v_expectedType_1037_);
v_a_1070_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1044_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1044_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1078_, lean_object* v_type_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1078_, v_type_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1086_, lean_object* v_value_1087_, uint8_t v_safety_1088_, uint8_t v_checkMeta_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; 
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1095_, 0, v_expectedType_1086_);
v___x_1096_ = l_Lean_Meta_evalExprCore___redArg(v_value_1087_, v___f_1095_, v_safety_1088_, v_checkMeta_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1097_, lean_object* v_value_1098_, lean_object* v_safety_1099_, lean_object* v_checkMeta_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
uint8_t v_safety_boxed_1106_; uint8_t v_checkMeta_boxed_1107_; lean_object* v_res_1108_; 
v_safety_boxed_1106_ = lean_unbox(v_safety_1099_);
v_checkMeta_boxed_1107_ = lean_unbox(v_checkMeta_1100_);
v_res_1108_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1097_, v_value_1098_, v_safety_boxed_1106_, v_checkMeta_boxed_1107_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1109_, lean_object* v_expectedType_1110_, lean_object* v_value_1111_, uint8_t v_safety_1112_, uint8_t v_checkMeta_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1110_, v_value_1111_, v_safety_1112_, v_checkMeta_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_expectedType_1121_, lean_object* v_value_1122_, lean_object* v_safety_1123_, lean_object* v_checkMeta_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
uint8_t v_safety_boxed_1130_; uint8_t v_checkMeta_boxed_1131_; lean_object* v_res_1132_; 
v_safety_boxed_1130_ = lean_unbox(v_safety_1123_);
v_checkMeta_boxed_1131_ = lean_unbox(v_checkMeta_1124_);
v_res_1132_ = l_Lean_Meta_evalExpr(v_00_u03b1_1120_, v_expectedType_1121_, v_value_1122_, v_safety_boxed_1130_, v_checkMeta_boxed_1131_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
return v_res_1132_;
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

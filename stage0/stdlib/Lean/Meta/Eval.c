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
lean_object* v___y_281_; uint8_t v___y_282_; lean_object* v___y_283_; uint8_t v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v_fileName_290_; lean_object* v_fileMap_291_; lean_object* v_currRecDepth_292_; lean_object* v_ref_293_; lean_object* v_currNamespace_294_; lean_object* v_openDecls_295_; lean_object* v_initHeartbeats_296_; lean_object* v_maxHeartbeats_297_; lean_object* v_quotContext_298_; lean_object* v_currMacroScope_299_; lean_object* v_cancelTk_x3f_300_; uint8_t v_suppressElabErrors_301_; lean_object* v_inheritedTraceOptions_302_; lean_object* v___y_303_; lean_object* v___y_317_; uint8_t v___y_318_; lean_object* v___y_319_; uint8_t v___y_320_; uint8_t v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; uint8_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; uint8_t v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; uint8_t v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; uint8_t v___y_354_; lean_object* v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; uint8_t v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; uint8_t v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; uint8_t v___y_430_; uint8_t v___y_431_; lean_object* v___y_452_; uint8_t v___y_453_; lean_object* v___y_454_; uint8_t v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; uint8_t v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; uint8_t v___y_499_; lean_object* v___y_500_; uint8_t v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v_nextMacroScope_666_; lean_object* v_ngen_667_; lean_object* v_auxDeclNGen_668_; lean_object* v_traceState_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v___y_673_; lean_object* v___x_692_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_692_ = lean_st_ref_get(v___y_278_);
lean_inc_ref(v_value_274_);
v___x_705_ = l_Lean_Expr_getUsedConstants(v_value_274_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_array_get_size(v___x_705_);
v___x_708_ = lean_nat_dec_lt(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_dec_ref(v___x_705_);
lean_dec(v___x_692_);
goto v___jp_693_;
}
else
{
if (v___x_708_ == 0)
{
lean_dec_ref(v___x_705_);
lean_dec(v___x_692_);
goto v___jp_693_;
}
else
{
lean_object* v_env_709_; size_t v___x_710_; size_t v___x_711_; uint8_t v___x_712_; 
v_env_709_ = lean_ctor_get(v___x_692_, 0);
lean_inc_ref(v_env_709_);
lean_dec(v___x_692_);
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_707_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_709_, v___x_707_, v___x_705_, v___x_710_, v___x_711_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v_env_709_);
if (v___x_712_ == 0)
{
goto v___jp_693_;
}
else
{
v___y_620_ = v___y_275_;
v___y_621_ = v___y_276_;
v___y_622_ = v___y_277_;
v___y_623_ = v___y_278_;
goto v___jp_619_;
}
}
}
v___jp_280_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_287_, v___y_289_);
v___x_305_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_305_, 0, v_fileName_290_);
lean_ctor_set(v___x_305_, 1, v_fileMap_291_);
lean_ctor_set(v___x_305_, 2, v___y_287_);
lean_ctor_set(v___x_305_, 3, v_currRecDepth_292_);
lean_ctor_set(v___x_305_, 4, v___x_304_);
lean_ctor_set(v___x_305_, 5, v_ref_293_);
lean_ctor_set(v___x_305_, 6, v_currNamespace_294_);
lean_ctor_set(v___x_305_, 7, v_openDecls_295_);
lean_ctor_set(v___x_305_, 8, v_initHeartbeats_296_);
lean_ctor_set(v___x_305_, 9, v_maxHeartbeats_297_);
lean_ctor_set(v___x_305_, 10, v_quotContext_298_);
lean_ctor_set(v___x_305_, 11, v_currMacroScope_299_);
lean_ctor_set(v___x_305_, 12, v_cancelTk_x3f_300_);
lean_ctor_set(v___x_305_, 13, v_inheritedTraceOptions_302_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*14, v___y_285_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*14 + 1, v_suppressElabErrors_301_);
v___x_306_ = l_Lean_addAndCompile(v___y_286_, v___y_284_, v___y_282_, v___x_305_, v___y_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; 
lean_dec_ref_known(v___x_306_, 1);
v___x_307_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_281_, v_checkMeta_271_, v___y_288_, v___y_283_, v___x_305_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref_known(v___x_305_, 14);
lean_dec(v___y_283_);
lean_dec_ref(v___y_288_);
return v___x_307_;
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref_known(v___x_305_, 14);
lean_dec(v___y_303_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_283_);
lean_dec(v___y_281_);
v_a_308_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
v___jp_316_:
{
lean_object* v_fileName_328_; lean_object* v_fileMap_329_; lean_object* v_currRecDepth_330_; lean_object* v_ref_331_; lean_object* v_currNamespace_332_; lean_object* v_openDecls_333_; lean_object* v_initHeartbeats_334_; lean_object* v_maxHeartbeats_335_; lean_object* v_quotContext_336_; lean_object* v_currMacroScope_337_; lean_object* v_cancelTk_x3f_338_; uint8_t v_suppressElabErrors_339_; lean_object* v_inheritedTraceOptions_340_; 
v_fileName_328_ = lean_ctor_get(v___y_326_, 0);
lean_inc_ref(v_fileName_328_);
v_fileMap_329_ = lean_ctor_get(v___y_326_, 1);
lean_inc_ref(v_fileMap_329_);
v_currRecDepth_330_ = lean_ctor_get(v___y_326_, 3);
lean_inc(v_currRecDepth_330_);
v_ref_331_ = lean_ctor_get(v___y_326_, 5);
lean_inc(v_ref_331_);
v_currNamespace_332_ = lean_ctor_get(v___y_326_, 6);
lean_inc(v_currNamespace_332_);
v_openDecls_333_ = lean_ctor_get(v___y_326_, 7);
lean_inc(v_openDecls_333_);
v_initHeartbeats_334_ = lean_ctor_get(v___y_326_, 8);
lean_inc(v_initHeartbeats_334_);
v_maxHeartbeats_335_ = lean_ctor_get(v___y_326_, 9);
lean_inc(v_maxHeartbeats_335_);
v_quotContext_336_ = lean_ctor_get(v___y_326_, 10);
lean_inc(v_quotContext_336_);
v_currMacroScope_337_ = lean_ctor_get(v___y_326_, 11);
lean_inc(v_currMacroScope_337_);
v_cancelTk_x3f_338_ = lean_ctor_get(v___y_326_, 12);
lean_inc(v_cancelTk_x3f_338_);
v_suppressElabErrors_339_ = lean_ctor_get_uint8(v___y_326_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_340_ = lean_ctor_get(v___y_326_, 13);
lean_inc_ref(v_inheritedTraceOptions_340_);
lean_dec_ref(v___y_326_);
v___y_281_ = v___y_317_;
v___y_282_ = v___y_318_;
v___y_283_ = v___y_319_;
v___y_284_ = v___y_320_;
v___y_285_ = v___y_321_;
v___y_286_ = v___y_322_;
v___y_287_ = v___y_323_;
v___y_288_ = v___y_324_;
v___y_289_ = v___y_325_;
v_fileName_290_ = v_fileName_328_;
v_fileMap_291_ = v_fileMap_329_;
v_currRecDepth_292_ = v_currRecDepth_330_;
v_ref_293_ = v_ref_331_;
v_currNamespace_294_ = v_currNamespace_332_;
v_openDecls_295_ = v_openDecls_333_;
v_initHeartbeats_296_ = v_initHeartbeats_334_;
v_maxHeartbeats_297_ = v_maxHeartbeats_335_;
v_quotContext_298_ = v_quotContext_336_;
v_currMacroScope_299_ = v_currMacroScope_337_;
v_cancelTk_x3f_300_ = v_cancelTk_x3f_338_;
v_suppressElabErrors_301_ = v_suppressElabErrors_339_;
v_inheritedTraceOptions_302_ = v_inheritedTraceOptions_340_;
v___y_303_ = v___y_327_;
goto v___jp_280_;
}
v___jp_341_:
{
if (v___y_354_ == 0)
{
lean_object* v___x_355_; lean_object* v_env_356_; lean_object* v_nextMacroScope_357_; lean_object* v_ngen_358_; lean_object* v_auxDeclNGen_359_; lean_object* v_traceState_360_; lean_object* v_messages_361_; lean_object* v_infoState_362_; lean_object* v_snapshotTasks_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_372_; 
v___x_355_ = lean_st_ref_take(v___y_344_);
v_env_356_ = lean_ctor_get(v___x_355_, 0);
v_nextMacroScope_357_ = lean_ctor_get(v___x_355_, 1);
v_ngen_358_ = lean_ctor_get(v___x_355_, 2);
v_auxDeclNGen_359_ = lean_ctor_get(v___x_355_, 3);
v_traceState_360_ = lean_ctor_get(v___x_355_, 4);
v_messages_361_ = lean_ctor_get(v___x_355_, 6);
v_infoState_362_ = lean_ctor_get(v___x_355_, 7);
v_snapshotTasks_363_ = lean_ctor_get(v___x_355_, 8);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_355_, 5);
lean_dec(v_unused_373_);
v___x_365_ = v___x_355_;
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snapshotTasks_363_);
lean_inc(v_infoState_362_);
lean_inc(v_messages_361_);
lean_inc(v_traceState_360_);
lean_inc(v_auxDeclNGen_359_);
lean_inc(v_ngen_358_);
lean_inc(v_nextMacroScope_357_);
lean_inc(v_env_356_);
lean_dec(v___x_355_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = l_Lean_Kernel_enableDiag(v_env_356_, v___y_345_);
lean_inc_ref(v___y_350_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 5, v___y_350_);
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_nextMacroScope_357_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_ngen_358_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_auxDeclNGen_359_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_traceState_360_);
lean_ctor_set(v_reuseFailAlloc_371_, 5, v___y_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 6, v_messages_361_);
lean_ctor_set(v_reuseFailAlloc_371_, 7, v_infoState_362_);
lean_ctor_set(v_reuseFailAlloc_371_, 8, v_snapshotTasks_363_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; 
v___x_370_ = lean_st_ref_put(v___y_344_, v___x_369_);
v___y_317_ = v___y_348_;
v___y_318_ = v___y_342_;
v___y_319_ = v___y_343_;
v___y_320_ = v___y_349_;
v___y_321_ = v___y_345_;
v___y_322_ = v___y_346_;
v___y_323_ = v___y_351_;
v___y_324_ = v___y_353_;
v___y_325_ = v___y_347_;
v___y_326_ = v___y_352_;
v___y_327_ = v___y_344_;
goto v___jp_316_;
}
}
}
else
{
v___y_317_ = v___y_348_;
v___y_318_ = v___y_342_;
v___y_319_ = v___y_343_;
v___y_320_ = v___y_349_;
v___y_321_ = v___y_345_;
v___y_322_ = v___y_346_;
v___y_323_ = v___y_351_;
v___y_324_ = v___y_353_;
v___y_325_ = v___y_347_;
v___y_326_ = v___y_352_;
v___y_327_ = v___y_344_;
goto v___jp_316_;
}
}
v___jp_374_:
{
lean_object* v___x_388_; lean_object* v_fileName_389_; lean_object* v_fileMap_390_; lean_object* v_currRecDepth_391_; lean_object* v_ref_392_; lean_object* v_currNamespace_393_; lean_object* v_openDecls_394_; lean_object* v_initHeartbeats_395_; lean_object* v_maxHeartbeats_396_; lean_object* v_quotContext_397_; lean_object* v_currMacroScope_398_; lean_object* v_cancelTk_x3f_399_; uint8_t v_suppressElabErrors_400_; lean_object* v_inheritedTraceOptions_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_414_; 
v___x_388_ = lean_st_ref_get(v___y_387_);
v_fileName_389_ = lean_ctor_get(v___y_386_, 0);
v_fileMap_390_ = lean_ctor_get(v___y_386_, 1);
v_currRecDepth_391_ = lean_ctor_get(v___y_386_, 3);
v_ref_392_ = lean_ctor_get(v___y_386_, 5);
v_currNamespace_393_ = lean_ctor_get(v___y_386_, 6);
v_openDecls_394_ = lean_ctor_get(v___y_386_, 7);
v_initHeartbeats_395_ = lean_ctor_get(v___y_386_, 8);
v_maxHeartbeats_396_ = lean_ctor_get(v___y_386_, 9);
v_quotContext_397_ = lean_ctor_get(v___y_386_, 10);
v_currMacroScope_398_ = lean_ctor_get(v___y_386_, 11);
v_cancelTk_x3f_399_ = lean_ctor_get(v___y_386_, 12);
v_suppressElabErrors_400_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_401_ = lean_ctor_get(v___y_386_, 13);
v_isSharedCheck_414_ = !lean_is_exclusive(v___y_386_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_415_ = lean_ctor_get(v___y_386_, 4);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v___y_386_, 2);
lean_dec(v_unused_416_);
v___x_403_ = v___y_386_;
v_isShared_404_ = v_isSharedCheck_414_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_inheritedTraceOptions_401_);
lean_inc(v_cancelTk_x3f_399_);
lean_inc(v_currMacroScope_398_);
lean_inc(v_quotContext_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc(v_ref_392_);
lean_inc(v_currRecDepth_391_);
lean_inc(v_fileMap_390_);
lean_inc(v_fileName_389_);
lean_dec(v___y_386_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_414_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_env_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v_env_405_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_405_);
lean_dec(v___x_388_);
v___x_406_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_383_, v___y_385_);
lean_inc_ref(v_inheritedTraceOptions_401_);
lean_inc(v_cancelTk_x3f_399_);
lean_inc(v_currMacroScope_398_);
lean_inc(v_quotContext_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc(v_ref_392_);
lean_inc(v_currRecDepth_391_);
lean_inc_ref(v___y_383_);
lean_inc_ref(v_fileMap_390_);
lean_inc_ref(v_fileName_389_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 4, v___x_406_);
lean_ctor_set(v___x_403_, 2, v___y_383_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_fileName_389_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_fileMap_390_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v___y_383_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_currRecDepth_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_ref_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_currNamespace_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_openDecls_394_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_initHeartbeats_395_);
lean_ctor_set(v_reuseFailAlloc_413_, 9, v_maxHeartbeats_396_);
lean_ctor_set(v_reuseFailAlloc_413_, 10, v_quotContext_397_);
lean_ctor_set(v_reuseFailAlloc_413_, 11, v_currMacroScope_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 12, v_cancelTk_x3f_399_);
lean_ctor_set(v_reuseFailAlloc_413_, 13, v_inheritedTraceOptions_401_);
lean_ctor_set_uint8(v_reuseFailAlloc_413_, sizeof(void*)*14 + 1, v_suppressElabErrors_400_);
v___x_408_ = v_reuseFailAlloc_413_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; uint8_t v___x_412_; 
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*14, v___y_384_);
v___x_409_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_410_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_383_, v___x_409_, v___y_378_);
v___x_411_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_410_, v___y_382_);
v___x_412_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_405_);
lean_dec_ref(v_env_405_);
if (v___x_411_ == 0)
{
if (v___x_412_ == 0)
{
lean_dec_ref(v___x_408_);
v___y_281_ = v___y_375_;
v___y_282_ = v___y_376_;
v___y_283_ = v___y_377_;
v___y_284_ = v___y_378_;
v___y_285_ = v___x_411_;
v___y_286_ = v___y_380_;
v___y_287_ = v___x_410_;
v___y_288_ = v___y_381_;
v___y_289_ = v___y_385_;
v_fileName_290_ = v_fileName_389_;
v_fileMap_291_ = v_fileMap_390_;
v_currRecDepth_292_ = v_currRecDepth_391_;
v_ref_293_ = v_ref_392_;
v_currNamespace_294_ = v_currNamespace_393_;
v_openDecls_295_ = v_openDecls_394_;
v_initHeartbeats_296_ = v_initHeartbeats_395_;
v_maxHeartbeats_297_ = v_maxHeartbeats_396_;
v_quotContext_298_ = v_quotContext_397_;
v_currMacroScope_299_ = v_currMacroScope_398_;
v_cancelTk_x3f_300_ = v_cancelTk_x3f_399_;
v_suppressElabErrors_301_ = v_suppressElabErrors_400_;
v_inheritedTraceOptions_302_ = v_inheritedTraceOptions_401_;
v___y_303_ = v___y_387_;
goto v___jp_280_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_401_);
lean_dec(v_cancelTk_x3f_399_);
lean_dec(v_currMacroScope_398_);
lean_dec(v_quotContext_397_);
lean_dec(v_maxHeartbeats_396_);
lean_dec(v_initHeartbeats_395_);
lean_dec(v_openDecls_394_);
lean_dec(v_currNamespace_393_);
lean_dec(v_ref_392_);
lean_dec(v_currRecDepth_391_);
lean_dec_ref(v_fileMap_390_);
lean_dec_ref(v_fileName_389_);
v___y_342_ = v___y_376_;
v___y_343_ = v___y_377_;
v___y_344_ = v___y_387_;
v___y_345_ = v___x_411_;
v___y_346_ = v___y_380_;
v___y_347_ = v___y_385_;
v___y_348_ = v___y_375_;
v___y_349_ = v___y_378_;
v___y_350_ = v___y_379_;
v___y_351_ = v___x_410_;
v___y_352_ = v___x_408_;
v___y_353_ = v___y_381_;
v___y_354_ = v___x_411_;
goto v___jp_341_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_401_);
lean_dec(v_cancelTk_x3f_399_);
lean_dec(v_currMacroScope_398_);
lean_dec(v_quotContext_397_);
lean_dec(v_maxHeartbeats_396_);
lean_dec(v_initHeartbeats_395_);
lean_dec(v_openDecls_394_);
lean_dec(v_currNamespace_393_);
lean_dec(v_ref_392_);
lean_dec(v_currRecDepth_391_);
lean_dec_ref(v_fileMap_390_);
lean_dec_ref(v_fileName_389_);
v___y_342_ = v___y_376_;
v___y_343_ = v___y_377_;
v___y_344_ = v___y_387_;
v___y_345_ = v___x_411_;
v___y_346_ = v___y_380_;
v___y_347_ = v___y_385_;
v___y_348_ = v___y_375_;
v___y_349_ = v___y_378_;
v___y_350_ = v___y_379_;
v___y_351_ = v___x_410_;
v___y_352_ = v___x_408_;
v___y_353_ = v___y_381_;
v___y_354_ = v___x_412_;
goto v___jp_341_;
}
}
}
}
v___jp_417_:
{
if (v___y_431_ == 0)
{
lean_object* v___x_432_; lean_object* v_env_433_; lean_object* v_nextMacroScope_434_; lean_object* v_ngen_435_; lean_object* v_auxDeclNGen_436_; lean_object* v_traceState_437_; lean_object* v_messages_438_; lean_object* v_infoState_439_; lean_object* v_snapshotTasks_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_449_; 
v___x_432_ = lean_st_ref_take(v___y_421_);
v_env_433_ = lean_ctor_get(v___x_432_, 0);
v_nextMacroScope_434_ = lean_ctor_get(v___x_432_, 1);
v_ngen_435_ = lean_ctor_get(v___x_432_, 2);
v_auxDeclNGen_436_ = lean_ctor_get(v___x_432_, 3);
v_traceState_437_ = lean_ctor_get(v___x_432_, 4);
v_messages_438_ = lean_ctor_get(v___x_432_, 6);
v_infoState_439_ = lean_ctor_get(v___x_432_, 7);
v_snapshotTasks_440_ = lean_ctor_get(v___x_432_, 8);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_432_, 5);
lean_dec(v_unused_450_);
v___x_442_ = v___x_432_;
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snapshotTasks_440_);
lean_inc(v_infoState_439_);
lean_inc(v_messages_438_);
lean_inc(v_traceState_437_);
lean_inc(v_auxDeclNGen_436_);
lean_inc(v_ngen_435_);
lean_inc(v_nextMacroScope_434_);
lean_inc(v_env_433_);
lean_dec(v___x_432_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = l_Lean_Kernel_enableDiag(v_env_433_, v___y_430_);
lean_inc_ref(v___y_426_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 5, v___y_426_);
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_nextMacroScope_434_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_ngen_435_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_auxDeclNGen_436_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_traceState_437_);
lean_ctor_set(v_reuseFailAlloc_448_, 5, v___y_426_);
lean_ctor_set(v_reuseFailAlloc_448_, 6, v_messages_438_);
lean_ctor_set(v_reuseFailAlloc_448_, 7, v_infoState_439_);
lean_ctor_set(v_reuseFailAlloc_448_, 8, v_snapshotTasks_440_);
v___x_446_ = v_reuseFailAlloc_448_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; 
v___x_447_ = lean_st_ref_put(v___y_421_, v___x_446_);
v___y_375_ = v___y_424_;
v___y_376_ = v___y_418_;
v___y_377_ = v___y_419_;
v___y_378_ = v___y_425_;
v___y_379_ = v___y_426_;
v___y_380_ = v___y_422_;
v___y_381_ = v___y_427_;
v___y_382_ = v___y_428_;
v___y_383_ = v___y_429_;
v___y_384_ = v___y_430_;
v___y_385_ = v___y_423_;
v___y_386_ = v___y_420_;
v___y_387_ = v___y_421_;
goto v___jp_374_;
}
}
}
else
{
v___y_375_ = v___y_424_;
v___y_376_ = v___y_418_;
v___y_377_ = v___y_419_;
v___y_378_ = v___y_425_;
v___y_379_ = v___y_426_;
v___y_380_ = v___y_422_;
v___y_381_ = v___y_427_;
v___y_382_ = v___y_428_;
v___y_383_ = v___y_429_;
v___y_384_ = v___y_430_;
v___y_385_ = v___y_423_;
v___y_386_ = v___y_420_;
v___y_387_ = v___y_421_;
goto v___jp_374_;
}
}
v___jp_451_:
{
lean_object* v___x_464_; lean_object* v_fileName_465_; lean_object* v_fileMap_466_; lean_object* v_currRecDepth_467_; lean_object* v_ref_468_; lean_object* v_currNamespace_469_; lean_object* v_openDecls_470_; lean_object* v_initHeartbeats_471_; lean_object* v_maxHeartbeats_472_; lean_object* v_quotContext_473_; lean_object* v_currMacroScope_474_; lean_object* v_cancelTk_x3f_475_; uint8_t v_suppressElabErrors_476_; lean_object* v_inheritedTraceOptions_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_491_; 
v___x_464_ = lean_st_ref_get(v___y_463_);
v_fileName_465_ = lean_ctor_get(v___y_462_, 0);
v_fileMap_466_ = lean_ctor_get(v___y_462_, 1);
v_currRecDepth_467_ = lean_ctor_get(v___y_462_, 3);
v_ref_468_ = lean_ctor_get(v___y_462_, 5);
v_currNamespace_469_ = lean_ctor_get(v___y_462_, 6);
v_openDecls_470_ = lean_ctor_get(v___y_462_, 7);
v_initHeartbeats_471_ = lean_ctor_get(v___y_462_, 8);
v_maxHeartbeats_472_ = lean_ctor_get(v___y_462_, 9);
v_quotContext_473_ = lean_ctor_get(v___y_462_, 10);
v_currMacroScope_474_ = lean_ctor_get(v___y_462_, 11);
v_cancelTk_x3f_475_ = lean_ctor_get(v___y_462_, 12);
v_suppressElabErrors_476_ = lean_ctor_get_uint8(v___y_462_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_477_ = lean_ctor_get(v___y_462_, 13);
v_isSharedCheck_491_ = !lean_is_exclusive(v___y_462_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v___y_462_, 4);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v___y_462_, 2);
lean_dec(v_unused_493_);
v___x_479_ = v___y_462_;
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_inheritedTraceOptions_477_);
lean_inc(v_cancelTk_x3f_475_);
lean_inc(v_currMacroScope_474_);
lean_inc(v_quotContext_473_);
lean_inc(v_maxHeartbeats_472_);
lean_inc(v_initHeartbeats_471_);
lean_inc(v_openDecls_470_);
lean_inc(v_currNamespace_469_);
lean_inc(v_ref_468_);
lean_inc(v_currRecDepth_467_);
lean_inc(v_fileMap_466_);
lean_inc(v_fileName_465_);
lean_dec(v___y_462_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_env_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v_env_481_ = lean_ctor_get(v___x_464_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_464_);
v___x_482_ = l_Lean_maxRecDepth;
v___x_483_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_456_, v___x_482_);
lean_inc_ref(v___y_456_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_483_);
lean_ctor_set(v___x_479_, 2, v___y_456_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_fileName_465_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_fileMap_466_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v___y_456_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_currRecDepth_467_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_490_, 5, v_ref_468_);
lean_ctor_set(v_reuseFailAlloc_490_, 6, v_currNamespace_469_);
lean_ctor_set(v_reuseFailAlloc_490_, 7, v_openDecls_470_);
lean_ctor_set(v_reuseFailAlloc_490_, 8, v_initHeartbeats_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 9, v_maxHeartbeats_472_);
lean_ctor_set(v_reuseFailAlloc_490_, 10, v_quotContext_473_);
lean_ctor_set(v_reuseFailAlloc_490_, 11, v_currMacroScope_474_);
lean_ctor_set(v_reuseFailAlloc_490_, 12, v_cancelTk_x3f_475_);
lean_ctor_set(v_reuseFailAlloc_490_, 13, v_inheritedTraceOptions_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*14 + 1, v_suppressElabErrors_476_);
v___x_485_ = v_reuseFailAlloc_490_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; uint8_t v___x_489_; 
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*14, v___y_461_);
v___x_486_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_487_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_456_, v___x_486_, v___y_453_);
v___x_488_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_487_, v___y_460_);
v___x_489_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_481_);
lean_dec_ref(v_env_481_);
if (v___x_488_ == 0)
{
if (v___x_489_ == 0)
{
v___y_375_ = v___y_452_;
v___y_376_ = v___y_453_;
v___y_377_ = v___y_454_;
v___y_378_ = v___y_455_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_457_;
v___y_381_ = v___y_459_;
v___y_382_ = v___y_460_;
v___y_383_ = v___x_487_;
v___y_384_ = v___x_488_;
v___y_385_ = v___x_482_;
v___y_386_ = v___x_485_;
v___y_387_ = v___y_463_;
goto v___jp_374_;
}
else
{
v___y_418_ = v___y_453_;
v___y_419_ = v___y_454_;
v___y_420_ = v___x_485_;
v___y_421_ = v___y_463_;
v___y_422_ = v___y_457_;
v___y_423_ = v___x_482_;
v___y_424_ = v___y_452_;
v___y_425_ = v___y_455_;
v___y_426_ = v___y_458_;
v___y_427_ = v___y_459_;
v___y_428_ = v___y_460_;
v___y_429_ = v___x_487_;
v___y_430_ = v___x_488_;
v___y_431_ = v___x_488_;
goto v___jp_417_;
}
}
else
{
v___y_418_ = v___y_453_;
v___y_419_ = v___y_454_;
v___y_420_ = v___x_485_;
v___y_421_ = v___y_463_;
v___y_422_ = v___y_457_;
v___y_423_ = v___x_482_;
v___y_424_ = v___y_452_;
v___y_425_ = v___y_455_;
v___y_426_ = v___y_458_;
v___y_427_ = v___y_459_;
v___y_428_ = v___y_460_;
v___y_429_ = v___x_487_;
v___y_430_ = v___x_488_;
v___y_431_ = v___x_489_;
goto v___jp_417_;
}
}
}
}
v___jp_494_:
{
if (v___y_507_ == 0)
{
lean_object* v___x_508_; lean_object* v_env_509_; lean_object* v_nextMacroScope_510_; lean_object* v_ngen_511_; lean_object* v_auxDeclNGen_512_; lean_object* v_traceState_513_; lean_object* v_messages_514_; lean_object* v_infoState_515_; lean_object* v_snapshotTasks_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v___x_508_ = lean_st_ref_take(v___y_506_);
v_env_509_ = lean_ctor_get(v___x_508_, 0);
v_nextMacroScope_510_ = lean_ctor_get(v___x_508_, 1);
v_ngen_511_ = lean_ctor_get(v___x_508_, 2);
v_auxDeclNGen_512_ = lean_ctor_get(v___x_508_, 3);
v_traceState_513_ = lean_ctor_get(v___x_508_, 4);
v_messages_514_ = lean_ctor_get(v___x_508_, 6);
v_infoState_515_ = lean_ctor_get(v___x_508_, 7);
v_snapshotTasks_516_ = lean_ctor_get(v___x_508_, 8);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v___x_508_, 5);
lean_dec(v_unused_526_);
v___x_518_ = v___x_508_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_snapshotTasks_516_);
lean_inc(v_infoState_515_);
lean_inc(v_messages_514_);
lean_inc(v_traceState_513_);
lean_inc(v_auxDeclNGen_512_);
lean_inc(v_ngen_511_);
lean_inc(v_nextMacroScope_510_);
lean_inc(v_env_509_);
lean_dec(v___x_508_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = l_Lean_Kernel_enableDiag(v_env_509_, v___y_499_);
lean_inc_ref(v___y_503_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 5, v___y_503_);
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_nextMacroScope_510_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_ngen_511_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_auxDeclNGen_512_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_traceState_513_);
lean_ctor_set(v_reuseFailAlloc_524_, 5, v___y_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 6, v_messages_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 7, v_infoState_515_);
lean_ctor_set(v_reuseFailAlloc_524_, 8, v_snapshotTasks_516_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_st_ref_put(v___y_506_, v___x_522_);
v___y_452_ = v___y_500_;
v___y_453_ = v___y_495_;
v___y_454_ = v___y_496_;
v___y_455_ = v___y_501_;
v___y_456_ = v___y_497_;
v___y_457_ = v___y_498_;
v___y_458_ = v___y_503_;
v___y_459_ = v___y_504_;
v___y_460_ = v___y_505_;
v___y_461_ = v___y_499_;
v___y_462_ = v___y_502_;
v___y_463_ = v___y_506_;
goto v___jp_451_;
}
}
}
else
{
v___y_452_ = v___y_500_;
v___y_453_ = v___y_495_;
v___y_454_ = v___y_496_;
v___y_455_ = v___y_501_;
v___y_456_ = v___y_497_;
v___y_457_ = v___y_498_;
v___y_458_ = v___y_503_;
v___y_459_ = v___y_504_;
v___y_460_ = v___y_505_;
v___y_461_ = v___y_499_;
v___y_462_ = v___y_502_;
v___y_463_ = v___y_506_;
goto v___jp_451_;
}
}
v___jp_527_:
{
lean_object* v___x_536_; 
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc_ref(v___y_531_);
v___x_536_ = lean_infer_type(v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc_n(v_a_537_, 2);
lean_dec_ref_known(v___x_536_, 1);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
v___x_538_ = lean_apply_6(v_checkType_272_, v_a_537_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, lean_box(0));
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; lean_object* v_env_540_; lean_object* v_nextMacroScope_541_; lean_object* v_ngen_542_; lean_object* v_auxDeclNGen_543_; lean_object* v_traceState_544_; lean_object* v_messages_545_; lean_object* v_infoState_546_; lean_object* v_snapshotTasks_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref_known(v___x_538_, 1);
v___x_539_ = lean_st_ref_take(v___y_535_);
v_env_540_ = lean_ctor_get(v___x_539_, 0);
v_nextMacroScope_541_ = lean_ctor_get(v___x_539_, 1);
v_ngen_542_ = lean_ctor_get(v___x_539_, 2);
v_auxDeclNGen_543_ = lean_ctor_get(v___x_539_, 3);
v_traceState_544_ = lean_ctor_get(v___x_539_, 4);
v_messages_545_ = lean_ctor_get(v___x_539_, 6);
v_infoState_546_ = lean_ctor_get(v___x_539_, 7);
v_snapshotTasks_547_ = lean_ctor_get(v___x_539_, 8);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_539_, 5);
lean_dec(v_unused_602_);
v___x_549_ = v___x_539_;
v_isShared_550_ = v_isSharedCheck_601_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snapshotTasks_547_);
lean_inc(v_infoState_546_);
lean_inc(v_messages_545_);
lean_inc(v_traceState_544_);
lean_inc(v_auxDeclNGen_543_);
lean_inc(v_ngen_542_);
lean_inc(v_nextMacroScope_541_);
lean_inc(v_env_540_);
lean_dec(v___x_539_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_601_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_551_ = lean_array_to_list(v___y_530_);
lean_inc_n(v___y_528_, 3);
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v___y_528_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
lean_ctor_set(v___x_552_, 2, v_a_537_);
lean_inc(v___y_529_);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v___y_528_);
lean_ctor_set(v___x_553_, 1, v___y_529_);
v___x_554_ = l_Lean_markMeta(v_env_540_, v___y_528_);
v___x_555_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 5, v___x_555_);
lean_ctor_set(v___x_549_, 0, v___x_554_);
v___x_557_ = v___x_549_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_nextMacroScope_541_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_ngen_542_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_auxDeclNGen_543_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_traceState_544_);
lean_ctor_set(v_reuseFailAlloc_600_, 5, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_600_, 6, v_messages_545_);
lean_ctor_set(v_reuseFailAlloc_600_, 7, v_infoState_546_);
lean_ctor_set(v_reuseFailAlloc_600_, 8, v_snapshotTasks_547_);
v___x_557_ = v_reuseFailAlloc_600_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_mctx_560_; lean_object* v_zetaDeltaFVarIds_561_; lean_object* v_postponed_562_; lean_object* v_diag_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_598_; 
v___x_558_ = lean_st_ref_put(v___y_535_, v___x_557_);
v___x_559_ = lean_st_ref_take(v___y_533_);
v_mctx_560_ = lean_ctor_get(v___x_559_, 0);
v_zetaDeltaFVarIds_561_ = lean_ctor_get(v___x_559_, 2);
v_postponed_562_ = lean_ctor_get(v___x_559_, 3);
v_diag_563_ = lean_ctor_get(v___x_559_, 4);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_559_, 1);
lean_dec(v_unused_599_);
v___x_565_ = v___x_559_;
v_isShared_566_ = v_isSharedCheck_598_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_diag_563_);
lean_inc(v_postponed_562_);
lean_inc(v_zetaDeltaFVarIds_561_);
lean_inc(v_mctx_560_);
lean_dec(v___x_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_598_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_mctx_560_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_zetaDeltaFVarIds_561_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_postponed_562_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_diag_563_);
v___x_569_ = v_reuseFailAlloc_597_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_env_572_; lean_object* v_checked_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_570_ = lean_st_ref_put(v___y_533_, v___x_569_);
v___x_571_ = lean_st_ref_get(v___y_535_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
v_checked_573_ = lean_ctor_get(v_env_572_, 2);
lean_inc_ref(v_checked_573_);
lean_dec_ref(v_env_572_);
v___x_574_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_575_ = l_Lean_traceBlock___redArg(v___x_574_, v_checked_573_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; lean_object* v_options_577_; lean_object* v_env_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; uint8_t v___x_588_; 
lean_dec_ref_known(v___x_575_, 1);
v___x_576_ = lean_st_ref_get(v___y_535_);
v_options_577_ = lean_ctor_get(v___y_534_, 2);
v_env_578_ = lean_ctor_get(v___x_576_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_580_, 0, v___x_552_);
lean_ctor_set(v___x_580_, 1, v___y_531_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
lean_ctor_set(v___x_580_, 3, v___x_553_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*4, v_safety_273_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = 1;
v___x_583_ = 0;
v___x_584_ = l_Lean_Elab_async;
lean_inc_ref(v_options_577_);
v___x_585_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_577_, v___x_584_, v___x_583_);
v___x_586_ = l_Lean_diagnostics;
v___x_587_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_585_, v___x_586_);
v___x_588_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_578_);
lean_dec_ref(v_env_578_);
if (v___x_587_ == 0)
{
if (v___x_588_ == 0)
{
v___y_452_ = v___y_528_;
v___y_453_ = v___x_583_;
v___y_454_ = v___y_533_;
v___y_455_ = v___x_582_;
v___y_456_ = v___x_585_;
v___y_457_ = v___x_581_;
v___y_458_ = v___x_555_;
v___y_459_ = v___y_532_;
v___y_460_ = v___x_586_;
v___y_461_ = v___x_587_;
v___y_462_ = v___y_534_;
v___y_463_ = v___y_535_;
goto v___jp_451_;
}
else
{
v___y_495_ = v___x_583_;
v___y_496_ = v___y_533_;
v___y_497_ = v___x_585_;
v___y_498_ = v___x_581_;
v___y_499_ = v___x_587_;
v___y_500_ = v___y_528_;
v___y_501_ = v___x_582_;
v___y_502_ = v___y_534_;
v___y_503_ = v___x_555_;
v___y_504_ = v___y_532_;
v___y_505_ = v___x_586_;
v___y_506_ = v___y_535_;
v___y_507_ = v___x_587_;
goto v___jp_494_;
}
}
else
{
v___y_495_ = v___x_583_;
v___y_496_ = v___y_533_;
v___y_497_ = v___x_585_;
v___y_498_ = v___x_581_;
v___y_499_ = v___x_587_;
v___y_500_ = v___y_528_;
v___y_501_ = v___x_582_;
v___y_502_ = v___y_534_;
v___y_503_ = v___x_555_;
v___y_504_ = v___y_532_;
v___y_505_ = v___x_586_;
v___y_506_ = v___y_535_;
v___y_507_ = v___x_588_;
goto v___jp_494_;
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref_known(v___x_553_, 2);
lean_dec_ref_known(v___x_552_, 3);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_528_);
v_a_589_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_575_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_575_);
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
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_a_537_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_528_);
v_a_603_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_538_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_538_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_528_);
lean_dec_ref(v_checkType_272_);
v_a_611_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_536_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_536_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
v___jp_619_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_st_ref_get(v___y_623_);
v___x_625_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_626_ = l_Lean_Core_mkFreshUserName(v___x_625_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_628_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v___x_628_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_274_, v___y_621_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v_env_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_params_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_n(v_a_629_, 2);
lean_dec_ref_known(v___x_628_, 1);
v_env_630_ = lean_ctor_get(v___x_624_, 0);
lean_inc_ref(v_env_630_);
lean_dec(v___x_624_);
v___x_631_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_632_ = l_Lean_collectLevelParams(v___x_631_, v_a_629_);
v_params_633_ = lean_ctor_get(v___x_632_, 2);
lean_inc_ref(v_params_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Lean_mkPrivateName(v_env_630_, v_a_627_);
lean_dec_ref(v_env_630_);
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_Expr_hasMVar(v_a_629_);
if (v___x_636_ == 0)
{
v___y_528_ = v___x_634_;
v___y_529_ = v___x_635_;
v___y_530_ = v_params_633_;
v___y_531_ = v_a_629_;
v___y_532_ = v___y_620_;
v___y_533_ = v___y_621_;
v___y_534_ = v___y_622_;
v___y_535_ = v___y_623_;
goto v___jp_527_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_629_);
v___x_638_ = l_Lean_indentExpr(v_a_629_);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_639_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec_ref_known(v___x_640_, 1);
v___y_528_ = v___x_634_;
v___y_529_ = v___x_635_;
v___y_530_ = v_params_633_;
v___y_531_ = v_a_629_;
v___y_532_ = v___y_620_;
v___y_533_ = v___y_621_;
v___y_534_ = v___y_622_;
v___y_535_ = v___y_623_;
goto v___jp_527_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v___x_634_);
lean_dec_ref(v_params_633_);
lean_dec(v_a_629_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_checkType_272_);
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
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
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_627_);
lean_dec(v___x_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_checkType_272_);
v_a_649_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_628_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_628_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v___x_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_value_274_);
lean_dec_ref(v_checkType_272_);
v_a_657_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_626_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_626_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
v___jp_665_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_mctx_678_; lean_object* v_zetaDeltaFVarIds_679_; lean_object* v_postponed_680_; lean_object* v_diag_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_690_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_675_, 0, v___y_673_);
lean_ctor_set(v___x_675_, 1, v_nextMacroScope_666_);
lean_ctor_set(v___x_675_, 2, v_ngen_667_);
lean_ctor_set(v___x_675_, 3, v_auxDeclNGen_668_);
lean_ctor_set(v___x_675_, 4, v_traceState_669_);
lean_ctor_set(v___x_675_, 5, v___x_674_);
lean_ctor_set(v___x_675_, 6, v_messages_670_);
lean_ctor_set(v___x_675_, 7, v_infoState_671_);
lean_ctor_set(v___x_675_, 8, v_snapshotTasks_672_);
v___x_676_ = lean_st_ref_put(v___y_278_, v___x_675_);
v___x_677_ = lean_st_ref_take(v___y_276_);
v_mctx_678_ = lean_ctor_get(v___x_677_, 0);
v_zetaDeltaFVarIds_679_ = lean_ctor_get(v___x_677_, 2);
v_postponed_680_ = lean_ctor_get(v___x_677_, 3);
v_diag_681_ = lean_ctor_get(v___x_677_, 4);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v___x_677_, 1);
lean_dec(v_unused_691_);
v___x_683_ = v___x_677_;
v_isShared_684_ = v_isSharedCheck_690_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_diag_681_);
lean_inc(v_postponed_680_);
lean_inc(v_zetaDeltaFVarIds_679_);
lean_inc(v_mctx_678_);
lean_dec(v___x_677_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_690_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_mctx_678_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_zetaDeltaFVarIds_679_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_postponed_680_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_diag_681_);
v___x_687_ = v_reuseFailAlloc_689_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; 
v___x_688_ = lean_st_ref_put(v___y_276_, v___x_687_);
v___y_620_ = v___y_275_;
v___y_621_ = v___y_276_;
v___y_622_ = v___y_277_;
v___y_623_ = v___y_278_;
goto v___jp_619_;
}
}
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_traceState_699_; lean_object* v_messages_700_; lean_object* v_infoState_701_; lean_object* v_snapshotTasks_702_; lean_object* v___x_703_; 
v___x_694_ = lean_st_ref_take(v___y_278_);
v_env_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref_n(v_env_695_, 2);
v_nextMacroScope_696_ = lean_ctor_get(v___x_694_, 1);
lean_inc(v_nextMacroScope_696_);
v_ngen_697_ = lean_ctor_get(v___x_694_, 2);
lean_inc_ref(v_ngen_697_);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_694_, 3);
lean_inc_ref(v_auxDeclNGen_698_);
v_traceState_699_ = lean_ctor_get(v___x_694_, 4);
lean_inc_ref(v_traceState_699_);
v_messages_700_ = lean_ctor_get(v___x_694_, 6);
lean_inc_ref(v_messages_700_);
v_infoState_701_ = lean_ctor_get(v___x_694_, 7);
lean_inc_ref(v_infoState_701_);
v_snapshotTasks_702_ = lean_ctor_get(v___x_694_, 8);
lean_inc_ref(v_snapshotTasks_702_);
lean_dec(v___x_694_);
v___x_703_ = l_Lean_Environment_importEnv_x3f(v_env_695_);
if (lean_obj_tag(v___x_703_) == 0)
{
v_nextMacroScope_666_ = v_nextMacroScope_696_;
v_ngen_667_ = v_ngen_697_;
v_auxDeclNGen_668_ = v_auxDeclNGen_698_;
v_traceState_669_ = v_traceState_699_;
v_messages_670_ = v_messages_700_;
v_infoState_671_ = v_infoState_701_;
v_snapshotTasks_672_ = v_snapshotTasks_702_;
v___y_673_ = v_env_695_;
goto v___jp_665_;
}
else
{
lean_object* v_val_704_; 
lean_dec_ref(v_env_695_);
v_val_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v___x_703_, 1);
v_nextMacroScope_666_ = v_nextMacroScope_696_;
v_ngen_667_ = v_ngen_697_;
v_auxDeclNGen_668_ = v_auxDeclNGen_698_;
v_traceState_669_ = v_traceState_699_;
v_messages_670_ = v_messages_700_;
v_infoState_671_ = v_infoState_701_;
v_snapshotTasks_672_ = v_snapshotTasks_702_;
v___y_673_ = v_val_704_;
goto v___jp_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_713_, lean_object* v_checkType_714_, lean_object* v_safety_715_, lean_object* v_value_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v_checkMeta_boxed_722_; uint8_t v_safety_boxed_723_; lean_object* v_res_724_; 
v_checkMeta_boxed_722_ = lean_unbox(v_checkMeta_713_);
v_safety_boxed_723_ = lean_unbox(v_safety_715_);
v_res_724_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_722_, v_checkType_714_, v_safety_boxed_723_, v_value_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; lean_object* v_nextMacroScope_730_; lean_object* v_ngen_731_; lean_object* v_auxDeclNGen_732_; lean_object* v_traceState_733_; lean_object* v_messages_734_; lean_object* v_infoState_735_; lean_object* v_snapshotTasks_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_762_; 
v___x_729_ = lean_st_ref_take(v___y_727_);
v_nextMacroScope_730_ = lean_ctor_get(v___x_729_, 1);
v_ngen_731_ = lean_ctor_get(v___x_729_, 2);
v_auxDeclNGen_732_ = lean_ctor_get(v___x_729_, 3);
v_traceState_733_ = lean_ctor_get(v___x_729_, 4);
v_messages_734_ = lean_ctor_get(v___x_729_, 6);
v_infoState_735_ = lean_ctor_get(v___x_729_, 7);
v_snapshotTasks_736_ = lean_ctor_get(v___x_729_, 8);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_763_ = lean_ctor_get(v___x_729_, 5);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_764_);
v___x_738_ = v___x_729_;
v_isShared_739_ = v_isSharedCheck_762_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snapshotTasks_736_);
lean_inc(v_infoState_735_);
lean_inc(v_messages_734_);
lean_inc(v_traceState_733_);
lean_inc(v_auxDeclNGen_732_);
lean_inc(v_ngen_731_);
lean_inc(v_nextMacroScope_730_);
lean_dec(v___x_729_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_762_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 5, v___x_740_);
lean_ctor_set(v___x_738_, 0, v_env_725_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_env_725_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_nextMacroScope_730_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_ngen_731_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_auxDeclNGen_732_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_traceState_733_);
lean_ctor_set(v_reuseFailAlloc_761_, 5, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_761_, 6, v_messages_734_);
lean_ctor_set(v_reuseFailAlloc_761_, 7, v_infoState_735_);
lean_ctor_set(v_reuseFailAlloc_761_, 8, v_snapshotTasks_736_);
v___x_742_ = v_reuseFailAlloc_761_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_mctx_745_; lean_object* v_zetaDeltaFVarIds_746_; lean_object* v_postponed_747_; lean_object* v_diag_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_759_; 
v___x_743_ = lean_st_ref_put(v___y_727_, v___x_742_);
v___x_744_ = lean_st_ref_take(v___y_726_);
v_mctx_745_ = lean_ctor_get(v___x_744_, 0);
v_zetaDeltaFVarIds_746_ = lean_ctor_get(v___x_744_, 2);
v_postponed_747_ = lean_ctor_get(v___x_744_, 3);
v_diag_748_ = lean_ctor_get(v___x_744_, 4);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_744_, 1);
lean_dec(v_unused_760_);
v___x_750_ = v___x_744_;
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_diag_748_);
lean_inc(v_postponed_747_);
lean_inc(v_zetaDeltaFVarIds_746_);
lean_inc(v_mctx_745_);
lean_dec(v___x_744_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_mctx_745_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_zetaDeltaFVarIds_746_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_postponed_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_diag_748_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_st_ref_put(v___y_726_, v___x_754_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_770_, lean_object* v_x_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; lean_object* v_env_778_; lean_object* v_a_780_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_777_ = lean_st_ref_get(v___y_775_);
v_env_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc_ref(v_env_778_);
lean_dec(v___x_777_);
v___x_790_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_770_, v___y_773_, v___y_775_);
lean_dec_ref(v___x_790_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
v___x_791_ = lean_apply_5(v_x_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, lean_box(0));
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_778_, v___y_773_, v___y_775_);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_793_, 0);
lean_dec(v_unused_801_);
v___x_795_ = v___x_793_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_dec(v___x_793_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_a_792_);
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_792_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
lean_object* v_a_802_; 
v_a_802_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_791_, 1);
v_a_780_ = v_a_802_;
goto v___jp_779_;
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v___x_781_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_778_, v___y_773_, v___y_775_);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_781_, 0);
lean_dec(v_unused_789_);
v___x_783_ = v___x_781_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_dec(v___x_781_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 1);
lean_ctor_set(v___x_783_, 0, v_a_780_);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_780_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_803_, lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_803_, v_x_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_811_, lean_object* v_checkType_812_, uint8_t v_safety_813_, uint8_t v_checkMeta_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_env_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_820_ = lean_st_ref_get(v_a_818_);
v_env_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_env_821_);
lean_dec(v___x_820_);
v___x_822_ = lean_box(v_checkMeta_814_);
v___x_823_ = lean_box(v_safety_813_);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_824_, 0, v___x_822_);
lean_closure_set(v___f_824_, 1, v_checkType_812_);
lean_closure_set(v___f_824_, 2, v___x_823_);
lean_closure_set(v___f_824_, 3, v_value_811_);
v___x_825_ = l_Lean_Environment_unlockAsync(v_env_821_);
v___x_826_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_825_, v___f_824_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_827_, lean_object* v_checkType_828_, lean_object* v_safety_829_, lean_object* v_checkMeta_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
uint8_t v_safety_boxed_836_; uint8_t v_checkMeta_boxed_837_; lean_object* v_res_838_; 
v_safety_boxed_836_ = lean_unbox(v_safety_829_);
v_checkMeta_boxed_837_ = lean_unbox(v_checkMeta_830_);
v_res_838_ = l_Lean_Meta_evalExprCore___redArg(v_value_827_, v_checkType_828_, v_safety_boxed_836_, v_checkMeta_boxed_837_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_839_, lean_object* v_value_840_, lean_object* v_checkType_841_, uint8_t v_safety_842_, uint8_t v_checkMeta_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Meta_evalExprCore___redArg(v_value_840_, v_checkType_841_, v_safety_842_, v_checkMeta_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_850_, lean_object* v_value_851_, lean_object* v_checkType_852_, lean_object* v_safety_853_, lean_object* v_checkMeta_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
uint8_t v_safety_boxed_860_; uint8_t v_checkMeta_boxed_861_; lean_object* v_res_862_; 
v_safety_boxed_860_ = lean_unbox(v_safety_853_);
v_checkMeta_boxed_861_ = lean_unbox(v_checkMeta_854_);
v_res_862_ = l_Lean_Meta_evalExprCore(v_00_u03b1_850_, v_value_851_, v_checkType_852_, v_safety_boxed_860_, v_checkMeta_boxed_861_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_877_, lean_object* v_constName_878_, uint8_t v_checkMeta_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_878_, v_checkMeta_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_886_, lean_object* v_constName_887_, lean_object* v_checkMeta_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
uint8_t v_checkMeta_boxed_894_; lean_object* v_res_895_; 
v_checkMeta_boxed_894_ = lean_unbox(v_checkMeta_888_);
v_res_895_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_886_, v_constName_887_, v_checkMeta_boxed_894_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_896_, lean_object* v_msg_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_904_, lean_object* v_msg_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_904_, v_msg_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_912_, v___y_914_, v___y_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_926_, lean_object* v_env_927_, lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_927_, v_x_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_935_, lean_object* v_env_936_, lean_object* v_x_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_935_, v_env_936_, v_x_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_944_, lean_object* v_x_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_952_, lean_object* v_x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_952_, v_x_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_959_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_963_, lean_object* v_type_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_Meta_whnfD(v_type_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_984_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_984_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_984_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_984_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
uint8_t v___x_975_; 
v___x_975_ = l_Lean_Expr_isConstOf(v_a_971_, v_typeName_963_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_del_object(v___x_973_);
v___x_976_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_977_ = l_Lean_indentExpr(v_a_971_);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_978_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec(v_a_971_);
v___x_980_ = lean_box(0);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_980_);
v___x_982_ = v___x_973_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
v_a_985_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_970_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_970_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_993_, lean_object* v_type_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_993_, v_type_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v_typeName_993_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1001_, lean_object* v_value_1002_, uint8_t v_safety_1003_, uint8_t v_checkMeta_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; 
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1010_, 0, v_typeName_1001_);
v___x_1011_ = l_Lean_Meta_evalExprCore___redArg(v_value_1002_, v___f_1010_, v_safety_1003_, v_checkMeta_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1012_, lean_object* v_value_1013_, lean_object* v_safety_1014_, lean_object* v_checkMeta_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v_safety_boxed_1021_; uint8_t v_checkMeta_boxed_1022_; lean_object* v_res_1023_; 
v_safety_boxed_1021_ = lean_unbox(v_safety_1014_);
v_checkMeta_boxed_1022_ = lean_unbox(v_checkMeta_1015_);
v_res_1023_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1012_, v_value_1013_, v_safety_boxed_1021_, v_checkMeta_boxed_1022_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1024_, lean_object* v_typeName_1025_, lean_object* v_value_1026_, uint8_t v_safety_1027_, uint8_t v_checkMeta_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1025_, v_value_1026_, v_safety_1027_, v_checkMeta_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_typeName_1036_, lean_object* v_value_1037_, lean_object* v_safety_1038_, lean_object* v_checkMeta_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
uint8_t v_safety_boxed_1045_; uint8_t v_checkMeta_boxed_1046_; lean_object* v_res_1047_; 
v_safety_boxed_1045_ = lean_unbox(v_safety_1038_);
v_checkMeta_boxed_1046_ = lean_unbox(v_checkMeta_1039_);
v_res_1047_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1035_, v_typeName_1036_, v_value_1037_, v_safety_boxed_1045_, v_checkMeta_boxed_1046_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1047_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1053_, lean_object* v_type_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
lean_inc_ref(v_expectedType_1053_);
lean_inc_ref(v_type_1054_);
v___x_1060_ = l_Lean_Meta_isExprDefEq(v_type_1054_, v_expectedType_1053_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1085_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_unbox(v_a_1061_);
lean_dec(v_a_1061_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_del_object(v___x_1063_);
v___x_1066_ = lean_box(0);
v___x_1067_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1068_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1054_, v_expectedType_1053_, v___x_1066_, v___x_1067_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_a_1069_);
v___x_1072_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1071_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1072_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1068_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1068_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_dec_ref(v_type_1054_);
lean_dec_ref(v_expectedType_1053_);
v___x_1081_ = lean_box(0);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1081_);
v___x_1083_ = v___x_1063_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_type_1054_);
lean_dec_ref(v_expectedType_1053_);
v_a_1086_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1060_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1060_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1094_, lean_object* v_type_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1094_, v_type_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1102_, lean_object* v_value_1103_, uint8_t v_safety_1104_, uint8_t v_checkMeta_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1111_, 0, v_expectedType_1102_);
v___x_1112_ = l_Lean_Meta_evalExprCore___redArg(v_value_1103_, v___f_1111_, v_safety_1104_, v_checkMeta_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1113_, lean_object* v_value_1114_, lean_object* v_safety_1115_, lean_object* v_checkMeta_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
uint8_t v_safety_boxed_1122_; uint8_t v_checkMeta_boxed_1123_; lean_object* v_res_1124_; 
v_safety_boxed_1122_ = lean_unbox(v_safety_1115_);
v_checkMeta_boxed_1123_ = lean_unbox(v_checkMeta_1116_);
v_res_1124_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1113_, v_value_1114_, v_safety_boxed_1122_, v_checkMeta_boxed_1123_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1125_, lean_object* v_expectedType_1126_, lean_object* v_value_1127_, uint8_t v_safety_1128_, uint8_t v_checkMeta_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1126_, v_value_1127_, v_safety_1128_, v_checkMeta_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_expectedType_1137_, lean_object* v_value_1138_, lean_object* v_safety_1139_, lean_object* v_checkMeta_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
uint8_t v_safety_boxed_1146_; uint8_t v_checkMeta_boxed_1147_; lean_object* v_res_1148_; 
v_safety_boxed_1146_ = lean_unbox(v_safety_1139_);
v_checkMeta_boxed_1147_ = lean_unbox(v_checkMeta_1140_);
v_res_1148_ = l_Lean_Meta_evalExpr(v_00_u03b1_1136_, v_expectedType_1137_, v_value_1138_, v_safety_boxed_1146_, v_checkMeta_boxed_1147_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1148_;
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

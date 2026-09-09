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
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v___x_77_; lean_object* v_toCold_78_; lean_object* v_mctx_79_; lean_object* v_lctx_80_; lean_object* v_options_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_st_ref_get(v___y_71_);
v_toCold_78_ = lean_ctor_get(v___y_72_, 0);
v_mctx_79_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_mctx_79_);
lean_dec(v___x_77_);
v_lctx_80_ = lean_ctor_get(v___y_70_, 2);
v_options_81_ = lean_ctor_get(v_toCold_78_, 2);
lean_inc_ref(v_options_81_);
lean_inc_ref(v_lctx_80_);
v___x_82_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_82_, 0, v_env_76_);
lean_ctor_set(v___x_82_, 1, v_mctx_79_);
lean_ctor_set(v___x_82_, 2, v_lctx_80_);
lean_ctor_set(v___x_82_, 3, v_options_81_);
v___x_83_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_msgData_69_);
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
v_ref_98_ = lean_ctor_get(v___y_95_, 2);
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
lean_object* v___x_158_; lean_object* v_toCold_159_; lean_object* v_env_160_; lean_object* v_options_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = lean_st_ref_get(v___y_153_);
v_toCold_159_ = lean_ctor_get(v___y_152_, 0);
v_env_160_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_env_160_);
lean_dec(v___x_158_);
v_options_161_ = lean_ctor_get(v_toCold_159_, 2);
v___x_162_ = l_Lean_Environment_evalConst___redArg(v_env_160_, v_options_161_, v_constName_148_, v_checkMeta_149_);
lean_dec(v_constName_148_);
lean_dec_ref(v_env_160_);
v___x_163_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_162_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; lean_object* v_toCold_166_; lean_object* v_env_167_; lean_object* v_options_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec_ref_known(v___x_164_, 1);
v___x_165_ = lean_st_ref_get(v___y_153_);
v_toCold_166_ = lean_ctor_get(v___y_152_, 0);
v_env_167_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_165_);
v_options_168_ = lean_ctor_get(v_toCold_166_, 2);
v___x_169_ = l_Lean_Environment_evalConst___redArg(v_env_167_, v_options_168_, v_constName_148_, v_checkMeta_149_);
lean_dec(v_constName_148_);
lean_dec_ref(v_env_167_);
v___x_170_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v___x_169_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_constName_148_);
v_a_171_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_164_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_164_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* v_constName_179_, lean_object* v_checkMeta_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
uint8_t v_checkMeta_boxed_186_; lean_object* v_res_187_; 
v_checkMeta_boxed_186_ = lean_unbox(v_checkMeta_180_);
v_res_187_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_179_, v_checkMeta_boxed_186_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_187_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object* v___x_188_, lean_object* v___x_189_, lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_191_, v_stop_192_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_array_uget_borrowed(v_as_190_, v_i_191_);
v___x_199_ = l_Lean_Environment_isImportedConst(v___x_188_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_nat_dec_lt(v___x_200_, v___x_189_);
if (v___x_201_ == 0)
{
goto v___jp_193_;
}
else
{
return v___x_201_;
}
}
else
{
goto v___jp_193_;
}
}
else
{
uint8_t v___x_202_; 
v___x_202_ = 0;
return v___x_202_;
}
v___jp_193_:
{
size_t v___x_194_; size_t v___x_195_; 
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_191_, v___x_194_);
v_i_191_ = v___x_195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* v___x_203_, lean_object* v___x_204_, lean_object* v_as_205_, lean_object* v_i_206_, lean_object* v_stop_207_){
_start:
{
size_t v_i_boxed_208_; size_t v_stop_boxed_209_; uint8_t v_res_210_; lean_object* v_r_211_; 
v_i_boxed_208_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_stop_boxed_209_ = lean_unbox_usize(v_stop_207_);
lean_dec(v_stop_207_);
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v___x_203_, v___x_204_, v_as_205_, v_i_boxed_208_, v_stop_boxed_209_);
lean_dec_ref(v_as_205_);
lean_dec(v___x_204_);
lean_dec_ref(v___x_203_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* v_o_215_, lean_object* v_k_216_, uint8_t v_v_217_){
_start:
{
lean_object* v_map_218_; uint8_t v_hasTrace_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_233_; 
v_map_218_ = lean_ctor_get(v_o_215_, 0);
v_hasTrace_219_ = lean_ctor_get_uint8(v_o_215_, sizeof(void*)*1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_o_215_);
if (v_isSharedCheck_233_ == 0)
{
v___x_221_ = v_o_215_;
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_map_218_);
lean_dec(v_o_215_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_223_, 0, v_v_217_);
lean_inc(v_k_216_);
v___x_224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_216_, v___x_223_, v_map_218_);
if (v_hasTrace_219_ == 0)
{
lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_228_; 
v___x_225_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1));
v___x_226_ = l_Lean_Name_isPrefixOf(v___x_225_, v_k_216_);
lean_dec(v_k_216_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_228_ = v___x_221_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_224_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_226_);
return v___x_228_;
}
}
else
{
lean_object* v___x_231_; 
lean_dec(v_k_216_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_231_ = v___x_221_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_224_);
lean_ctor_set_uint8(v_reuseFailAlloc_232_, sizeof(void*)*1, v_hasTrace_219_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object* v_o_234_, lean_object* v_k_235_, lean_object* v_v_236_){
_start:
{
uint8_t v_v_boxed_237_; lean_object* v_res_238_; 
v_v_boxed_237_ = lean_unbox(v_v_236_);
v_res_238_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_o_234_, v_k_235_, v_v_boxed_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object* v_opts_239_, lean_object* v_opt_240_, uint8_t v_val_241_){
_start:
{
lean_object* v_name_242_; lean_object* v___x_243_; 
v_name_242_ = lean_ctor_get(v_opt_240_, 0);
lean_inc(v_name_242_);
lean_dec_ref(v_opt_240_);
v___x_243_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(v_opts_239_, v_name_242_, v_val_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* v_opts_244_, lean_object* v_opt_245_, lean_object* v_val_246_){
_start:
{
uint8_t v_val_boxed_247_; lean_object* v_res_248_; 
v_val_boxed_247_ = lean_unbox(v_val_246_);
v_res_248_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_opts_244_, v_opt_245_, v_val_boxed_247_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
v___x_255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
lean_ctor_set(v___x_255_, 4, v___x_254_);
lean_ctor_set(v___x_255_, 5, v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_unsigned_to_nat(16u);
v___x_262_ = lean_mk_array(v___x_261_, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9));
v___x_269_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
v___x_270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_ctor_set(v___x_270_, 2, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t v_checkMeta_274_, lean_object* v_checkType_275_, uint8_t v_safety_276_, lean_object* v_value_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
uint8_t v___y_284_; lean_object* v___y_285_; uint8_t v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; uint8_t v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v_fileName_293_; lean_object* v_fileMap_294_; lean_object* v_currNamespace_295_; lean_object* v_openDecls_296_; lean_object* v_initHeartbeats_297_; lean_object* v_maxHeartbeats_298_; lean_object* v_quotContext_299_; lean_object* v_currMacroScope_300_; lean_object* v_cancelTk_x3f_301_; lean_object* v_inheritedTraceOptions_302_; lean_object* v_currRecDepth_303_; lean_object* v_ref_304_; uint8_t v_suppressElabErrors_305_; lean_object* v___y_306_; uint8_t v___y_321_; lean_object* v___y_322_; uint8_t v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; uint8_t v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_347_; lean_object* v___y_348_; uint8_t v___y_349_; lean_object* v___y_350_; uint8_t v___y_351_; lean_object* v___y_352_; uint8_t v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; uint8_t v___y_359_; uint8_t v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; uint8_t v___y_431_; lean_object* v___y_432_; uint8_t v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; uint8_t v___y_444_; uint8_t v___y_465_; lean_object* v___y_466_; uint8_t v___y_467_; uint8_t v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; uint8_t v___y_516_; uint8_t v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; uint8_t v___y_528_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_traceState_691_; lean_object* v_messages_692_; lean_object* v_infoState_693_; lean_object* v_snapshotTasks_694_; lean_object* v___y_695_; lean_object* v___x_714_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_714_ = lean_st_ref_get(v___y_281_);
lean_inc_ref(v_value_277_);
v___x_727_ = l_Lean_Expr_getUsedConstants(v_value_277_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_array_get_size(v___x_727_);
v___x_730_ = lean_nat_dec_lt(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v___x_727_);
lean_dec(v___x_714_);
goto v___jp_715_;
}
else
{
if (v___x_730_ == 0)
{
lean_dec_ref(v___x_727_);
lean_dec(v___x_714_);
goto v___jp_715_;
}
else
{
lean_object* v_env_731_; size_t v___x_732_; size_t v___x_733_; uint8_t v___x_734_; 
v_env_731_ = lean_ctor_get(v___x_714_, 0);
lean_inc_ref(v_env_731_);
lean_dec(v___x_714_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_729_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_731_, v___x_729_, v___x_727_, v___x_732_, v___x_733_);
lean_dec_ref(v___x_727_);
lean_dec_ref(v_env_731_);
if (v___x_734_ == 0)
{
goto v___jp_715_;
}
else
{
v___y_642_ = v___y_278_;
v___y_643_ = v___y_279_;
v___y_644_ = v___y_280_;
v___y_645_ = v___y_281_;
goto v___jp_641_;
}
}
}
v___jp_283_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_287_, v___y_292_);
v___x_308_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_308_, 0, v_fileName_293_);
lean_ctor_set(v___x_308_, 1, v_fileMap_294_);
lean_ctor_set(v___x_308_, 2, v___y_287_);
lean_ctor_set(v___x_308_, 3, v___x_307_);
lean_ctor_set(v___x_308_, 4, v_currNamespace_295_);
lean_ctor_set(v___x_308_, 5, v_openDecls_296_);
lean_ctor_set(v___x_308_, 6, v_initHeartbeats_297_);
lean_ctor_set(v___x_308_, 7, v_maxHeartbeats_298_);
lean_ctor_set(v___x_308_, 8, v_quotContext_299_);
lean_ctor_set(v___x_308_, 9, v_currMacroScope_300_);
lean_ctor_set(v___x_308_, 10, v_cancelTk_x3f_301_);
lean_ctor_set(v___x_308_, 11, v_inheritedTraceOptions_302_);
v___x_309_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_currRecDepth_303_);
lean_ctor_set(v___x_309_, 2, v_ref_304_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*3, v___y_290_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*3 + 1, v_suppressElabErrors_305_);
v___x_310_ = l_Lean_addAndCompile(v___y_289_, v___y_286_, v___y_284_, v___x_309_, v___y_306_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_311_; 
lean_dec_ref_known(v___x_310_, 1);
v___x_311_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_288_, v_checkMeta_274_, v___y_285_, v___y_291_, v___x_309_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref_known(v___x_309_, 3);
lean_dec(v___y_291_);
lean_dec_ref(v___y_285_);
return v___x_311_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref_known(v___x_309_, 3);
lean_dec(v___y_306_);
lean_dec(v___y_291_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_285_);
v_a_312_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_310_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
v___jp_320_:
{
lean_object* v_toCold_332_; lean_object* v_currRecDepth_333_; lean_object* v_ref_334_; uint8_t v_suppressElabErrors_335_; lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_currNamespace_338_; lean_object* v_openDecls_339_; lean_object* v_initHeartbeats_340_; lean_object* v_maxHeartbeats_341_; lean_object* v_quotContext_342_; lean_object* v_currMacroScope_343_; lean_object* v_cancelTk_x3f_344_; lean_object* v_inheritedTraceOptions_345_; 
v_toCold_332_ = lean_ctor_get(v___y_330_, 0);
lean_inc_ref(v_toCold_332_);
v_currRecDepth_333_ = lean_ctor_get(v___y_330_, 1);
lean_inc(v_currRecDepth_333_);
v_ref_334_ = lean_ctor_get(v___y_330_, 2);
lean_inc(v_ref_334_);
v_suppressElabErrors_335_ = lean_ctor_get_uint8(v___y_330_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_330_);
v_fileName_336_ = lean_ctor_get(v_toCold_332_, 0);
lean_inc_ref(v_fileName_336_);
v_fileMap_337_ = lean_ctor_get(v_toCold_332_, 1);
lean_inc_ref(v_fileMap_337_);
v_currNamespace_338_ = lean_ctor_get(v_toCold_332_, 4);
lean_inc(v_currNamespace_338_);
v_openDecls_339_ = lean_ctor_get(v_toCold_332_, 5);
lean_inc(v_openDecls_339_);
v_initHeartbeats_340_ = lean_ctor_get(v_toCold_332_, 6);
lean_inc(v_initHeartbeats_340_);
v_maxHeartbeats_341_ = lean_ctor_get(v_toCold_332_, 7);
lean_inc(v_maxHeartbeats_341_);
v_quotContext_342_ = lean_ctor_get(v_toCold_332_, 8);
lean_inc(v_quotContext_342_);
v_currMacroScope_343_ = lean_ctor_get(v_toCold_332_, 9);
lean_inc(v_currMacroScope_343_);
v_cancelTk_x3f_344_ = lean_ctor_get(v_toCold_332_, 10);
lean_inc(v_cancelTk_x3f_344_);
v_inheritedTraceOptions_345_ = lean_ctor_get(v_toCold_332_, 11);
lean_inc_ref(v_inheritedTraceOptions_345_);
lean_dec_ref(v_toCold_332_);
v___y_284_ = v___y_321_;
v___y_285_ = v___y_322_;
v___y_286_ = v___y_323_;
v___y_287_ = v___y_324_;
v___y_288_ = v___y_325_;
v___y_289_ = v___y_326_;
v___y_290_ = v___y_327_;
v___y_291_ = v___y_328_;
v___y_292_ = v___y_329_;
v_fileName_293_ = v_fileName_336_;
v_fileMap_294_ = v_fileMap_337_;
v_currNamespace_295_ = v_currNamespace_338_;
v_openDecls_296_ = v_openDecls_339_;
v_initHeartbeats_297_ = v_initHeartbeats_340_;
v_maxHeartbeats_298_ = v_maxHeartbeats_341_;
v_quotContext_299_ = v_quotContext_342_;
v_currMacroScope_300_ = v_currMacroScope_343_;
v_cancelTk_x3f_301_ = v_cancelTk_x3f_344_;
v_inheritedTraceOptions_302_ = v_inheritedTraceOptions_345_;
v_currRecDepth_303_ = v_currRecDepth_333_;
v_ref_304_ = v_ref_334_;
v_suppressElabErrors_305_ = v_suppressElabErrors_335_;
v___y_306_ = v___y_331_;
goto v___jp_283_;
}
v___jp_346_:
{
if (v___y_359_ == 0)
{
lean_object* v___x_360_; lean_object* v_env_361_; lean_object* v_nextMacroScope_362_; lean_object* v_ngen_363_; lean_object* v_auxDeclNGen_364_; lean_object* v_traceState_365_; lean_object* v_messages_366_; lean_object* v_infoState_367_; lean_object* v_snapshotTasks_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_377_; 
v___x_360_ = lean_st_ref_take(v___y_347_);
v_env_361_ = lean_ctor_get(v___x_360_, 0);
v_nextMacroScope_362_ = lean_ctor_get(v___x_360_, 1);
v_ngen_363_ = lean_ctor_get(v___x_360_, 2);
v_auxDeclNGen_364_ = lean_ctor_get(v___x_360_, 3);
v_traceState_365_ = lean_ctor_get(v___x_360_, 4);
v_messages_366_ = lean_ctor_get(v___x_360_, 6);
v_infoState_367_ = lean_ctor_get(v___x_360_, 7);
v_snapshotTasks_368_ = lean_ctor_get(v___x_360_, 8);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_360_, 5);
lean_dec(v_unused_378_);
v___x_370_ = v___x_360_;
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_snapshotTasks_368_);
lean_inc(v_infoState_367_);
lean_inc(v_messages_366_);
lean_inc(v_traceState_365_);
lean_inc(v_auxDeclNGen_364_);
lean_inc(v_ngen_363_);
lean_inc(v_nextMacroScope_362_);
lean_inc(v_env_361_);
lean_dec(v___x_360_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = l_Lean_Kernel_enableDiag(v_env_361_, v___y_353_);
lean_inc_ref(v___y_354_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 5, v___y_354_);
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_nextMacroScope_362_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_ngen_363_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_auxDeclNGen_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_traceState_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 5, v___y_354_);
lean_ctor_set(v_reuseFailAlloc_376_, 6, v_messages_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 7, v_infoState_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 8, v_snapshotTasks_368_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_st_ref_put(v___y_347_, v___x_374_);
v___y_321_ = v___y_349_;
v___y_322_ = v___y_350_;
v___y_323_ = v___y_351_;
v___y_324_ = v___y_352_;
v___y_325_ = v___y_356_;
v___y_326_ = v___y_357_;
v___y_327_ = v___y_353_;
v___y_328_ = v___y_358_;
v___y_329_ = v___y_355_;
v___y_330_ = v___y_348_;
v___y_331_ = v___y_347_;
goto v___jp_320_;
}
}
}
else
{
v___y_321_ = v___y_349_;
v___y_322_ = v___y_350_;
v___y_323_ = v___y_351_;
v___y_324_ = v___y_352_;
v___y_325_ = v___y_356_;
v___y_326_ = v___y_357_;
v___y_327_ = v___y_353_;
v___y_328_ = v___y_358_;
v___y_329_ = v___y_355_;
v___y_330_ = v___y_348_;
v___y_331_ = v___y_347_;
goto v___jp_320_;
}
}
v___jp_379_:
{
lean_object* v___x_393_; lean_object* v_toCold_394_; lean_object* v_currRecDepth_395_; lean_object* v_ref_396_; uint8_t v_suppressElabErrors_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_429_; 
v___x_393_ = lean_st_ref_get(v___y_392_);
v_toCold_394_ = lean_ctor_get(v___y_391_, 0);
v_currRecDepth_395_ = lean_ctor_get(v___y_391_, 1);
v_ref_396_ = lean_ctor_get(v___y_391_, 2);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*3 + 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v___y_391_);
if (v_isSharedCheck_429_ == 0)
{
v___x_399_ = v___y_391_;
v_isShared_400_ = v_isSharedCheck_429_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_ref_396_);
lean_inc(v_currRecDepth_395_);
lean_inc(v_toCold_394_);
lean_dec(v___y_391_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_429_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_fileName_401_; lean_object* v_fileMap_402_; lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v_initHeartbeats_405_; lean_object* v_maxHeartbeats_406_; lean_object* v_quotContext_407_; lean_object* v_currMacroScope_408_; lean_object* v_cancelTk_x3f_409_; lean_object* v_inheritedTraceOptions_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_426_; 
v_fileName_401_ = lean_ctor_get(v_toCold_394_, 0);
v_fileMap_402_ = lean_ctor_get(v_toCold_394_, 1);
v_currNamespace_403_ = lean_ctor_get(v_toCold_394_, 4);
v_openDecls_404_ = lean_ctor_get(v_toCold_394_, 5);
v_initHeartbeats_405_ = lean_ctor_get(v_toCold_394_, 6);
v_maxHeartbeats_406_ = lean_ctor_get(v_toCold_394_, 7);
v_quotContext_407_ = lean_ctor_get(v_toCold_394_, 8);
v_currMacroScope_408_ = lean_ctor_get(v_toCold_394_, 9);
v_cancelTk_x3f_409_ = lean_ctor_get(v_toCold_394_, 10);
v_inheritedTraceOptions_410_ = lean_ctor_get(v_toCold_394_, 11);
v_isSharedCheck_426_ = !lean_is_exclusive(v_toCold_394_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; lean_object* v_unused_428_; 
v_unused_427_ = lean_ctor_get(v_toCold_394_, 3);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_toCold_394_, 2);
lean_dec(v_unused_428_);
v___x_412_ = v_toCold_394_;
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_inheritedTraceOptions_410_);
lean_inc(v_cancelTk_x3f_409_);
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
lean_inc(v_maxHeartbeats_406_);
lean_inc(v_initHeartbeats_405_);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
lean_inc(v_fileMap_402_);
lean_inc(v_fileName_401_);
lean_dec(v_toCold_394_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_env_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v_env_414_ = lean_ctor_get(v___x_393_, 0);
lean_inc_ref(v_env_414_);
lean_dec(v___x_393_);
v___x_415_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_390_, v___y_389_);
lean_inc_ref(v_inheritedTraceOptions_410_);
lean_inc(v_cancelTk_x3f_409_);
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
lean_inc(v_maxHeartbeats_406_);
lean_inc(v_initHeartbeats_405_);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
lean_inc_ref(v___y_390_);
lean_inc_ref(v_fileMap_402_);
lean_inc_ref(v_fileName_401_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 3, v___x_415_);
lean_ctor_set(v___x_412_, 2, v___y_390_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_fileName_401_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_fileMap_402_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v___y_390_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_currNamespace_403_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v_openDecls_404_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v_initHeartbeats_405_);
lean_ctor_set(v_reuseFailAlloc_425_, 7, v_maxHeartbeats_406_);
lean_ctor_set(v_reuseFailAlloc_425_, 8, v_quotContext_407_);
lean_ctor_set(v_reuseFailAlloc_425_, 9, v_currMacroScope_408_);
lean_ctor_set(v_reuseFailAlloc_425_, 10, v_cancelTk_x3f_409_);
lean_ctor_set(v_reuseFailAlloc_425_, 11, v_inheritedTraceOptions_410_);
v___x_417_ = v_reuseFailAlloc_425_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
lean_inc(v_ref_396_);
lean_inc(v_currRecDepth_395_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_417_);
v___x_419_ = v___x_399_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_currRecDepth_395_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_ref_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*3 + 1, v_suppressElabErrors_397_);
v___x_419_ = v_reuseFailAlloc_424_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; uint8_t v___x_423_; 
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*3, v___y_380_);
v___x_420_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_421_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_390_, v___x_420_, v___y_384_);
v___x_422_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_421_, v___y_382_);
v___x_423_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_414_);
lean_dec_ref(v_env_414_);
if (v___x_422_ == 0)
{
if (v___x_423_ == 0)
{
lean_dec_ref(v___x_419_);
v___y_284_ = v___y_381_;
v___y_285_ = v___y_383_;
v___y_286_ = v___y_384_;
v___y_287_ = v___x_421_;
v___y_288_ = v___y_385_;
v___y_289_ = v___y_386_;
v___y_290_ = v___x_422_;
v___y_291_ = v___y_388_;
v___y_292_ = v___y_389_;
v_fileName_293_ = v_fileName_401_;
v_fileMap_294_ = v_fileMap_402_;
v_currNamespace_295_ = v_currNamespace_403_;
v_openDecls_296_ = v_openDecls_404_;
v_initHeartbeats_297_ = v_initHeartbeats_405_;
v_maxHeartbeats_298_ = v_maxHeartbeats_406_;
v_quotContext_299_ = v_quotContext_407_;
v_currMacroScope_300_ = v_currMacroScope_408_;
v_cancelTk_x3f_301_ = v_cancelTk_x3f_409_;
v_inheritedTraceOptions_302_ = v_inheritedTraceOptions_410_;
v_currRecDepth_303_ = v_currRecDepth_395_;
v_ref_304_ = v_ref_396_;
v_suppressElabErrors_305_ = v_suppressElabErrors_397_;
v___y_306_ = v___y_392_;
goto v___jp_283_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_410_);
lean_dec(v_cancelTk_x3f_409_);
lean_dec(v_currMacroScope_408_);
lean_dec(v_quotContext_407_);
lean_dec(v_maxHeartbeats_406_);
lean_dec(v_initHeartbeats_405_);
lean_dec(v_openDecls_404_);
lean_dec(v_currNamespace_403_);
lean_dec_ref(v_fileMap_402_);
lean_dec_ref(v_fileName_401_);
lean_dec(v_ref_396_);
lean_dec(v_currRecDepth_395_);
v___y_347_ = v___y_392_;
v___y_348_ = v___x_419_;
v___y_349_ = v___y_381_;
v___y_350_ = v___y_383_;
v___y_351_ = v___y_384_;
v___y_352_ = v___x_421_;
v___y_353_ = v___x_422_;
v___y_354_ = v___y_387_;
v___y_355_ = v___y_389_;
v___y_356_ = v___y_385_;
v___y_357_ = v___y_386_;
v___y_358_ = v___y_388_;
v___y_359_ = v___x_422_;
goto v___jp_346_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_410_);
lean_dec(v_cancelTk_x3f_409_);
lean_dec(v_currMacroScope_408_);
lean_dec(v_quotContext_407_);
lean_dec(v_maxHeartbeats_406_);
lean_dec(v_initHeartbeats_405_);
lean_dec(v_openDecls_404_);
lean_dec(v_currNamespace_403_);
lean_dec_ref(v_fileMap_402_);
lean_dec_ref(v_fileName_401_);
lean_dec(v_ref_396_);
lean_dec(v_currRecDepth_395_);
v___y_347_ = v___y_392_;
v___y_348_ = v___x_419_;
v___y_349_ = v___y_381_;
v___y_350_ = v___y_383_;
v___y_351_ = v___y_384_;
v___y_352_ = v___x_421_;
v___y_353_ = v___x_422_;
v___y_354_ = v___y_387_;
v___y_355_ = v___y_389_;
v___y_356_ = v___y_385_;
v___y_357_ = v___y_386_;
v___y_358_ = v___y_388_;
v___y_359_ = v___x_423_;
goto v___jp_346_;
}
}
}
}
}
}
v___jp_430_:
{
if (v___y_444_ == 0)
{
lean_object* v___x_445_; lean_object* v_env_446_; lean_object* v_nextMacroScope_447_; lean_object* v_ngen_448_; lean_object* v_auxDeclNGen_449_; lean_object* v_traceState_450_; lean_object* v_messages_451_; lean_object* v_infoState_452_; lean_object* v_snapshotTasks_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_462_; 
v___x_445_ = lean_st_ref_take(v___y_442_);
v_env_446_ = lean_ctor_get(v___x_445_, 0);
v_nextMacroScope_447_ = lean_ctor_get(v___x_445_, 1);
v_ngen_448_ = lean_ctor_get(v___x_445_, 2);
v_auxDeclNGen_449_ = lean_ctor_get(v___x_445_, 3);
v_traceState_450_ = lean_ctor_get(v___x_445_, 4);
v_messages_451_ = lean_ctor_get(v___x_445_, 6);
v_infoState_452_ = lean_ctor_get(v___x_445_, 7);
v_snapshotTasks_453_ = lean_ctor_get(v___x_445_, 8);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_445_, 5);
lean_dec(v_unused_463_);
v___x_455_ = v___x_445_;
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_snapshotTasks_453_);
lean_inc(v_infoState_452_);
lean_inc(v_messages_451_);
lean_inc(v_traceState_450_);
lean_inc(v_auxDeclNGen_449_);
lean_inc(v_ngen_448_);
lean_inc(v_nextMacroScope_447_);
lean_inc(v_env_446_);
lean_dec(v___x_445_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_Kernel_enableDiag(v_env_446_, v___y_436_);
lean_inc_ref(v___y_434_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 5, v___y_434_);
lean_ctor_set(v___x_455_, 0, v___x_457_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_nextMacroScope_447_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_ngen_448_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_auxDeclNGen_449_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_traceState_450_);
lean_ctor_set(v_reuseFailAlloc_461_, 5, v___y_434_);
lean_ctor_set(v_reuseFailAlloc_461_, 6, v_messages_451_);
lean_ctor_set(v_reuseFailAlloc_461_, 7, v_infoState_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 8, v_snapshotTasks_453_);
v___x_459_ = v_reuseFailAlloc_461_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; 
v___x_460_ = lean_st_ref_put(v___y_442_, v___x_459_);
v___y_380_ = v___y_436_;
v___y_381_ = v___y_431_;
v___y_382_ = v___y_437_;
v___y_383_ = v___y_432_;
v___y_384_ = v___y_433_;
v___y_385_ = v___y_439_;
v___y_386_ = v___y_440_;
v___y_387_ = v___y_434_;
v___y_388_ = v___y_441_;
v___y_389_ = v___y_435_;
v___y_390_ = v___y_443_;
v___y_391_ = v___y_438_;
v___y_392_ = v___y_442_;
goto v___jp_379_;
}
}
}
else
{
v___y_380_ = v___y_436_;
v___y_381_ = v___y_431_;
v___y_382_ = v___y_437_;
v___y_383_ = v___y_432_;
v___y_384_ = v___y_433_;
v___y_385_ = v___y_439_;
v___y_386_ = v___y_440_;
v___y_387_ = v___y_434_;
v___y_388_ = v___y_441_;
v___y_389_ = v___y_435_;
v___y_390_ = v___y_443_;
v___y_391_ = v___y_438_;
v___y_392_ = v___y_442_;
goto v___jp_379_;
}
}
v___jp_464_:
{
lean_object* v___x_477_; lean_object* v_toCold_478_; lean_object* v_currRecDepth_479_; lean_object* v_ref_480_; uint8_t v_suppressElabErrors_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_514_; 
v___x_477_ = lean_st_ref_get(v___y_476_);
v_toCold_478_ = lean_ctor_get(v___y_475_, 0);
v_currRecDepth_479_ = lean_ctor_get(v___y_475_, 1);
v_ref_480_ = lean_ctor_get(v___y_475_, 2);
v_suppressElabErrors_481_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*3 + 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v___y_475_);
if (v_isSharedCheck_514_ == 0)
{
v___x_483_ = v___y_475_;
v_isShared_484_ = v_isSharedCheck_514_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_ref_480_);
lean_inc(v_currRecDepth_479_);
lean_inc(v_toCold_478_);
lean_dec(v___y_475_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_514_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_fileName_485_; lean_object* v_fileMap_486_; lean_object* v_currNamespace_487_; lean_object* v_openDecls_488_; lean_object* v_initHeartbeats_489_; lean_object* v_maxHeartbeats_490_; lean_object* v_quotContext_491_; lean_object* v_currMacroScope_492_; lean_object* v_cancelTk_x3f_493_; lean_object* v_inheritedTraceOptions_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_511_; 
v_fileName_485_ = lean_ctor_get(v_toCold_478_, 0);
v_fileMap_486_ = lean_ctor_get(v_toCold_478_, 1);
v_currNamespace_487_ = lean_ctor_get(v_toCold_478_, 4);
v_openDecls_488_ = lean_ctor_get(v_toCold_478_, 5);
v_initHeartbeats_489_ = lean_ctor_get(v_toCold_478_, 6);
v_maxHeartbeats_490_ = lean_ctor_get(v_toCold_478_, 7);
v_quotContext_491_ = lean_ctor_get(v_toCold_478_, 8);
v_currMacroScope_492_ = lean_ctor_get(v_toCold_478_, 9);
v_cancelTk_x3f_493_ = lean_ctor_get(v_toCold_478_, 10);
v_inheritedTraceOptions_494_ = lean_ctor_get(v_toCold_478_, 11);
v_isSharedCheck_511_ = !lean_is_exclusive(v_toCold_478_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; lean_object* v_unused_513_; 
v_unused_512_ = lean_ctor_get(v_toCold_478_, 3);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_toCold_478_, 2);
lean_dec(v_unused_513_);
v___x_496_ = v_toCold_478_;
v_isShared_497_ = v_isSharedCheck_511_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_inheritedTraceOptions_494_);
lean_inc(v_cancelTk_x3f_493_);
lean_inc(v_currMacroScope_492_);
lean_inc(v_quotContext_491_);
lean_inc(v_maxHeartbeats_490_);
lean_inc(v_initHeartbeats_489_);
lean_inc(v_openDecls_488_);
lean_inc(v_currNamespace_487_);
lean_inc(v_fileMap_486_);
lean_inc(v_fileName_485_);
lean_dec(v_toCold_478_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_511_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_env_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v_env_498_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_env_498_);
lean_dec(v___x_477_);
v___x_499_ = l_Lean_maxRecDepth;
v___x_500_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_474_, v___x_499_);
lean_inc_ref(v___y_474_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 3, v___x_500_);
lean_ctor_set(v___x_496_, 2, v___y_474_);
v___x_502_ = v___x_496_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fileName_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_fileMap_486_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___y_474_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_currNamespace_487_);
lean_ctor_set(v_reuseFailAlloc_510_, 5, v_openDecls_488_);
lean_ctor_set(v_reuseFailAlloc_510_, 6, v_initHeartbeats_489_);
lean_ctor_set(v_reuseFailAlloc_510_, 7, v_maxHeartbeats_490_);
lean_ctor_set(v_reuseFailAlloc_510_, 8, v_quotContext_491_);
lean_ctor_set(v_reuseFailAlloc_510_, 9, v_currMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_510_, 10, v_cancelTk_x3f_493_);
lean_ctor_set(v_reuseFailAlloc_510_, 11, v_inheritedTraceOptions_494_);
v___x_502_ = v_reuseFailAlloc_510_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_502_);
v___x_504_ = v___x_483_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_currRecDepth_479_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_ref_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_509_, sizeof(void*)*3 + 1, v_suppressElabErrors_481_);
v___x_504_ = v_reuseFailAlloc_509_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; uint8_t v___x_508_; 
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3, v___y_465_);
v___x_505_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_506_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_474_, v___x_505_, v___y_467_);
v___x_507_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_506_, v___y_466_);
v___x_508_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_498_);
lean_dec_ref(v_env_498_);
if (v___x_507_ == 0)
{
if (v___x_508_ == 0)
{
v___y_380_ = v___x_507_;
v___y_381_ = v___y_467_;
v___y_382_ = v___y_466_;
v___y_383_ = v___y_469_;
v___y_384_ = v___y_468_;
v___y_385_ = v___y_470_;
v___y_386_ = v___y_471_;
v___y_387_ = v___y_472_;
v___y_388_ = v___y_473_;
v___y_389_ = v___x_499_;
v___y_390_ = v___x_506_;
v___y_391_ = v___x_504_;
v___y_392_ = v___y_476_;
goto v___jp_379_;
}
else
{
v___y_431_ = v___y_467_;
v___y_432_ = v___y_469_;
v___y_433_ = v___y_468_;
v___y_434_ = v___y_472_;
v___y_435_ = v___x_499_;
v___y_436_ = v___x_507_;
v___y_437_ = v___y_466_;
v___y_438_ = v___x_504_;
v___y_439_ = v___y_470_;
v___y_440_ = v___y_471_;
v___y_441_ = v___y_473_;
v___y_442_ = v___y_476_;
v___y_443_ = v___x_506_;
v___y_444_ = v___x_507_;
goto v___jp_430_;
}
}
else
{
v___y_431_ = v___y_467_;
v___y_432_ = v___y_469_;
v___y_433_ = v___y_468_;
v___y_434_ = v___y_472_;
v___y_435_ = v___x_499_;
v___y_436_ = v___x_507_;
v___y_437_ = v___y_466_;
v___y_438_ = v___x_504_;
v___y_439_ = v___y_470_;
v___y_440_ = v___y_471_;
v___y_441_ = v___y_473_;
v___y_442_ = v___y_476_;
v___y_443_ = v___x_506_;
v___y_444_ = v___x_508_;
goto v___jp_430_;
}
}
}
}
}
}
v___jp_515_:
{
if (v___y_528_ == 0)
{
lean_object* v___x_529_; lean_object* v_env_530_; lean_object* v_nextMacroScope_531_; lean_object* v_ngen_532_; lean_object* v_auxDeclNGen_533_; lean_object* v_traceState_534_; lean_object* v_messages_535_; lean_object* v_infoState_536_; lean_object* v_snapshotTasks_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_546_; 
v___x_529_ = lean_st_ref_take(v___y_523_);
v_env_530_ = lean_ctor_get(v___x_529_, 0);
v_nextMacroScope_531_ = lean_ctor_get(v___x_529_, 1);
v_ngen_532_ = lean_ctor_get(v___x_529_, 2);
v_auxDeclNGen_533_ = lean_ctor_get(v___x_529_, 3);
v_traceState_534_ = lean_ctor_get(v___x_529_, 4);
v_messages_535_ = lean_ctor_get(v___x_529_, 6);
v_infoState_536_ = lean_ctor_get(v___x_529_, 7);
v_snapshotTasks_537_ = lean_ctor_get(v___x_529_, 8);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v___x_529_, 5);
lean_dec(v_unused_547_);
v___x_539_ = v___x_529_;
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snapshotTasks_537_);
lean_inc(v_infoState_536_);
lean_inc(v_messages_535_);
lean_inc(v_traceState_534_);
lean_inc(v_auxDeclNGen_533_);
lean_inc(v_ngen_532_);
lean_inc(v_nextMacroScope_531_);
lean_inc(v_env_530_);
lean_dec(v___x_529_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = l_Lean_Kernel_enableDiag(v_env_530_, v___y_521_);
lean_inc_ref(v___y_519_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 5, v___y_519_);
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_nextMacroScope_531_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_ngen_532_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_auxDeclNGen_533_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_traceState_534_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v___y_519_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_messages_535_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_infoState_536_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v_snapshotTasks_537_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_st_ref_put(v___y_523_, v___x_543_);
v___y_465_ = v___y_521_;
v___y_466_ = v___y_522_;
v___y_467_ = v___y_516_;
v___y_468_ = v___y_517_;
v___y_469_ = v___y_518_;
v___y_470_ = v___y_524_;
v___y_471_ = v___y_525_;
v___y_472_ = v___y_519_;
v___y_473_ = v___y_526_;
v___y_474_ = v___y_520_;
v___y_475_ = v___y_527_;
v___y_476_ = v___y_523_;
goto v___jp_464_;
}
}
}
else
{
v___y_465_ = v___y_521_;
v___y_466_ = v___y_522_;
v___y_467_ = v___y_516_;
v___y_468_ = v___y_517_;
v___y_469_ = v___y_518_;
v___y_470_ = v___y_524_;
v___y_471_ = v___y_525_;
v___y_472_ = v___y_519_;
v___y_473_ = v___y_526_;
v___y_474_ = v___y_520_;
v___y_475_ = v___y_527_;
v___y_476_ = v___y_523_;
goto v___jp_464_;
}
}
v___jp_548_:
{
lean_object* v___x_557_; 
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc_ref(v___y_549_);
v___x_557_ = lean_infer_type(v___y_549_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc_n(v_a_558_, 2);
lean_dec_ref_known(v___x_557_, 1);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
v___x_559_ = lean_apply_6(v_checkType_275_, v_a_558_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, lean_box(0));
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_560_; lean_object* v_env_561_; lean_object* v_nextMacroScope_562_; lean_object* v_ngen_563_; lean_object* v_auxDeclNGen_564_; lean_object* v_traceState_565_; lean_object* v_messages_566_; lean_object* v_infoState_567_; lean_object* v_snapshotTasks_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref_known(v___x_559_, 1);
v___x_560_ = lean_st_ref_take(v___y_556_);
v_env_561_ = lean_ctor_get(v___x_560_, 0);
v_nextMacroScope_562_ = lean_ctor_get(v___x_560_, 1);
v_ngen_563_ = lean_ctor_get(v___x_560_, 2);
v_auxDeclNGen_564_ = lean_ctor_get(v___x_560_, 3);
v_traceState_565_ = lean_ctor_get(v___x_560_, 4);
v_messages_566_ = lean_ctor_get(v___x_560_, 6);
v_infoState_567_ = lean_ctor_get(v___x_560_, 7);
v_snapshotTasks_568_ = lean_ctor_get(v___x_560_, 8);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v___x_560_, 5);
lean_dec(v_unused_624_);
v___x_570_ = v___x_560_;
v_isShared_571_ = v_isSharedCheck_623_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_snapshotTasks_568_);
lean_inc(v_infoState_567_);
lean_inc(v_messages_566_);
lean_inc(v_traceState_565_);
lean_inc(v_auxDeclNGen_564_);
lean_inc(v_ngen_563_);
lean_inc(v_nextMacroScope_562_);
lean_inc(v_env_561_);
lean_dec(v___x_560_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_623_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_572_ = lean_array_to_list(v___y_552_);
lean_inc_n(v___y_550_, 3);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v___y_550_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
lean_ctor_set(v___x_573_, 2, v_a_558_);
lean_inc(v___y_551_);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_550_);
lean_ctor_set(v___x_574_, 1, v___y_551_);
v___x_575_ = l_Lean_markMeta(v_env_561_, v___y_550_);
v___x_576_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 5, v___x_576_);
lean_ctor_set(v___x_570_, 0, v___x_575_);
v___x_578_ = v___x_570_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_nextMacroScope_562_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_ngen_563_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_auxDeclNGen_564_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v_traceState_565_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_messages_566_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_infoState_567_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v_snapshotTasks_568_);
v___x_578_ = v_reuseFailAlloc_622_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_mctx_581_; lean_object* v_zetaDeltaFVarIds_582_; lean_object* v_postponed_583_; lean_object* v_diag_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_620_; 
v___x_579_ = lean_st_ref_put(v___y_556_, v___x_578_);
v___x_580_ = lean_st_ref_take(v___y_554_);
v_mctx_581_ = lean_ctor_get(v___x_580_, 0);
v_zetaDeltaFVarIds_582_ = lean_ctor_get(v___x_580_, 2);
v_postponed_583_ = lean_ctor_get(v___x_580_, 3);
v_diag_584_ = lean_ctor_get(v___x_580_, 4);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_580_, 1);
lean_dec(v_unused_621_);
v___x_586_ = v___x_580_;
v_isShared_587_ = v_isSharedCheck_620_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_diag_584_);
lean_inc(v_postponed_583_);
lean_inc(v_zetaDeltaFVarIds_582_);
lean_inc(v_mctx_581_);
lean_dec(v___x_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_620_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_mctx_581_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_zetaDeltaFVarIds_582_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_postponed_583_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_diag_584_);
v___x_590_ = v_reuseFailAlloc_619_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_env_593_; lean_object* v_checked_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_591_ = lean_st_ref_put(v___y_554_, v___x_590_);
v___x_592_ = lean_st_ref_get(v___y_556_);
v_env_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc_ref(v_env_593_);
lean_dec(v___x_592_);
v_checked_594_ = lean_ctor_get(v_env_593_, 2);
lean_inc_ref(v_checked_594_);
lean_dec_ref(v_env_593_);
v___x_595_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_596_ = l_Lean_traceBlock___redArg(v___x_595_, v_checked_594_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_597_; lean_object* v_toCold_598_; lean_object* v_options_599_; lean_object* v_env_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; uint8_t v___x_610_; 
lean_dec_ref_known(v___x_596_, 1);
v___x_597_ = lean_st_ref_get(v___y_556_);
v_toCold_598_ = lean_ctor_get(v___y_555_, 0);
v_options_599_ = lean_ctor_get(v_toCold_598_, 2);
v_env_600_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_600_);
lean_dec(v___x_597_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_602_, 0, v___x_573_);
lean_ctor_set(v___x_602_, 1, v___y_549_);
lean_ctor_set(v___x_602_, 2, v___x_601_);
lean_ctor_set(v___x_602_, 3, v___x_574_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*4, v_safety_276_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = 1;
v___x_605_ = 0;
v___x_606_ = l_Lean_Elab_async;
lean_inc_ref(v_options_599_);
v___x_607_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_599_, v___x_606_, v___x_605_);
v___x_608_ = l_Lean_diagnostics;
v___x_609_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_607_, v___x_608_);
v___x_610_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_600_);
lean_dec_ref(v_env_600_);
if (v___x_609_ == 0)
{
if (v___x_610_ == 0)
{
v___y_465_ = v___x_609_;
v___y_466_ = v___x_608_;
v___y_467_ = v___x_605_;
v___y_468_ = v___x_604_;
v___y_469_ = v___y_553_;
v___y_470_ = v___y_550_;
v___y_471_ = v___x_603_;
v___y_472_ = v___x_576_;
v___y_473_ = v___y_554_;
v___y_474_ = v___x_607_;
v___y_475_ = v___y_555_;
v___y_476_ = v___y_556_;
goto v___jp_464_;
}
else
{
v___y_516_ = v___x_605_;
v___y_517_ = v___x_604_;
v___y_518_ = v___y_553_;
v___y_519_ = v___x_576_;
v___y_520_ = v___x_607_;
v___y_521_ = v___x_609_;
v___y_522_ = v___x_608_;
v___y_523_ = v___y_556_;
v___y_524_ = v___y_550_;
v___y_525_ = v___x_603_;
v___y_526_ = v___y_554_;
v___y_527_ = v___y_555_;
v___y_528_ = v___x_609_;
goto v___jp_515_;
}
}
else
{
v___y_516_ = v___x_605_;
v___y_517_ = v___x_604_;
v___y_518_ = v___y_553_;
v___y_519_ = v___x_576_;
v___y_520_ = v___x_607_;
v___y_521_ = v___x_609_;
v___y_522_ = v___x_608_;
v___y_523_ = v___y_556_;
v___y_524_ = v___y_550_;
v___y_525_ = v___x_603_;
v___y_526_ = v___y_554_;
v___y_527_ = v___y_555_;
v___y_528_ = v___x_610_;
goto v___jp_515_;
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref_known(v___x_574_, 2);
lean_dec_ref_known(v___x_573_, 3);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
v_a_611_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_596_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_596_);
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
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_558_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
v_a_625_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_559_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_559_);
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
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec_ref(v_checkType_275_);
v_a_633_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_557_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_557_);
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
v___jp_641_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_st_ref_get(v___y_645_);
v___x_647_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_648_ = l_Lean_Core_mkFreshUserName(v___x_647_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_277_, v___y_643_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_env_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_params_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc_n(v_a_651_, 2);
lean_dec_ref_known(v___x_650_, 1);
v_env_652_ = lean_ctor_get(v___x_646_, 0);
lean_inc_ref(v_env_652_);
lean_dec(v___x_646_);
v___x_653_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_654_ = l_Lean_collectLevelParams(v___x_653_, v_a_651_);
v_params_655_ = lean_ctor_get(v___x_654_, 2);
lean_inc_ref(v_params_655_);
lean_dec_ref(v___x_654_);
v___x_656_ = l_Lean_mkPrivateName(v_env_652_, v_a_649_);
lean_dec_ref(v_env_652_);
v___x_657_ = lean_box(0);
v___x_658_ = l_Lean_Expr_hasMVar(v_a_651_);
if (v___x_658_ == 0)
{
v___y_549_ = v_a_651_;
v___y_550_ = v___x_656_;
v___y_551_ = v___x_657_;
v___y_552_ = v_params_655_;
v___y_553_ = v___y_642_;
v___y_554_ = v___y_643_;
v___y_555_ = v___y_644_;
v___y_556_ = v___y_645_;
goto v___jp_548_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_651_);
v___x_660_ = l_Lean_indentExpr(v_a_651_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_661_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_dec_ref_known(v___x_662_, 1);
v___y_549_ = v_a_651_;
v___y_550_ = v___x_656_;
v___y_551_ = v___x_657_;
v___y_552_ = v_params_655_;
v___y_553_ = v___y_642_;
v___y_554_ = v___y_643_;
v___y_555_ = v___y_644_;
v___y_556_ = v___y_645_;
goto v___jp_548_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v___x_656_);
lean_dec_ref(v_params_655_);
lean_dec(v_a_651_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_checkType_275_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_a_649_);
lean_dec(v___x_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_checkType_275_);
v_a_671_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_650_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_650_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___x_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_value_277_);
lean_dec_ref(v_checkType_275_);
v_a_679_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_648_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_648_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
v___jp_687_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_mctx_700_; lean_object* v_zetaDeltaFVarIds_701_; lean_object* v_postponed_702_; lean_object* v_diag_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_712_; 
v___x_696_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_697_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_697_, 0, v___y_695_);
lean_ctor_set(v___x_697_, 1, v_nextMacroScope_688_);
lean_ctor_set(v___x_697_, 2, v_ngen_689_);
lean_ctor_set(v___x_697_, 3, v_auxDeclNGen_690_);
lean_ctor_set(v___x_697_, 4, v_traceState_691_);
lean_ctor_set(v___x_697_, 5, v___x_696_);
lean_ctor_set(v___x_697_, 6, v_messages_692_);
lean_ctor_set(v___x_697_, 7, v_infoState_693_);
lean_ctor_set(v___x_697_, 8, v_snapshotTasks_694_);
v___x_698_ = lean_st_ref_put(v___y_281_, v___x_697_);
v___x_699_ = lean_st_ref_take(v___y_279_);
v_mctx_700_ = lean_ctor_get(v___x_699_, 0);
v_zetaDeltaFVarIds_701_ = lean_ctor_get(v___x_699_, 2);
v_postponed_702_ = lean_ctor_get(v___x_699_, 3);
v_diag_703_ = lean_ctor_get(v___x_699_, 4);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_699_, 1);
lean_dec(v_unused_713_);
v___x_705_ = v___x_699_;
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_diag_703_);
lean_inc(v_postponed_702_);
lean_inc(v_zetaDeltaFVarIds_701_);
lean_inc(v_mctx_700_);
lean_dec(v___x_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_mctx_700_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_zetaDeltaFVarIds_701_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_postponed_702_);
lean_ctor_set(v_reuseFailAlloc_711_, 4, v_diag_703_);
v___x_709_ = v_reuseFailAlloc_711_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; 
v___x_710_ = lean_st_ref_put(v___y_279_, v___x_709_);
v___y_642_ = v___y_278_;
v___y_643_ = v___y_279_;
v___y_644_ = v___y_280_;
v___y_645_ = v___y_281_;
goto v___jp_641_;
}
}
}
v___jp_715_:
{
lean_object* v___x_716_; lean_object* v_env_717_; lean_object* v_nextMacroScope_718_; lean_object* v_ngen_719_; lean_object* v_auxDeclNGen_720_; lean_object* v_traceState_721_; lean_object* v_messages_722_; lean_object* v_infoState_723_; lean_object* v_snapshotTasks_724_; lean_object* v___x_725_; 
v___x_716_ = lean_st_ref_take(v___y_281_);
v_env_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref_n(v_env_717_, 2);
v_nextMacroScope_718_ = lean_ctor_get(v___x_716_, 1);
lean_inc(v_nextMacroScope_718_);
v_ngen_719_ = lean_ctor_get(v___x_716_, 2);
lean_inc_ref(v_ngen_719_);
v_auxDeclNGen_720_ = lean_ctor_get(v___x_716_, 3);
lean_inc_ref(v_auxDeclNGen_720_);
v_traceState_721_ = lean_ctor_get(v___x_716_, 4);
lean_inc_ref(v_traceState_721_);
v_messages_722_ = lean_ctor_get(v___x_716_, 6);
lean_inc_ref(v_messages_722_);
v_infoState_723_ = lean_ctor_get(v___x_716_, 7);
lean_inc_ref(v_infoState_723_);
v_snapshotTasks_724_ = lean_ctor_get(v___x_716_, 8);
lean_inc_ref(v_snapshotTasks_724_);
lean_dec(v___x_716_);
v___x_725_ = l_Lean_Environment_importEnv_x3f(v_env_717_);
if (lean_obj_tag(v___x_725_) == 0)
{
v_nextMacroScope_688_ = v_nextMacroScope_718_;
v_ngen_689_ = v_ngen_719_;
v_auxDeclNGen_690_ = v_auxDeclNGen_720_;
v_traceState_691_ = v_traceState_721_;
v_messages_692_ = v_messages_722_;
v_infoState_693_ = v_infoState_723_;
v_snapshotTasks_694_ = v_snapshotTasks_724_;
v___y_695_ = v_env_717_;
goto v___jp_687_;
}
else
{
lean_object* v_val_726_; 
lean_dec_ref(v_env_717_);
v_val_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_725_, 1);
v_nextMacroScope_688_ = v_nextMacroScope_718_;
v_ngen_689_ = v_ngen_719_;
v_auxDeclNGen_690_ = v_auxDeclNGen_720_;
v_traceState_691_ = v_traceState_721_;
v_messages_692_ = v_messages_722_;
v_infoState_693_ = v_infoState_723_;
v_snapshotTasks_694_ = v_snapshotTasks_724_;
v___y_695_ = v_val_726_;
goto v___jp_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_735_, lean_object* v_checkType_736_, lean_object* v_safety_737_, lean_object* v_value_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v_checkMeta_boxed_744_; uint8_t v_safety_boxed_745_; lean_object* v_res_746_; 
v_checkMeta_boxed_744_ = lean_unbox(v_checkMeta_735_);
v_safety_boxed_745_ = lean_unbox(v_safety_737_);
v_res_746_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_744_, v_checkType_736_, v_safety_boxed_745_, v_value_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; lean_object* v_nextMacroScope_752_; lean_object* v_ngen_753_; lean_object* v_auxDeclNGen_754_; lean_object* v_traceState_755_; lean_object* v_messages_756_; lean_object* v_infoState_757_; lean_object* v_snapshotTasks_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_784_; 
v___x_751_ = lean_st_ref_take(v___y_749_);
v_nextMacroScope_752_ = lean_ctor_get(v___x_751_, 1);
v_ngen_753_ = lean_ctor_get(v___x_751_, 2);
v_auxDeclNGen_754_ = lean_ctor_get(v___x_751_, 3);
v_traceState_755_ = lean_ctor_get(v___x_751_, 4);
v_messages_756_ = lean_ctor_get(v___x_751_, 6);
v_infoState_757_ = lean_ctor_get(v___x_751_, 7);
v_snapshotTasks_758_ = lean_ctor_get(v___x_751_, 8);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; 
v_unused_785_ = lean_ctor_get(v___x_751_, 5);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_786_);
v___x_760_ = v___x_751_;
v_isShared_761_ = v_isSharedCheck_784_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snapshotTasks_758_);
lean_inc(v_infoState_757_);
lean_inc(v_messages_756_);
lean_inc(v_traceState_755_);
lean_inc(v_auxDeclNGen_754_);
lean_inc(v_ngen_753_);
lean_inc(v_nextMacroScope_752_);
lean_dec(v___x_751_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_784_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 5, v___x_762_);
lean_ctor_set(v___x_760_, 0, v_env_747_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_env_747_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_nextMacroScope_752_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_ngen_753_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_auxDeclNGen_754_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_traceState_755_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_783_, 6, v_messages_756_);
lean_ctor_set(v_reuseFailAlloc_783_, 7, v_infoState_757_);
lean_ctor_set(v_reuseFailAlloc_783_, 8, v_snapshotTasks_758_);
v___x_764_ = v_reuseFailAlloc_783_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_mctx_767_; lean_object* v_zetaDeltaFVarIds_768_; lean_object* v_postponed_769_; lean_object* v_diag_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_781_; 
v___x_765_ = lean_st_ref_put(v___y_749_, v___x_764_);
v___x_766_ = lean_st_ref_take(v___y_748_);
v_mctx_767_ = lean_ctor_get(v___x_766_, 0);
v_zetaDeltaFVarIds_768_ = lean_ctor_get(v___x_766_, 2);
v_postponed_769_ = lean_ctor_get(v___x_766_, 3);
v_diag_770_ = lean_ctor_get(v___x_766_, 4);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_766_, 1);
lean_dec(v_unused_782_);
v___x_772_ = v___x_766_;
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_diag_770_);
lean_inc(v_postponed_769_);
lean_inc(v_zetaDeltaFVarIds_768_);
lean_inc(v_mctx_767_);
lean_dec(v___x_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_mctx_767_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_zetaDeltaFVarIds_768_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_postponed_769_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_diag_770_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = lean_st_ref_put(v___y_748_, v___x_776_);
v___x_778_ = lean_box(0);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec(v___y_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; lean_object* v_env_800_; lean_object* v_a_802_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_799_ = lean_st_ref_get(v___y_797_);
v_env_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc_ref(v_env_800_);
lean_dec(v___x_799_);
v___x_812_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_792_, v___y_795_, v___y_797_);
lean_dec_ref(v___x_812_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
v___x_813_ = lean_apply_5(v_x_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, lean_box(0));
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v___x_815_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_800_, v___y_795_, v___y_797_);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_815_, 0);
lean_dec(v_unused_823_);
v___x_817_ = v___x_815_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_dec(v___x_815_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v_a_814_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_814_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_813_, 1);
v_a_802_ = v_a_824_;
goto v___jp_801_;
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v___x_803_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_800_, v___y_795_, v___y_797_);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_803_, 0);
lean_dec(v_unused_811_);
v___x_805_ = v___x_803_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_dec(v___x_803_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 1);
lean_ctor_set(v___x_805_, 0, v_a_802_);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_802_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_825_, lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_825_, v_x_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_833_, lean_object* v_checkType_834_, uint8_t v_safety_835_, uint8_t v_checkMeta_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; lean_object* v_env_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_842_ = lean_st_ref_get(v_a_840_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v___x_844_ = lean_box(v_checkMeta_836_);
v___x_845_ = lean_box(v_safety_835_);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_846_, 0, v___x_844_);
lean_closure_set(v___f_846_, 1, v_checkType_834_);
lean_closure_set(v___f_846_, 2, v___x_845_);
lean_closure_set(v___f_846_, 3, v_value_833_);
v___x_847_ = l_Lean_Environment_unlockAsync(v_env_843_);
v___x_848_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_847_, v___f_846_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_849_, lean_object* v_checkType_850_, lean_object* v_safety_851_, lean_object* v_checkMeta_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
uint8_t v_safety_boxed_858_; uint8_t v_checkMeta_boxed_859_; lean_object* v_res_860_; 
v_safety_boxed_858_ = lean_unbox(v_safety_851_);
v_checkMeta_boxed_859_ = lean_unbox(v_checkMeta_852_);
v_res_860_ = l_Lean_Meta_evalExprCore___redArg(v_value_849_, v_checkType_850_, v_safety_boxed_858_, v_checkMeta_boxed_859_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_861_, lean_object* v_value_862_, lean_object* v_checkType_863_, uint8_t v_safety_864_, uint8_t v_checkMeta_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_evalExprCore___redArg(v_value_862_, v_checkType_863_, v_safety_864_, v_checkMeta_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_872_, lean_object* v_value_873_, lean_object* v_checkType_874_, lean_object* v_safety_875_, lean_object* v_checkMeta_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
uint8_t v_safety_boxed_882_; uint8_t v_checkMeta_boxed_883_; lean_object* v_res_884_; 
v_safety_boxed_882_ = lean_unbox(v_safety_875_);
v_checkMeta_boxed_883_ = lean_unbox(v_checkMeta_876_);
v_res_884_ = l_Lean_Meta_evalExprCore(v_00_u03b1_872_, v_value_873_, v_checkType_874_, v_safety_boxed_882_, v_checkMeta_boxed_883_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_899_, lean_object* v_constName_900_, uint8_t v_checkMeta_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_900_, v_checkMeta_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_908_, lean_object* v_constName_909_, lean_object* v_checkMeta_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v_checkMeta_boxed_916_; lean_object* v_res_917_; 
v_checkMeta_boxed_916_ = lean_unbox(v_checkMeta_910_);
v_res_917_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_908_, v_constName_909_, v_checkMeta_boxed_916_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_918_, lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_926_, lean_object* v_msg_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_926_, v_msg_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_934_, v___y_936_, v___y_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_948_, lean_object* v_env_949_, lean_object* v_x_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_949_, v_x_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_957_, lean_object* v_env_958_, lean_object* v_x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_957_, v_env_958_, v_x_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_966_, lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_974_, v_x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_981_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_985_, lean_object* v_type_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Meta_whnfD(v_type_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1006_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1006_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1006_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_Expr_isConstOf(v_a_993_, v_typeName_985_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_del_object(v___x_995_);
v___x_998_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_999_ = l_Lean_indentExpr(v_a_993_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1000_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_dec(v_a_993_);
v___x_1002_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1002_);
v___x_1004_ = v___x_995_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1007_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_992_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_992_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1015_, lean_object* v_type_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1015_, v_type_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v_typeName_1015_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1023_, lean_object* v_value_1024_, uint8_t v_safety_1025_, uint8_t v_checkMeta_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; 
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1032_, 0, v_typeName_1023_);
v___x_1033_ = l_Lean_Meta_evalExprCore___redArg(v_value_1024_, v___f_1032_, v_safety_1025_, v_checkMeta_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1034_, lean_object* v_value_1035_, lean_object* v_safety_1036_, lean_object* v_checkMeta_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_safety_boxed_1043_; uint8_t v_checkMeta_boxed_1044_; lean_object* v_res_1045_; 
v_safety_boxed_1043_ = lean_unbox(v_safety_1036_);
v_checkMeta_boxed_1044_ = lean_unbox(v_checkMeta_1037_);
v_res_1045_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1034_, v_value_1035_, v_safety_boxed_1043_, v_checkMeta_boxed_1044_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1046_, lean_object* v_typeName_1047_, lean_object* v_value_1048_, uint8_t v_safety_1049_, uint8_t v_checkMeta_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1047_, v_value_1048_, v_safety_1049_, v_checkMeta_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_typeName_1058_, lean_object* v_value_1059_, lean_object* v_safety_1060_, lean_object* v_checkMeta_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
uint8_t v_safety_boxed_1067_; uint8_t v_checkMeta_boxed_1068_; lean_object* v_res_1069_; 
v_safety_boxed_1067_ = lean_unbox(v_safety_1060_);
v_checkMeta_boxed_1068_ = lean_unbox(v_checkMeta_1061_);
v_res_1069_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1057_, v_typeName_1058_, v_value_1059_, v_safety_boxed_1067_, v_checkMeta_boxed_1068_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1069_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1075_, lean_object* v_type_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
lean_inc_ref(v_expectedType_1075_);
lean_inc_ref(v_type_1076_);
v___x_1082_ = l_Lean_Meta_isExprDefEq(v_type_1076_, v_expectedType_1075_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1107_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1107_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1107_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_unbox(v_a_1083_);
lean_dec(v_a_1083_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_del_object(v___x_1085_);
v___x_1088_ = lean_box(0);
v___x_1089_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1090_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1076_, v_expectedType_1075_, v___x_1088_, v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_a_1091_);
v___x_1094_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1093_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1094_;
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1090_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1090_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_dec_ref(v_type_1076_);
lean_dec_ref(v_expectedType_1075_);
v___x_1103_ = lean_box(0);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1103_);
v___x_1105_ = v___x_1085_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_type_1076_);
lean_dec_ref(v_expectedType_1075_);
v_a_1108_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1082_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1082_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1116_, lean_object* v_type_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1116_, v_type_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1124_, lean_object* v_value_1125_, uint8_t v_safety_1126_, uint8_t v_checkMeta_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___f_1133_; lean_object* v___x_1134_; 
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1133_, 0, v_expectedType_1124_);
v___x_1134_ = l_Lean_Meta_evalExprCore___redArg(v_value_1125_, v___f_1133_, v_safety_1126_, v_checkMeta_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1135_, lean_object* v_value_1136_, lean_object* v_safety_1137_, lean_object* v_checkMeta_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
uint8_t v_safety_boxed_1144_; uint8_t v_checkMeta_boxed_1145_; lean_object* v_res_1146_; 
v_safety_boxed_1144_ = lean_unbox(v_safety_1137_);
v_checkMeta_boxed_1145_ = lean_unbox(v_checkMeta_1138_);
v_res_1146_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1135_, v_value_1136_, v_safety_boxed_1144_, v_checkMeta_boxed_1145_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1147_, lean_object* v_expectedType_1148_, lean_object* v_value_1149_, uint8_t v_safety_1150_, uint8_t v_checkMeta_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1148_, v_value_1149_, v_safety_1150_, v_checkMeta_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_expectedType_1159_, lean_object* v_value_1160_, lean_object* v_safety_1161_, lean_object* v_checkMeta_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_safety_boxed_1168_; uint8_t v_checkMeta_boxed_1169_; lean_object* v_res_1170_; 
v_safety_boxed_1168_ = lean_unbox(v_safety_1161_);
v_checkMeta_boxed_1169_ = lean_unbox(v_checkMeta_1162_);
v_res_1170_ = l_Lean_Meta_evalExpr(v_00_u03b1_1158_, v_expectedType_1159_, v_value_1160_, v_safety_boxed_1168_, v_checkMeta_boxed_1169_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1170_;
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

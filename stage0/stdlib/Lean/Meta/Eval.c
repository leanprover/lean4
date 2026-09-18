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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
extern lean_object* l_Lean_diagnostics;
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
v___x_249_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___y_284_; uint8_t v___y_285_; uint8_t v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v_fileName_293_; lean_object* v_fileMap_294_; lean_object* v_currNamespace_295_; lean_object* v_openDecls_296_; lean_object* v_initHeartbeats_297_; lean_object* v_maxHeartbeats_298_; lean_object* v_quotContext_299_; lean_object* v_currMacroScope_300_; lean_object* v_cancelTk_x3f_301_; lean_object* v_inheritedTraceOptions_302_; lean_object* v_currRecDepth_303_; lean_object* v_ref_304_; uint8_t v_suppressElabErrors_305_; lean_object* v___y_306_; lean_object* v___y_321_; uint8_t v___y_322_; uint8_t v___y_323_; lean_object* v___y_324_; uint8_t v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_347_; uint8_t v___y_348_; lean_object* v___y_349_; uint8_t v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; uint8_t v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; uint8_t v___y_359_; lean_object* v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; uint8_t v___y_389_; lean_object* v___y_390_; lean_object* v_fileName_391_; lean_object* v_fileMap_392_; lean_object* v_currNamespace_393_; lean_object* v_openDecls_394_; lean_object* v_initHeartbeats_395_; lean_object* v_maxHeartbeats_396_; lean_object* v_quotContext_397_; lean_object* v_currMacroScope_398_; lean_object* v_cancelTk_x3f_399_; lean_object* v_inheritedTraceOptions_400_; lean_object* v_currRecDepth_401_; lean_object* v_ref_402_; uint8_t v_suppressElabErrors_403_; lean_object* v___y_404_; lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; uint8_t v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; uint8_t v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_443_; uint8_t v___y_444_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; uint8_t v___y_454_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_477_; uint8_t v___y_478_; lean_object* v___y_479_; uint8_t v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v_fileName_487_; lean_object* v_fileMap_488_; lean_object* v_currNamespace_489_; lean_object* v_openDecls_490_; lean_object* v_initHeartbeats_491_; lean_object* v_maxHeartbeats_492_; lean_object* v_quotContext_493_; lean_object* v_currMacroScope_494_; lean_object* v_cancelTk_x3f_495_; lean_object* v_inheritedTraceOptions_496_; lean_object* v_currRecDepth_497_; lean_object* v_ref_498_; uint8_t v_suppressElabErrors_499_; lean_object* v___y_500_; lean_object* v___y_512_; uint8_t v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; lean_object* v___y_516_; uint8_t v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_539_; uint8_t v___y_540_; uint8_t v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; uint8_t v___y_551_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v_nextMacroScope_720_; lean_object* v_ngen_721_; lean_object* v_auxDeclNGen_722_; lean_object* v_traceState_723_; lean_object* v_messages_724_; lean_object* v_infoState_725_; lean_object* v_snapshotTasks_726_; lean_object* v___y_727_; lean_object* v___x_746_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_746_ = lean_st_ref_get(v___y_281_);
lean_inc_ref(v_value_277_);
v___x_759_ = l_Lean_Expr_getUsedConstants(v_value_277_);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_array_get_size(v___x_759_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec_ref(v___x_759_);
lean_dec(v___x_746_);
goto v___jp_747_;
}
else
{
if (v___x_762_ == 0)
{
lean_dec_ref(v___x_759_);
lean_dec(v___x_746_);
goto v___jp_747_;
}
else
{
lean_object* v_env_763_; size_t v___x_764_; size_t v___x_765_; uint8_t v___x_766_; 
v_env_763_ = lean_ctor_get(v___x_746_, 0);
lean_inc_ref(v_env_763_);
lean_dec(v___x_746_);
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_761_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_763_, v___x_761_, v___x_759_, v___x_764_, v___x_765_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v_env_763_);
if (v___x_766_ == 0)
{
goto v___jp_747_;
}
else
{
goto v___jp_677_;
}
}
}
v___jp_283_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_284_, v___y_292_);
v___x_308_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_308_, 0, v_fileName_293_);
lean_ctor_set(v___x_308_, 1, v_fileMap_294_);
lean_ctor_set(v___x_308_, 2, v___y_284_);
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
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*3, v___y_286_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*3 + 1, v_suppressElabErrors_305_);
v___x_310_ = l_Lean_addAndCompile(v___y_290_, v___y_288_, v___y_285_, v___x_309_, v___y_306_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_311_; 
lean_dec_ref_known(v___x_310_, 1);
v___x_311_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_289_, v_checkMeta_274_, v___y_287_, v___y_291_, v___x_309_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref_known(v___x_309_, 3);
lean_dec(v___y_291_);
lean_dec_ref(v___y_287_);
return v___x_311_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref_known(v___x_309_, 3);
lean_dec(v___y_306_);
lean_dec(v___y_291_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_287_);
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
v___x_360_ = lean_st_ref_take(v___y_357_);
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
v___x_372_ = l_Lean_Kernel_enableDiag(v_env_361_, v___y_354_);
lean_inc_ref(v___y_351_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 5, v___y_351_);
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
lean_ctor_set(v_reuseFailAlloc_376_, 5, v___y_351_);
lean_ctor_set(v_reuseFailAlloc_376_, 6, v_messages_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 7, v_infoState_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 8, v_snapshotTasks_368_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_st_ref_put(v___y_357_, v___x_374_);
v___y_321_ = v___y_347_;
v___y_322_ = v___y_348_;
v___y_323_ = v___y_354_;
v___y_324_ = v___y_349_;
v___y_325_ = v___y_350_;
v___y_326_ = v___y_355_;
v___y_327_ = v___y_356_;
v___y_328_ = v___y_358_;
v___y_329_ = v___y_352_;
v___y_330_ = v___y_353_;
v___y_331_ = v___y_357_;
goto v___jp_320_;
}
}
}
else
{
v___y_321_ = v___y_347_;
v___y_322_ = v___y_348_;
v___y_323_ = v___y_354_;
v___y_324_ = v___y_349_;
v___y_325_ = v___y_350_;
v___y_326_ = v___y_355_;
v___y_327_ = v___y_356_;
v___y_328_ = v___y_358_;
v___y_329_ = v___y_352_;
v___y_330_ = v___y_353_;
v___y_331_ = v___y_357_;
goto v___jp_320_;
}
}
v___jp_379_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v_env_412_; uint8_t v___x_413_; 
v___x_405_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_382_, v___y_390_);
lean_inc_ref(v_inheritedTraceOptions_400_);
lean_inc(v_cancelTk_x3f_399_);
lean_inc(v_currMacroScope_398_);
lean_inc(v_quotContext_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc_ref(v___y_382_);
lean_inc_ref(v_fileMap_392_);
lean_inc_ref(v_fileName_391_);
v___x_406_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_406_, 0, v_fileName_391_);
lean_ctor_set(v___x_406_, 1, v_fileMap_392_);
lean_ctor_set(v___x_406_, 2, v___y_382_);
lean_ctor_set(v___x_406_, 3, v___x_405_);
lean_ctor_set(v___x_406_, 4, v_currNamespace_393_);
lean_ctor_set(v___x_406_, 5, v_openDecls_394_);
lean_ctor_set(v___x_406_, 6, v_initHeartbeats_395_);
lean_ctor_set(v___x_406_, 7, v_maxHeartbeats_396_);
lean_ctor_set(v___x_406_, 8, v_quotContext_397_);
lean_ctor_set(v___x_406_, 9, v_currMacroScope_398_);
lean_ctor_set(v___x_406_, 10, v_cancelTk_x3f_399_);
lean_ctor_set(v___x_406_, 11, v_inheritedTraceOptions_400_);
lean_inc(v_ref_402_);
lean_inc(v_currRecDepth_401_);
v___x_407_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_currRecDepth_401_);
lean_ctor_set(v___x_407_, 2, v_ref_402_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3, v___y_389_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3 + 1, v_suppressElabErrors_403_);
v___x_408_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_409_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_382_, v___x_408_, v___y_384_);
v___x_410_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_409_, v___y_380_);
v___x_411_ = lean_st_ref_get(v___y_404_);
v_env_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_env_412_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_412_);
lean_dec_ref(v_env_412_);
if (v___x_410_ == 0)
{
if (v___x_413_ == 0)
{
lean_dec_ref_known(v___x_407_, 3);
v___y_284_ = v___x_409_;
v___y_285_ = v___y_381_;
v___y_286_ = v___x_410_;
v___y_287_ = v___y_383_;
v___y_288_ = v___y_384_;
v___y_289_ = v___y_385_;
v___y_290_ = v___y_386_;
v___y_291_ = v___y_388_;
v___y_292_ = v___y_390_;
v_fileName_293_ = v_fileName_391_;
v_fileMap_294_ = v_fileMap_392_;
v_currNamespace_295_ = v_currNamespace_393_;
v_openDecls_296_ = v_openDecls_394_;
v_initHeartbeats_297_ = v_initHeartbeats_395_;
v_maxHeartbeats_298_ = v_maxHeartbeats_396_;
v_quotContext_299_ = v_quotContext_397_;
v_currMacroScope_300_ = v_currMacroScope_398_;
v_cancelTk_x3f_301_ = v_cancelTk_x3f_399_;
v_inheritedTraceOptions_302_ = v_inheritedTraceOptions_400_;
v_currRecDepth_303_ = v_currRecDepth_401_;
v_ref_304_ = v_ref_402_;
v_suppressElabErrors_305_ = v_suppressElabErrors_403_;
v___y_306_ = v___y_404_;
goto v___jp_283_;
}
else
{
lean_dec(v_ref_402_);
lean_dec(v_currRecDepth_401_);
lean_dec_ref(v_inheritedTraceOptions_400_);
lean_dec(v_cancelTk_x3f_399_);
lean_dec(v_currMacroScope_398_);
lean_dec(v_quotContext_397_);
lean_dec(v_maxHeartbeats_396_);
lean_dec(v_initHeartbeats_395_);
lean_dec(v_openDecls_394_);
lean_dec(v_currNamespace_393_);
lean_dec_ref(v_fileMap_392_);
lean_dec_ref(v_fileName_391_);
v___y_347_ = v___x_409_;
v___y_348_ = v___y_381_;
v___y_349_ = v___y_383_;
v___y_350_ = v___y_384_;
v___y_351_ = v___y_387_;
v___y_352_ = v___y_390_;
v___y_353_ = v___x_407_;
v___y_354_ = v___x_410_;
v___y_355_ = v___y_385_;
v___y_356_ = v___y_386_;
v___y_357_ = v___y_404_;
v___y_358_ = v___y_388_;
v___y_359_ = v___x_410_;
goto v___jp_346_;
}
}
else
{
lean_dec(v_ref_402_);
lean_dec(v_currRecDepth_401_);
lean_dec_ref(v_inheritedTraceOptions_400_);
lean_dec(v_cancelTk_x3f_399_);
lean_dec(v_currMacroScope_398_);
lean_dec(v_quotContext_397_);
lean_dec(v_maxHeartbeats_396_);
lean_dec(v_initHeartbeats_395_);
lean_dec(v_openDecls_394_);
lean_dec(v_currNamespace_393_);
lean_dec_ref(v_fileMap_392_);
lean_dec_ref(v_fileName_391_);
v___y_347_ = v___x_409_;
v___y_348_ = v___y_381_;
v___y_349_ = v___y_383_;
v___y_350_ = v___y_384_;
v___y_351_ = v___y_387_;
v___y_352_ = v___y_390_;
v___y_353_ = v___x_407_;
v___y_354_ = v___x_410_;
v___y_355_ = v___y_385_;
v___y_356_ = v___y_386_;
v___y_357_ = v___y_404_;
v___y_358_ = v___y_388_;
v___y_359_ = v___x_413_;
goto v___jp_346_;
}
}
v___jp_414_:
{
lean_object* v_toCold_428_; lean_object* v_currRecDepth_429_; lean_object* v_ref_430_; uint8_t v_suppressElabErrors_431_; lean_object* v_fileName_432_; lean_object* v_fileMap_433_; lean_object* v_currNamespace_434_; lean_object* v_openDecls_435_; lean_object* v_initHeartbeats_436_; lean_object* v_maxHeartbeats_437_; lean_object* v_quotContext_438_; lean_object* v_currMacroScope_439_; lean_object* v_cancelTk_x3f_440_; lean_object* v_inheritedTraceOptions_441_; 
v_toCold_428_ = lean_ctor_get(v___y_426_, 0);
lean_inc_ref(v_toCold_428_);
v_currRecDepth_429_ = lean_ctor_get(v___y_426_, 1);
lean_inc(v_currRecDepth_429_);
v_ref_430_ = lean_ctor_get(v___y_426_, 2);
lean_inc(v_ref_430_);
v_suppressElabErrors_431_ = lean_ctor_get_uint8(v___y_426_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_426_);
v_fileName_432_ = lean_ctor_get(v_toCold_428_, 0);
lean_inc_ref(v_fileName_432_);
v_fileMap_433_ = lean_ctor_get(v_toCold_428_, 1);
lean_inc_ref(v_fileMap_433_);
v_currNamespace_434_ = lean_ctor_get(v_toCold_428_, 4);
lean_inc(v_currNamespace_434_);
v_openDecls_435_ = lean_ctor_get(v_toCold_428_, 5);
lean_inc(v_openDecls_435_);
v_initHeartbeats_436_ = lean_ctor_get(v_toCold_428_, 6);
lean_inc(v_initHeartbeats_436_);
v_maxHeartbeats_437_ = lean_ctor_get(v_toCold_428_, 7);
lean_inc(v_maxHeartbeats_437_);
v_quotContext_438_ = lean_ctor_get(v_toCold_428_, 8);
lean_inc(v_quotContext_438_);
v_currMacroScope_439_ = lean_ctor_get(v_toCold_428_, 9);
lean_inc(v_currMacroScope_439_);
v_cancelTk_x3f_440_ = lean_ctor_get(v_toCold_428_, 10);
lean_inc(v_cancelTk_x3f_440_);
v_inheritedTraceOptions_441_ = lean_ctor_get(v_toCold_428_, 11);
lean_inc_ref(v_inheritedTraceOptions_441_);
lean_dec_ref(v_toCold_428_);
v___y_380_ = v___y_415_;
v___y_381_ = v___y_416_;
v___y_382_ = v___y_417_;
v___y_383_ = v___y_418_;
v___y_384_ = v___y_419_;
v___y_385_ = v___y_420_;
v___y_386_ = v___y_421_;
v___y_387_ = v___y_422_;
v___y_388_ = v___y_423_;
v___y_389_ = v___y_424_;
v___y_390_ = v___y_425_;
v_fileName_391_ = v_fileName_432_;
v_fileMap_392_ = v_fileMap_433_;
v_currNamespace_393_ = v_currNamespace_434_;
v_openDecls_394_ = v_openDecls_435_;
v_initHeartbeats_395_ = v_initHeartbeats_436_;
v_maxHeartbeats_396_ = v_maxHeartbeats_437_;
v_quotContext_397_ = v_quotContext_438_;
v_currMacroScope_398_ = v_currMacroScope_439_;
v_cancelTk_x3f_399_ = v_cancelTk_x3f_440_;
v_inheritedTraceOptions_400_ = v_inheritedTraceOptions_441_;
v_currRecDepth_401_ = v_currRecDepth_429_;
v_ref_402_ = v_ref_430_;
v_suppressElabErrors_403_ = v_suppressElabErrors_431_;
v___y_404_ = v___y_427_;
goto v___jp_379_;
}
v___jp_442_:
{
if (v___y_456_ == 0)
{
lean_object* v___x_457_; lean_object* v_env_458_; lean_object* v_nextMacroScope_459_; lean_object* v_ngen_460_; lean_object* v_auxDeclNGen_461_; lean_object* v_traceState_462_; lean_object* v_messages_463_; lean_object* v_infoState_464_; lean_object* v_snapshotTasks_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v___x_457_ = lean_st_ref_take(v___y_449_);
v_env_458_ = lean_ctor_get(v___x_457_, 0);
v_nextMacroScope_459_ = lean_ctor_get(v___x_457_, 1);
v_ngen_460_ = lean_ctor_get(v___x_457_, 2);
v_auxDeclNGen_461_ = lean_ctor_get(v___x_457_, 3);
v_traceState_462_ = lean_ctor_get(v___x_457_, 4);
v_messages_463_ = lean_ctor_get(v___x_457_, 6);
v_infoState_464_ = lean_ctor_get(v___x_457_, 7);
v_snapshotTasks_465_ = lean_ctor_get(v___x_457_, 8);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_457_, 5);
lean_dec(v_unused_475_);
v___x_467_ = v___x_457_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snapshotTasks_465_);
lean_inc(v_infoState_464_);
lean_inc(v_messages_463_);
lean_inc(v_traceState_462_);
lean_inc(v_auxDeclNGen_461_);
lean_inc(v_ngen_460_);
lean_inc(v_nextMacroScope_459_);
lean_inc(v_env_458_);
lean_dec(v___x_457_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = l_Lean_Kernel_enableDiag(v_env_458_, v___y_454_);
lean_inc_ref(v___y_447_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 5, v___y_447_);
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_nextMacroScope_459_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_ngen_460_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_auxDeclNGen_461_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_traceState_462_);
lean_ctor_set(v_reuseFailAlloc_473_, 5, v___y_447_);
lean_ctor_set(v_reuseFailAlloc_473_, 6, v_messages_463_);
lean_ctor_set(v_reuseFailAlloc_473_, 7, v_infoState_464_);
lean_ctor_set(v_reuseFailAlloc_473_, 8, v_snapshotTasks_465_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_st_ref_put(v___y_449_, v___x_471_);
v___y_415_ = v___y_443_;
v___y_416_ = v___y_444_;
v___y_417_ = v___y_450_;
v___y_418_ = v___y_445_;
v___y_419_ = v___y_446_;
v___y_420_ = v___y_451_;
v___y_421_ = v___y_452_;
v___y_422_ = v___y_447_;
v___y_423_ = v___y_453_;
v___y_424_ = v___y_454_;
v___y_425_ = v___y_448_;
v___y_426_ = v___y_455_;
v___y_427_ = v___y_449_;
goto v___jp_414_;
}
}
}
else
{
v___y_415_ = v___y_443_;
v___y_416_ = v___y_444_;
v___y_417_ = v___y_450_;
v___y_418_ = v___y_445_;
v___y_419_ = v___y_446_;
v___y_420_ = v___y_451_;
v___y_421_ = v___y_452_;
v___y_422_ = v___y_447_;
v___y_423_ = v___y_453_;
v___y_424_ = v___y_454_;
v___y_425_ = v___y_448_;
v___y_426_ = v___y_455_;
v___y_427_ = v___y_449_;
goto v___jp_414_;
}
}
v___jp_476_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v_env_509_; uint8_t v___x_510_; 
v___x_501_ = l_Lean_maxRecDepth;
v___x_502_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_479_, v___x_501_);
lean_inc_ref(v_inheritedTraceOptions_496_);
lean_inc(v_cancelTk_x3f_495_);
lean_inc(v_currMacroScope_494_);
lean_inc(v_quotContext_493_);
lean_inc(v_maxHeartbeats_492_);
lean_inc(v_initHeartbeats_491_);
lean_inc(v_openDecls_490_);
lean_inc(v_currNamespace_489_);
lean_inc_ref(v___y_479_);
lean_inc_ref(v_fileMap_488_);
lean_inc_ref(v_fileName_487_);
v___x_503_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_503_, 0, v_fileName_487_);
lean_ctor_set(v___x_503_, 1, v_fileMap_488_);
lean_ctor_set(v___x_503_, 2, v___y_479_);
lean_ctor_set(v___x_503_, 3, v___x_502_);
lean_ctor_set(v___x_503_, 4, v_currNamespace_489_);
lean_ctor_set(v___x_503_, 5, v_openDecls_490_);
lean_ctor_set(v___x_503_, 6, v_initHeartbeats_491_);
lean_ctor_set(v___x_503_, 7, v_maxHeartbeats_492_);
lean_ctor_set(v___x_503_, 8, v_quotContext_493_);
lean_ctor_set(v___x_503_, 9, v_currMacroScope_494_);
lean_ctor_set(v___x_503_, 10, v_cancelTk_x3f_495_);
lean_ctor_set(v___x_503_, 11, v_inheritedTraceOptions_496_);
lean_inc(v_ref_498_);
lean_inc(v_currRecDepth_497_);
v___x_504_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_currRecDepth_497_);
lean_ctor_set(v___x_504_, 2, v_ref_498_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3, v___y_482_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3 + 1, v_suppressElabErrors_499_);
v___x_505_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_506_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_479_, v___x_505_, v___y_478_);
v___x_507_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_506_, v___y_477_);
v___x_508_ = lean_st_ref_get(v___y_500_);
v_env_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc_ref(v_env_509_);
lean_dec(v___x_508_);
v___x_510_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_509_);
lean_dec_ref(v_env_509_);
if (v___x_507_ == 0)
{
if (v___x_510_ == 0)
{
lean_dec_ref_known(v___x_504_, 3);
v___y_380_ = v___y_477_;
v___y_381_ = v___y_478_;
v___y_382_ = v___x_506_;
v___y_383_ = v___y_481_;
v___y_384_ = v___y_480_;
v___y_385_ = v___y_483_;
v___y_386_ = v___y_484_;
v___y_387_ = v___y_485_;
v___y_388_ = v___y_486_;
v___y_389_ = v___x_507_;
v___y_390_ = v___x_501_;
v_fileName_391_ = v_fileName_487_;
v_fileMap_392_ = v_fileMap_488_;
v_currNamespace_393_ = v_currNamespace_489_;
v_openDecls_394_ = v_openDecls_490_;
v_initHeartbeats_395_ = v_initHeartbeats_491_;
v_maxHeartbeats_396_ = v_maxHeartbeats_492_;
v_quotContext_397_ = v_quotContext_493_;
v_currMacroScope_398_ = v_currMacroScope_494_;
v_cancelTk_x3f_399_ = v_cancelTk_x3f_495_;
v_inheritedTraceOptions_400_ = v_inheritedTraceOptions_496_;
v_currRecDepth_401_ = v_currRecDepth_497_;
v_ref_402_ = v_ref_498_;
v_suppressElabErrors_403_ = v_suppressElabErrors_499_;
v___y_404_ = v___y_500_;
goto v___jp_379_;
}
else
{
lean_dec(v_ref_498_);
lean_dec(v_currRecDepth_497_);
lean_dec_ref(v_inheritedTraceOptions_496_);
lean_dec(v_cancelTk_x3f_495_);
lean_dec(v_currMacroScope_494_);
lean_dec(v_quotContext_493_);
lean_dec(v_maxHeartbeats_492_);
lean_dec(v_initHeartbeats_491_);
lean_dec(v_openDecls_490_);
lean_dec(v_currNamespace_489_);
lean_dec_ref(v_fileMap_488_);
lean_dec_ref(v_fileName_487_);
v___y_443_ = v___y_477_;
v___y_444_ = v___y_478_;
v___y_445_ = v___y_481_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_485_;
v___y_448_ = v___x_501_;
v___y_449_ = v___y_500_;
v___y_450_ = v___x_506_;
v___y_451_ = v___y_483_;
v___y_452_ = v___y_484_;
v___y_453_ = v___y_486_;
v___y_454_ = v___x_507_;
v___y_455_ = v___x_504_;
v___y_456_ = v___x_507_;
goto v___jp_442_;
}
}
else
{
lean_dec(v_ref_498_);
lean_dec(v_currRecDepth_497_);
lean_dec_ref(v_inheritedTraceOptions_496_);
lean_dec(v_cancelTk_x3f_495_);
lean_dec(v_currMacroScope_494_);
lean_dec(v_quotContext_493_);
lean_dec(v_maxHeartbeats_492_);
lean_dec(v_initHeartbeats_491_);
lean_dec(v_openDecls_490_);
lean_dec(v_currNamespace_489_);
lean_dec_ref(v_fileMap_488_);
lean_dec_ref(v_fileName_487_);
v___y_443_ = v___y_477_;
v___y_444_ = v___y_478_;
v___y_445_ = v___y_481_;
v___y_446_ = v___y_480_;
v___y_447_ = v___y_485_;
v___y_448_ = v___x_501_;
v___y_449_ = v___y_500_;
v___y_450_ = v___x_506_;
v___y_451_ = v___y_483_;
v___y_452_ = v___y_484_;
v___y_453_ = v___y_486_;
v___y_454_ = v___x_507_;
v___y_455_ = v___x_504_;
v___y_456_ = v___x_510_;
goto v___jp_442_;
}
}
v___jp_511_:
{
lean_object* v_toCold_524_; lean_object* v_currRecDepth_525_; lean_object* v_ref_526_; uint8_t v_suppressElabErrors_527_; lean_object* v_fileName_528_; lean_object* v_fileMap_529_; lean_object* v_currNamespace_530_; lean_object* v_openDecls_531_; lean_object* v_initHeartbeats_532_; lean_object* v_maxHeartbeats_533_; lean_object* v_quotContext_534_; lean_object* v_currMacroScope_535_; lean_object* v_cancelTk_x3f_536_; lean_object* v_inheritedTraceOptions_537_; 
v_toCold_524_ = lean_ctor_get(v___y_522_, 0);
lean_inc_ref(v_toCold_524_);
v_currRecDepth_525_ = lean_ctor_get(v___y_522_, 1);
lean_inc(v_currRecDepth_525_);
v_ref_526_ = lean_ctor_get(v___y_522_, 2);
lean_inc(v_ref_526_);
v_suppressElabErrors_527_ = lean_ctor_get_uint8(v___y_522_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_522_);
v_fileName_528_ = lean_ctor_get(v_toCold_524_, 0);
lean_inc_ref(v_fileName_528_);
v_fileMap_529_ = lean_ctor_get(v_toCold_524_, 1);
lean_inc_ref(v_fileMap_529_);
v_currNamespace_530_ = lean_ctor_get(v_toCold_524_, 4);
lean_inc(v_currNamespace_530_);
v_openDecls_531_ = lean_ctor_get(v_toCold_524_, 5);
lean_inc(v_openDecls_531_);
v_initHeartbeats_532_ = lean_ctor_get(v_toCold_524_, 6);
lean_inc(v_initHeartbeats_532_);
v_maxHeartbeats_533_ = lean_ctor_get(v_toCold_524_, 7);
lean_inc(v_maxHeartbeats_533_);
v_quotContext_534_ = lean_ctor_get(v_toCold_524_, 8);
lean_inc(v_quotContext_534_);
v_currMacroScope_535_ = lean_ctor_get(v_toCold_524_, 9);
lean_inc(v_currMacroScope_535_);
v_cancelTk_x3f_536_ = lean_ctor_get(v_toCold_524_, 10);
lean_inc(v_cancelTk_x3f_536_);
v_inheritedTraceOptions_537_ = lean_ctor_get(v_toCold_524_, 11);
lean_inc_ref(v_inheritedTraceOptions_537_);
lean_dec_ref(v_toCold_524_);
v___y_477_ = v___y_512_;
v___y_478_ = v___y_513_;
v___y_479_ = v___y_514_;
v___y_480_ = v___y_515_;
v___y_481_ = v___y_516_;
v___y_482_ = v___y_517_;
v___y_483_ = v___y_518_;
v___y_484_ = v___y_519_;
v___y_485_ = v___y_520_;
v___y_486_ = v___y_521_;
v_fileName_487_ = v_fileName_528_;
v_fileMap_488_ = v_fileMap_529_;
v_currNamespace_489_ = v_currNamespace_530_;
v_openDecls_490_ = v_openDecls_531_;
v_initHeartbeats_491_ = v_initHeartbeats_532_;
v_maxHeartbeats_492_ = v_maxHeartbeats_533_;
v_quotContext_493_ = v_quotContext_534_;
v_currMacroScope_494_ = v_currMacroScope_535_;
v_cancelTk_x3f_495_ = v_cancelTk_x3f_536_;
v_inheritedTraceOptions_496_ = v_inheritedTraceOptions_537_;
v_currRecDepth_497_ = v_currRecDepth_525_;
v_ref_498_ = v_ref_526_;
v_suppressElabErrors_499_ = v_suppressElabErrors_527_;
v___y_500_ = v___y_523_;
goto v___jp_476_;
}
v___jp_538_:
{
if (v___y_551_ == 0)
{
lean_object* v___x_552_; lean_object* v_env_553_; lean_object* v_nextMacroScope_554_; lean_object* v_ngen_555_; lean_object* v_auxDeclNGen_556_; lean_object* v_traceState_557_; lean_object* v_messages_558_; lean_object* v_infoState_559_; lean_object* v_snapshotTasks_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v___x_552_ = lean_st_ref_take(v___y_546_);
v_env_553_ = lean_ctor_get(v___x_552_, 0);
v_nextMacroScope_554_ = lean_ctor_get(v___x_552_, 1);
v_ngen_555_ = lean_ctor_get(v___x_552_, 2);
v_auxDeclNGen_556_ = lean_ctor_get(v___x_552_, 3);
v_traceState_557_ = lean_ctor_get(v___x_552_, 4);
v_messages_558_ = lean_ctor_get(v___x_552_, 6);
v_infoState_559_ = lean_ctor_get(v___x_552_, 7);
v_snapshotTasks_560_ = lean_ctor_get(v___x_552_, 8);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_552_, 5);
lean_dec(v_unused_570_);
v___x_562_ = v___x_552_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snapshotTasks_560_);
lean_inc(v_infoState_559_);
lean_inc(v_messages_558_);
lean_inc(v_traceState_557_);
lean_inc(v_auxDeclNGen_556_);
lean_inc(v_ngen_555_);
lean_inc(v_nextMacroScope_554_);
lean_inc(v_env_553_);
lean_dec(v___x_552_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = l_Lean_Kernel_enableDiag(v_env_553_, v___y_541_);
lean_inc_ref(v___y_544_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 5, v___y_544_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_nextMacroScope_554_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_ngen_555_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_auxDeclNGen_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_traceState_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 5, v___y_544_);
lean_ctor_set(v_reuseFailAlloc_568_, 6, v_messages_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 7, v_infoState_559_);
lean_ctor_set(v_reuseFailAlloc_568_, 8, v_snapshotTasks_560_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_st_ref_put(v___y_546_, v___x_566_);
v___y_512_ = v___y_539_;
v___y_513_ = v___y_540_;
v___y_514_ = v___y_545_;
v___y_515_ = v___y_542_;
v___y_516_ = v___y_543_;
v___y_517_ = v___y_541_;
v___y_518_ = v___y_547_;
v___y_519_ = v___y_548_;
v___y_520_ = v___y_544_;
v___y_521_ = v___y_549_;
v___y_522_ = v___y_550_;
v___y_523_ = v___y_546_;
goto v___jp_511_;
}
}
}
else
{
v___y_512_ = v___y_539_;
v___y_513_ = v___y_540_;
v___y_514_ = v___y_545_;
v___y_515_ = v___y_542_;
v___y_516_ = v___y_543_;
v___y_517_ = v___y_541_;
v___y_518_ = v___y_547_;
v___y_519_ = v___y_548_;
v___y_520_ = v___y_544_;
v___y_521_ = v___y_549_;
v___y_522_ = v___y_550_;
v___y_523_ = v___y_546_;
goto v___jp_511_;
}
}
v___jp_571_:
{
lean_object* v___x_580_; 
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
lean_inc(v___y_577_);
lean_inc_ref(v___y_576_);
lean_inc_ref(v___y_572_);
v___x_580_ = lean_infer_type(v___y_572_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc_n(v_a_581_, 2);
lean_dec_ref_known(v___x_580_, 1);
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
lean_inc(v___y_577_);
lean_inc_ref(v___y_576_);
v___x_582_ = lean_apply_6(v_checkType_275_, v_a_581_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, lean_box(0));
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_env_590_; lean_object* v_nextMacroScope_591_; lean_object* v_ngen_592_; lean_object* v_auxDeclNGen_593_; lean_object* v_traceState_594_; lean_object* v_messages_595_; lean_object* v_infoState_596_; lean_object* v_snapshotTasks_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref_known(v___x_582_, 1);
v___x_583_ = lean_array_to_list(v___y_573_);
lean_inc_n(v___y_574_, 2);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v___y_574_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
lean_ctor_set(v___x_584_, 2, v_a_581_);
v___x_585_ = lean_box(0);
lean_inc(v___y_575_);
v___x_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_586_, 0, v___y_574_);
lean_ctor_set(v___x_586_, 1, v___y_575_);
v___x_587_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_587_, 0, v___x_584_);
lean_ctor_set(v___x_587_, 1, v___y_572_);
lean_ctor_set(v___x_587_, 2, v___x_585_);
lean_ctor_set(v___x_587_, 3, v___x_586_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*4, v_safety_276_);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
v___x_589_ = lean_st_ref_take(v___y_579_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
v_nextMacroScope_591_ = lean_ctor_get(v___x_589_, 1);
v_ngen_592_ = lean_ctor_get(v___x_589_, 2);
v_auxDeclNGen_593_ = lean_ctor_get(v___x_589_, 3);
v_traceState_594_ = lean_ctor_get(v___x_589_, 4);
v_messages_595_ = lean_ctor_get(v___x_589_, 6);
v_infoState_596_ = lean_ctor_get(v___x_589_, 7);
v_snapshotTasks_597_ = lean_ctor_get(v___x_589_, 8);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_589_, 5);
lean_dec(v_unused_660_);
v___x_599_ = v___x_589_;
v_isShared_600_ = v_isSharedCheck_659_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snapshotTasks_597_);
lean_inc(v_infoState_596_);
lean_inc(v_messages_595_);
lean_inc(v_traceState_594_);
lean_inc(v_auxDeclNGen_593_);
lean_inc(v_ngen_592_);
lean_inc(v_nextMacroScope_591_);
lean_inc(v_env_590_);
lean_dec(v___x_589_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_659_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_inc(v___y_574_);
v___x_601_ = l_Lean_markMeta(v_env_590_, v___y_574_);
v___x_602_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 5, v___x_602_);
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_nextMacroScope_591_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_ngen_592_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_auxDeclNGen_593_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_traceState_594_);
lean_ctor_set(v_reuseFailAlloc_658_, 5, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_658_, 6, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_658_, 7, v_infoState_596_);
lean_ctor_set(v_reuseFailAlloc_658_, 8, v_snapshotTasks_597_);
v___x_604_ = v_reuseFailAlloc_658_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_mctx_607_; lean_object* v_zetaDeltaFVarIds_608_; lean_object* v_postponed_609_; lean_object* v_diag_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_656_; 
v___x_605_ = lean_st_ref_put(v___y_579_, v___x_604_);
v___x_606_ = lean_st_ref_take(v___y_577_);
v_mctx_607_ = lean_ctor_get(v___x_606_, 0);
v_zetaDeltaFVarIds_608_ = lean_ctor_get(v___x_606_, 2);
v_postponed_609_ = lean_ctor_get(v___x_606_, 3);
v_diag_610_ = lean_ctor_get(v___x_606_, 4);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_606_, 1);
lean_dec(v_unused_657_);
v___x_612_ = v___x_606_;
v_isShared_613_ = v_isSharedCheck_656_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_diag_610_);
lean_inc(v_postponed_609_);
lean_inc(v_zetaDeltaFVarIds_608_);
lean_inc(v_mctx_607_);
lean_dec(v___x_606_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_656_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_mctx_607_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_zetaDeltaFVarIds_608_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_postponed_609_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_diag_610_);
v___x_616_ = v_reuseFailAlloc_655_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_env_619_; lean_object* v_checked_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_617_ = lean_st_ref_put(v___y_577_, v___x_616_);
v___x_618_ = lean_st_ref_get(v___y_579_);
v_env_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_env_619_);
lean_dec(v___x_618_);
v_checked_620_ = lean_ctor_get(v_env_619_, 2);
lean_inc_ref(v_checked_620_);
lean_dec_ref(v_env_619_);
v___x_621_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_622_ = l_Lean_traceBlock___redArg(v___x_621_, v_checked_620_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_toCold_623_; lean_object* v_currRecDepth_624_; lean_object* v_ref_625_; uint8_t v_suppressElabErrors_626_; lean_object* v_fileName_627_; lean_object* v_fileMap_628_; lean_object* v_options_629_; lean_object* v_currNamespace_630_; lean_object* v_openDecls_631_; lean_object* v_initHeartbeats_632_; lean_object* v_maxHeartbeats_633_; lean_object* v_quotContext_634_; lean_object* v_currMacroScope_635_; lean_object* v_cancelTk_x3f_636_; lean_object* v_inheritedTraceOptions_637_; uint8_t v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v_env_645_; uint8_t v___x_646_; 
lean_dec_ref_known(v___x_622_, 1);
v_toCold_623_ = lean_ctor_get(v___y_578_, 0);
v_currRecDepth_624_ = lean_ctor_get(v___y_578_, 1);
v_ref_625_ = lean_ctor_get(v___y_578_, 2);
v_suppressElabErrors_626_ = lean_ctor_get_uint8(v___y_578_, sizeof(void*)*3 + 1);
v_fileName_627_ = lean_ctor_get(v_toCold_623_, 0);
v_fileMap_628_ = lean_ctor_get(v_toCold_623_, 1);
v_options_629_ = lean_ctor_get(v_toCold_623_, 2);
v_currNamespace_630_ = lean_ctor_get(v_toCold_623_, 4);
v_openDecls_631_ = lean_ctor_get(v_toCold_623_, 5);
v_initHeartbeats_632_ = lean_ctor_get(v_toCold_623_, 6);
v_maxHeartbeats_633_ = lean_ctor_get(v_toCold_623_, 7);
v_quotContext_634_ = lean_ctor_get(v_toCold_623_, 8);
v_currMacroScope_635_ = lean_ctor_get(v_toCold_623_, 9);
v_cancelTk_x3f_636_ = lean_ctor_get(v_toCold_623_, 10);
v_inheritedTraceOptions_637_ = lean_ctor_get(v_toCold_623_, 11);
v___x_638_ = 1;
v___x_639_ = 0;
v___x_640_ = l_Lean_Elab_async;
lean_inc_ref(v_options_629_);
v___x_641_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_629_, v___x_640_, v___x_639_);
v___x_642_ = l_Lean_diagnostics;
v___x_643_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_641_, v___x_642_);
v___x_644_ = lean_st_ref_get(v___y_579_);
v_env_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc_ref(v_env_645_);
lean_dec(v___x_644_);
v___x_646_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_645_);
lean_dec_ref(v_env_645_);
if (v___x_643_ == 0)
{
if (v___x_646_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_637_);
lean_inc(v_cancelTk_x3f_636_);
lean_inc(v_currMacroScope_635_);
lean_inc(v_quotContext_634_);
lean_inc(v_maxHeartbeats_633_);
lean_inc(v_initHeartbeats_632_);
lean_inc(v_openDecls_631_);
lean_inc(v_currNamespace_630_);
lean_inc_ref(v_fileMap_628_);
lean_inc_ref(v_fileName_627_);
lean_inc(v_ref_625_);
lean_inc(v_currRecDepth_624_);
lean_dec_ref(v___y_578_);
v___y_477_ = v___x_642_;
v___y_478_ = v___x_639_;
v___y_479_ = v___x_641_;
v___y_480_ = v___x_638_;
v___y_481_ = v___y_576_;
v___y_482_ = v___x_643_;
v___y_483_ = v___y_574_;
v___y_484_ = v___x_588_;
v___y_485_ = v___x_602_;
v___y_486_ = v___y_577_;
v_fileName_487_ = v_fileName_627_;
v_fileMap_488_ = v_fileMap_628_;
v_currNamespace_489_ = v_currNamespace_630_;
v_openDecls_490_ = v_openDecls_631_;
v_initHeartbeats_491_ = v_initHeartbeats_632_;
v_maxHeartbeats_492_ = v_maxHeartbeats_633_;
v_quotContext_493_ = v_quotContext_634_;
v_currMacroScope_494_ = v_currMacroScope_635_;
v_cancelTk_x3f_495_ = v_cancelTk_x3f_636_;
v_inheritedTraceOptions_496_ = v_inheritedTraceOptions_637_;
v_currRecDepth_497_ = v_currRecDepth_624_;
v_ref_498_ = v_ref_625_;
v_suppressElabErrors_499_ = v_suppressElabErrors_626_;
v___y_500_ = v___y_579_;
goto v___jp_476_;
}
else
{
v___y_539_ = v___x_642_;
v___y_540_ = v___x_639_;
v___y_541_ = v___x_643_;
v___y_542_ = v___x_638_;
v___y_543_ = v___y_576_;
v___y_544_ = v___x_602_;
v___y_545_ = v___x_641_;
v___y_546_ = v___y_579_;
v___y_547_ = v___y_574_;
v___y_548_ = v___x_588_;
v___y_549_ = v___y_577_;
v___y_550_ = v___y_578_;
v___y_551_ = v___x_643_;
goto v___jp_538_;
}
}
else
{
v___y_539_ = v___x_642_;
v___y_540_ = v___x_639_;
v___y_541_ = v___x_643_;
v___y_542_ = v___x_638_;
v___y_543_ = v___y_576_;
v___y_544_ = v___x_602_;
v___y_545_ = v___x_641_;
v___y_546_ = v___y_579_;
v___y_547_ = v___y_574_;
v___y_548_ = v___x_588_;
v___y_549_ = v___y_577_;
v___y_550_ = v___y_578_;
v___y_551_ = v___x_646_;
goto v___jp_538_;
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref_known(v___x_588_, 1);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_574_);
v_a_647_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_622_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_622_);
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
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_a_581_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v___y_572_);
v_a_661_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_582_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_582_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec_ref(v_checkType_275_);
v_a_669_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_580_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_580_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
v___jp_677_:
{
lean_object* v___x_678_; lean_object* v_env_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = lean_st_ref_get(v___y_281_);
v_env_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc_ref(v_env_679_);
lean_dec(v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_681_ = l_Lean_Core_mkFreshUserName(v___x_680_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = l_Lean_mkPrivateName(v_env_679_, v_a_682_);
lean_dec_ref(v_env_679_);
v___x_684_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_277_, v___y_279_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_params_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_n(v_a_685_, 2);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_687_ = l_Lean_collectLevelParams(v___x_686_, v_a_685_);
v_params_688_ = lean_ctor_get(v___x_687_, 2);
lean_inc_ref(v_params_688_);
lean_dec_ref(v___x_687_);
v___x_689_ = lean_box(0);
v___x_690_ = l_Lean_Expr_hasMVar(v_a_685_);
if (v___x_690_ == 0)
{
v___y_572_ = v_a_685_;
v___y_573_ = v_params_688_;
v___y_574_ = v___x_683_;
v___y_575_ = v___x_689_;
v___y_576_ = v___y_278_;
v___y_577_ = v___y_279_;
v___y_578_ = v___y_280_;
v___y_579_ = v___y_281_;
goto v___jp_571_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_685_);
v___x_692_ = l_Lean_indentExpr(v_a_685_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_693_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_dec_ref_known(v___x_694_, 1);
v___y_572_ = v_a_685_;
v___y_573_ = v_params_688_;
v___y_574_ = v___x_683_;
v___y_575_ = v___x_689_;
v___y_576_ = v___y_278_;
v___y_577_ = v___y_279_;
v___y_578_ = v___y_280_;
v___y_579_ = v___y_281_;
goto v___jp_571_;
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v_params_688_);
lean_dec(v_a_685_);
lean_dec(v___x_683_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec_ref(v_checkType_275_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
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
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v___x_683_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec_ref(v_checkType_275_);
v_a_703_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_684_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_684_);
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
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_env_679_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec_ref(v_value_277_);
lean_dec_ref(v_checkType_275_);
v_a_711_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_681_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_681_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
v___jp_719_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_mctx_732_; lean_object* v_zetaDeltaFVarIds_733_; lean_object* v_postponed_734_; lean_object* v_diag_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_744_; 
v___x_728_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_729_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_729_, 0, v___y_727_);
lean_ctor_set(v___x_729_, 1, v_nextMacroScope_720_);
lean_ctor_set(v___x_729_, 2, v_ngen_721_);
lean_ctor_set(v___x_729_, 3, v_auxDeclNGen_722_);
lean_ctor_set(v___x_729_, 4, v_traceState_723_);
lean_ctor_set(v___x_729_, 5, v___x_728_);
lean_ctor_set(v___x_729_, 6, v_messages_724_);
lean_ctor_set(v___x_729_, 7, v_infoState_725_);
lean_ctor_set(v___x_729_, 8, v_snapshotTasks_726_);
v___x_730_ = lean_st_ref_put(v___y_281_, v___x_729_);
v___x_731_ = lean_st_ref_take(v___y_279_);
v_mctx_732_ = lean_ctor_get(v___x_731_, 0);
v_zetaDeltaFVarIds_733_ = lean_ctor_get(v___x_731_, 2);
v_postponed_734_ = lean_ctor_get(v___x_731_, 3);
v_diag_735_ = lean_ctor_get(v___x_731_, 4);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v___x_731_, 1);
lean_dec(v_unused_745_);
v___x_737_ = v___x_731_;
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_diag_735_);
lean_inc(v_postponed_734_);
lean_inc(v_zetaDeltaFVarIds_733_);
lean_inc(v_mctx_732_);
lean_dec(v___x_731_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_mctx_732_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_zetaDeltaFVarIds_733_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_postponed_734_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_diag_735_);
v___x_741_ = v_reuseFailAlloc_743_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_st_ref_put(v___y_279_, v___x_741_);
goto v___jp_677_;
}
}
}
v___jp_747_:
{
lean_object* v___x_748_; lean_object* v_env_749_; lean_object* v_nextMacroScope_750_; lean_object* v_ngen_751_; lean_object* v_auxDeclNGen_752_; lean_object* v_traceState_753_; lean_object* v_messages_754_; lean_object* v_infoState_755_; lean_object* v_snapshotTasks_756_; lean_object* v___x_757_; 
v___x_748_ = lean_st_ref_take(v___y_281_);
v_env_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_ref_n(v_env_749_, 2);
v_nextMacroScope_750_ = lean_ctor_get(v___x_748_, 1);
lean_inc(v_nextMacroScope_750_);
v_ngen_751_ = lean_ctor_get(v___x_748_, 2);
lean_inc_ref(v_ngen_751_);
v_auxDeclNGen_752_ = lean_ctor_get(v___x_748_, 3);
lean_inc_ref(v_auxDeclNGen_752_);
v_traceState_753_ = lean_ctor_get(v___x_748_, 4);
lean_inc_ref(v_traceState_753_);
v_messages_754_ = lean_ctor_get(v___x_748_, 6);
lean_inc_ref(v_messages_754_);
v_infoState_755_ = lean_ctor_get(v___x_748_, 7);
lean_inc_ref(v_infoState_755_);
v_snapshotTasks_756_ = lean_ctor_get(v___x_748_, 8);
lean_inc_ref(v_snapshotTasks_756_);
lean_dec(v___x_748_);
v___x_757_ = l_Lean_Environment_importEnv_x3f(v_env_749_);
if (lean_obj_tag(v___x_757_) == 0)
{
v_nextMacroScope_720_ = v_nextMacroScope_750_;
v_ngen_721_ = v_ngen_751_;
v_auxDeclNGen_722_ = v_auxDeclNGen_752_;
v_traceState_723_ = v_traceState_753_;
v_messages_724_ = v_messages_754_;
v_infoState_725_ = v_infoState_755_;
v_snapshotTasks_726_ = v_snapshotTasks_756_;
v___y_727_ = v_env_749_;
goto v___jp_719_;
}
else
{
lean_object* v_val_758_; 
lean_dec_ref(v_env_749_);
v_val_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v___x_757_, 1);
v_nextMacroScope_720_ = v_nextMacroScope_750_;
v_ngen_721_ = v_ngen_751_;
v_auxDeclNGen_722_ = v_auxDeclNGen_752_;
v_traceState_723_ = v_traceState_753_;
v_messages_724_ = v_messages_754_;
v_infoState_725_ = v_infoState_755_;
v_snapshotTasks_726_ = v_snapshotTasks_756_;
v___y_727_ = v_val_758_;
goto v___jp_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_767_, lean_object* v_checkType_768_, lean_object* v_safety_769_, lean_object* v_value_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v_checkMeta_boxed_776_; uint8_t v_safety_boxed_777_; lean_object* v_res_778_; 
v_checkMeta_boxed_776_ = lean_unbox(v_checkMeta_767_);
v_safety_boxed_777_ = lean_unbox(v_safety_769_);
v_res_778_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_776_, v_checkType_768_, v_safety_boxed_777_, v_value_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; lean_object* v_nextMacroScope_784_; lean_object* v_ngen_785_; lean_object* v_auxDeclNGen_786_; lean_object* v_traceState_787_; lean_object* v_messages_788_; lean_object* v_infoState_789_; lean_object* v_snapshotTasks_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_816_; 
v___x_783_ = lean_st_ref_take(v___y_781_);
v_nextMacroScope_784_ = lean_ctor_get(v___x_783_, 1);
v_ngen_785_ = lean_ctor_get(v___x_783_, 2);
v_auxDeclNGen_786_ = lean_ctor_get(v___x_783_, 3);
v_traceState_787_ = lean_ctor_get(v___x_783_, 4);
v_messages_788_ = lean_ctor_get(v___x_783_, 6);
v_infoState_789_ = lean_ctor_get(v___x_783_, 7);
v_snapshotTasks_790_ = lean_ctor_get(v___x_783_, 8);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_817_ = lean_ctor_get(v___x_783_, 5);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_818_);
v___x_792_ = v___x_783_;
v_isShared_793_ = v_isSharedCheck_816_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snapshotTasks_790_);
lean_inc(v_infoState_789_);
lean_inc(v_messages_788_);
lean_inc(v_traceState_787_);
lean_inc(v_auxDeclNGen_786_);
lean_inc(v_ngen_785_);
lean_inc(v_nextMacroScope_784_);
lean_dec(v___x_783_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_816_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 5, v___x_794_);
lean_ctor_set(v___x_792_, 0, v_env_779_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_env_779_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_nextMacroScope_784_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_ngen_785_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_auxDeclNGen_786_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_traceState_787_);
lean_ctor_set(v_reuseFailAlloc_815_, 5, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_815_, 6, v_messages_788_);
lean_ctor_set(v_reuseFailAlloc_815_, 7, v_infoState_789_);
lean_ctor_set(v_reuseFailAlloc_815_, 8, v_snapshotTasks_790_);
v___x_796_ = v_reuseFailAlloc_815_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_mctx_799_; lean_object* v_zetaDeltaFVarIds_800_; lean_object* v_postponed_801_; lean_object* v_diag_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_813_; 
v___x_797_ = lean_st_ref_put(v___y_781_, v___x_796_);
v___x_798_ = lean_st_ref_take(v___y_780_);
v_mctx_799_ = lean_ctor_get(v___x_798_, 0);
v_zetaDeltaFVarIds_800_ = lean_ctor_get(v___x_798_, 2);
v_postponed_801_ = lean_ctor_get(v___x_798_, 3);
v_diag_802_ = lean_ctor_get(v___x_798_, 4);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v___x_798_, 1);
lean_dec(v_unused_814_);
v___x_804_ = v___x_798_;
v_isShared_805_ = v_isSharedCheck_813_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_diag_802_);
lean_inc(v_postponed_801_);
lean_inc(v_zetaDeltaFVarIds_800_);
lean_inc(v_mctx_799_);
lean_dec(v___x_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_813_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_806_ = lean_box(0);
v___x_807_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_807_);
v___x_809_ = v___x_804_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_mctx_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_zetaDeltaFVarIds_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_postponed_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_diag_802_);
v___x_809_ = v_reuseFailAlloc_812_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_st_ref_put(v___y_780_, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_806_);
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec(v___y_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_824_, lean_object* v_x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_env_832_; lean_object* v_a_834_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_831_ = lean_st_ref_get(v___y_829_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
v___x_844_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_824_, v___y_827_, v___y_829_);
lean_dec_ref(v___x_844_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_828_);
lean_inc(v___y_827_);
lean_inc_ref(v___y_826_);
v___x_845_ = lean_apply_5(v_x_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, lean_box(0));
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_832_, v___y_827_, v___y_829_);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_847_, 0);
lean_dec(v_unused_855_);
v___x_849_ = v___x_847_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_dec(v___x_847_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_a_846_);
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_846_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
lean_object* v_a_856_; 
v_a_856_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_845_, 1);
v_a_834_ = v_a_856_;
goto v___jp_833_;
}
v___jp_833_:
{
lean_object* v___x_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v___x_835_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_832_, v___y_827_, v___y_829_);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_835_, 0);
lean_dec(v_unused_843_);
v___x_837_ = v___x_835_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_dec(v___x_835_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 1);
lean_ctor_set(v___x_837_, 0, v_a_834_);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_834_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_857_, lean_object* v_x_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_857_, v_x_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_865_, lean_object* v_checkType_866_, uint8_t v_safety_867_, uint8_t v_checkMeta_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v_env_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_874_ = lean_box(v_checkMeta_868_);
v___x_875_ = lean_box(v_safety_867_);
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_876_, 0, v___x_874_);
lean_closure_set(v___f_876_, 1, v_checkType_866_);
lean_closure_set(v___f_876_, 2, v___x_875_);
lean_closure_set(v___f_876_, 3, v_value_865_);
v___x_877_ = lean_st_ref_get(v_a_872_);
v_env_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc_ref(v_env_878_);
lean_dec(v___x_877_);
v___x_879_ = l_Lean_Environment_unlockAsync(v_env_878_);
v___x_880_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_879_, v___f_876_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_881_, lean_object* v_checkType_882_, lean_object* v_safety_883_, lean_object* v_checkMeta_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
uint8_t v_safety_boxed_890_; uint8_t v_checkMeta_boxed_891_; lean_object* v_res_892_; 
v_safety_boxed_890_ = lean_unbox(v_safety_883_);
v_checkMeta_boxed_891_ = lean_unbox(v_checkMeta_884_);
v_res_892_ = l_Lean_Meta_evalExprCore___redArg(v_value_881_, v_checkType_882_, v_safety_boxed_890_, v_checkMeta_boxed_891_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_893_, lean_object* v_value_894_, lean_object* v_checkType_895_, uint8_t v_safety_896_, uint8_t v_checkMeta_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_evalExprCore___redArg(v_value_894_, v_checkType_895_, v_safety_896_, v_checkMeta_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_904_, lean_object* v_value_905_, lean_object* v_checkType_906_, lean_object* v_safety_907_, lean_object* v_checkMeta_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
uint8_t v_safety_boxed_914_; uint8_t v_checkMeta_boxed_915_; lean_object* v_res_916_; 
v_safety_boxed_914_ = lean_unbox(v_safety_907_);
v_checkMeta_boxed_915_ = lean_unbox(v_checkMeta_908_);
v_res_916_ = l_Lean_Meta_evalExprCore(v_00_u03b1_904_, v_value_905_, v_checkType_906_, v_safety_boxed_914_, v_checkMeta_boxed_915_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_931_, lean_object* v_constName_932_, uint8_t v_checkMeta_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_932_, v_checkMeta_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_940_, lean_object* v_constName_941_, lean_object* v_checkMeta_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
uint8_t v_checkMeta_boxed_948_; lean_object* v_res_949_; 
v_checkMeta_boxed_948_ = lean_unbox(v_checkMeta_942_);
v_res_949_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_940_, v_constName_941_, v_checkMeta_boxed_948_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_950_, lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_958_, v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_966_, v___y_968_, v___y_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_980_, lean_object* v_env_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_981_, v_x_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_989_, lean_object* v_env_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_989_, v_env_990_, v_x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_1006_, v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1013_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_1017_, lean_object* v_type_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_whnfD(v_type_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1038_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1038_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1038_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Expr_isConstOf(v_a_1025_, v_typeName_1017_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_del_object(v___x_1027_);
v___x_1030_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_1031_ = l_Lean_indentExpr(v_a_1025_);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1032_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_dec(v_a_1025_);
v___x_1034_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1034_);
v___x_1036_ = v___x_1027_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_a_1039_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1024_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1024_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_1047_, lean_object* v_type_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_1047_, v_type_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v_typeName_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1055_, lean_object* v_value_1056_, uint8_t v_safety_1057_, uint8_t v_checkMeta_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; 
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1064_, 0, v_typeName_1055_);
v___x_1065_ = l_Lean_Meta_evalExprCore___redArg(v_value_1056_, v___f_1064_, v_safety_1057_, v_checkMeta_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1066_, lean_object* v_value_1067_, lean_object* v_safety_1068_, lean_object* v_checkMeta_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
uint8_t v_safety_boxed_1075_; uint8_t v_checkMeta_boxed_1076_; lean_object* v_res_1077_; 
v_safety_boxed_1075_ = lean_unbox(v_safety_1068_);
v_checkMeta_boxed_1076_ = lean_unbox(v_checkMeta_1069_);
v_res_1077_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1066_, v_value_1067_, v_safety_boxed_1075_, v_checkMeta_boxed_1076_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1078_, lean_object* v_typeName_1079_, lean_object* v_value_1080_, uint8_t v_safety_1081_, uint8_t v_checkMeta_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1079_, v_value_1080_, v_safety_1081_, v_checkMeta_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1089_, lean_object* v_typeName_1090_, lean_object* v_value_1091_, lean_object* v_safety_1092_, lean_object* v_checkMeta_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
uint8_t v_safety_boxed_1099_; uint8_t v_checkMeta_boxed_1100_; lean_object* v_res_1101_; 
v_safety_boxed_1099_ = lean_unbox(v_safety_1092_);
v_checkMeta_boxed_1100_ = lean_unbox(v_checkMeta_1093_);
v_res_1101_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1089_, v_typeName_1090_, v_value_1091_, v_safety_boxed_1099_, v_checkMeta_boxed_1100_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
return v_res_1101_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1107_, lean_object* v_type_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
lean_inc_ref(v_expectedType_1107_);
lean_inc_ref(v_type_1108_);
v___x_1114_ = l_Lean_Meta_isExprDefEq(v_type_1108_, v_expectedType_1107_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1139_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1139_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1139_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_unbox(v_a_1115_);
lean_dec(v_a_1115_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_del_object(v___x_1117_);
v___x_1120_ = lean_box(0);
v___x_1121_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1122_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1108_, v_expectedType_1107_, v___x_1120_, v___x_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_a_1123_);
v___x_1126_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1125_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1122_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1122_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
lean_dec_ref(v_type_1108_);
lean_dec_ref(v_expectedType_1107_);
v___x_1135_ = lean_box(0);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1135_);
v___x_1137_ = v___x_1117_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_type_1108_);
lean_dec_ref(v_expectedType_1107_);
v_a_1140_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1114_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1114_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1148_, lean_object* v_type_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1148_, v_type_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1156_, lean_object* v_value_1157_, uint8_t v_safety_1158_, uint8_t v_checkMeta_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___f_1165_; lean_object* v___x_1166_; 
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1165_, 0, v_expectedType_1156_);
v___x_1166_ = l_Lean_Meta_evalExprCore___redArg(v_value_1157_, v___f_1165_, v_safety_1158_, v_checkMeta_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1167_, lean_object* v_value_1168_, lean_object* v_safety_1169_, lean_object* v_checkMeta_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
uint8_t v_safety_boxed_1176_; uint8_t v_checkMeta_boxed_1177_; lean_object* v_res_1178_; 
v_safety_boxed_1176_ = lean_unbox(v_safety_1169_);
v_checkMeta_boxed_1177_ = lean_unbox(v_checkMeta_1170_);
v_res_1178_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1167_, v_value_1168_, v_safety_boxed_1176_, v_checkMeta_boxed_1177_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1179_, lean_object* v_expectedType_1180_, lean_object* v_value_1181_, uint8_t v_safety_1182_, uint8_t v_checkMeta_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1180_, v_value_1181_, v_safety_1182_, v_checkMeta_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_expectedType_1191_, lean_object* v_value_1192_, lean_object* v_safety_1193_, lean_object* v_checkMeta_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
uint8_t v_safety_boxed_1200_; uint8_t v_checkMeta_boxed_1201_; lean_object* v_res_1202_; 
v_safety_boxed_1200_ = lean_unbox(v_safety_1193_);
v_checkMeta_boxed_1201_ = lean_unbox(v_checkMeta_1194_);
v_res_1202_ = l_Lean_Meta_evalExpr(v_00_u03b1_1190_, v_expectedType_1191_, v_value_1192_, v_safety_boxed_1200_, v_checkMeta_boxed_1201_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
return v_res_1202_;
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

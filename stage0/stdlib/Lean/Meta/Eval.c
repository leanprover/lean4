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
lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; uint8_t v___y_280_; uint8_t v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; uint8_t v___y_284_; lean_object* v___y_285_; lean_object* v_fileName_286_; lean_object* v_fileMap_287_; lean_object* v_currRecDepth_288_; lean_object* v_ref_289_; lean_object* v_currNamespace_290_; lean_object* v_openDecls_291_; lean_object* v_initHeartbeats_292_; lean_object* v_maxHeartbeats_293_; lean_object* v_quotContext_294_; lean_object* v_currMacroScope_295_; lean_object* v_cancelTk_x3f_296_; uint8_t v_suppressElabErrors_297_; lean_object* v_inheritedTraceOptions_298_; lean_object* v___y_299_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; uint8_t v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; uint8_t v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; uint8_t v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; uint8_t v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; uint8_t v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; uint8_t v___y_350_; lean_object* v___y_372_; uint8_t v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; lean_object* v___y_378_; uint8_t v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; uint8_t v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; uint8_t v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; uint8_t v___y_428_; lean_object* v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; uint8_t v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v_nextMacroScope_666_; lean_object* v_ngen_667_; lean_object* v_auxDeclNGen_668_; lean_object* v_traceState_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v_newDecls_673_; lean_object* v___y_674_; lean_object* v___x_693_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_693_ = lean_st_ref_get(v___y_274_);
lean_inc_ref(v_value_270_);
v___x_707_ = l_Lean_Expr_getUsedConstants(v_value_270_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_array_get_size(v___x_707_);
v___x_710_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
lean_dec_ref(v___x_707_);
lean_dec(v___x_693_);
goto v___jp_694_;
}
else
{
if (v___x_710_ == 0)
{
lean_dec_ref(v___x_707_);
lean_dec(v___x_693_);
goto v___jp_694_;
}
else
{
lean_object* v_env_711_; size_t v___x_712_; size_t v___x_713_; uint8_t v___x_714_; 
v_env_711_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_env_711_);
lean_dec(v___x_693_);
v___x_712_ = ((size_t)0ULL);
v___x_713_ = lean_usize_of_nat(v___x_709_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_711_, v___x_707_, v___x_712_, v___x_713_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v_env_711_);
if (v___x_714_ == 0)
{
goto v___jp_694_;
}
else
{
v___y_620_ = v___y_271_;
v___y_621_ = v___y_272_;
v___y_622_ = v___y_273_;
v___y_623_ = v___y_274_;
goto v___jp_619_;
}
}
}
v___jp_276_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_278_, v___y_277_);
v___x_301_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_301_, 0, v_fileName_286_);
lean_ctor_set(v___x_301_, 1, v_fileMap_287_);
lean_ctor_set(v___x_301_, 2, v___y_278_);
lean_ctor_set(v___x_301_, 3, v_currRecDepth_288_);
lean_ctor_set(v___x_301_, 4, v___x_300_);
lean_ctor_set(v___x_301_, 5, v_ref_289_);
lean_ctor_set(v___x_301_, 6, v_currNamespace_290_);
lean_ctor_set(v___x_301_, 7, v_openDecls_291_);
lean_ctor_set(v___x_301_, 8, v_initHeartbeats_292_);
lean_ctor_set(v___x_301_, 9, v_maxHeartbeats_293_);
lean_ctor_set(v___x_301_, 10, v_quotContext_294_);
lean_ctor_set(v___x_301_, 11, v_currMacroScope_295_);
lean_ctor_set(v___x_301_, 12, v_cancelTk_x3f_296_);
lean_ctor_set(v___x_301_, 13, v_inheritedTraceOptions_298_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*14, v___y_284_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*14 + 1, v_suppressElabErrors_297_);
v___x_302_ = l_Lean_addAndCompile(v___y_282_, v___y_280_, v___y_281_, v___x_301_, v___y_299_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_302_);
v___x_303_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_279_, v_checkMeta_267_, v___y_283_, v___y_285_, v___x_301_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___x_301_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_283_);
return v___x_303_;
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec_ref(v___x_301_);
lean_dec(v___y_299_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_279_);
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
lean_object* v_fileName_324_; lean_object* v_fileMap_325_; lean_object* v_currRecDepth_326_; lean_object* v_ref_327_; lean_object* v_currNamespace_328_; lean_object* v_openDecls_329_; lean_object* v_initHeartbeats_330_; lean_object* v_maxHeartbeats_331_; lean_object* v_quotContext_332_; lean_object* v_currMacroScope_333_; lean_object* v_cancelTk_x3f_334_; uint8_t v_suppressElabErrors_335_; lean_object* v_inheritedTraceOptions_336_; 
v_fileName_324_ = lean_ctor_get(v___y_322_, 0);
lean_inc_ref(v_fileName_324_);
v_fileMap_325_ = lean_ctor_get(v___y_322_, 1);
lean_inc_ref(v_fileMap_325_);
v_currRecDepth_326_ = lean_ctor_get(v___y_322_, 3);
lean_inc(v_currRecDepth_326_);
v_ref_327_ = lean_ctor_get(v___y_322_, 5);
lean_inc(v_ref_327_);
v_currNamespace_328_ = lean_ctor_get(v___y_322_, 6);
lean_inc(v_currNamespace_328_);
v_openDecls_329_ = lean_ctor_get(v___y_322_, 7);
lean_inc(v_openDecls_329_);
v_initHeartbeats_330_ = lean_ctor_get(v___y_322_, 8);
lean_inc(v_initHeartbeats_330_);
v_maxHeartbeats_331_ = lean_ctor_get(v___y_322_, 9);
lean_inc(v_maxHeartbeats_331_);
v_quotContext_332_ = lean_ctor_get(v___y_322_, 10);
lean_inc(v_quotContext_332_);
v_currMacroScope_333_ = lean_ctor_get(v___y_322_, 11);
lean_inc(v_currMacroScope_333_);
v_cancelTk_x3f_334_ = lean_ctor_get(v___y_322_, 12);
lean_inc(v_cancelTk_x3f_334_);
v_suppressElabErrors_335_ = lean_ctor_get_uint8(v___y_322_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_336_ = lean_ctor_get(v___y_322_, 13);
lean_inc_ref(v_inheritedTraceOptions_336_);
lean_dec_ref(v___y_322_);
v___y_277_ = v___y_313_;
v___y_278_ = v___y_314_;
v___y_279_ = v___y_315_;
v___y_280_ = v___y_316_;
v___y_281_ = v___y_317_;
v___y_282_ = v___y_318_;
v___y_283_ = v___y_319_;
v___y_284_ = v___y_320_;
v___y_285_ = v___y_321_;
v_fileName_286_ = v_fileName_324_;
v_fileMap_287_ = v_fileMap_325_;
v_currRecDepth_288_ = v_currRecDepth_326_;
v_ref_289_ = v_ref_327_;
v_currNamespace_290_ = v_currNamespace_328_;
v_openDecls_291_ = v_openDecls_329_;
v_initHeartbeats_292_ = v_initHeartbeats_330_;
v_maxHeartbeats_293_ = v_maxHeartbeats_331_;
v_quotContext_294_ = v_quotContext_332_;
v_currMacroScope_295_ = v_currMacroScope_333_;
v_cancelTk_x3f_296_ = v_cancelTk_x3f_334_;
v_suppressElabErrors_297_ = v_suppressElabErrors_335_;
v_inheritedTraceOptions_298_ = v_inheritedTraceOptions_336_;
v___y_299_ = v___y_323_;
goto v___jp_276_;
}
v___jp_337_:
{
if (v___y_350_ == 0)
{
lean_object* v___x_351_; lean_object* v_env_352_; lean_object* v_nextMacroScope_353_; lean_object* v_ngen_354_; lean_object* v_auxDeclNGen_355_; lean_object* v_traceState_356_; lean_object* v_messages_357_; lean_object* v_infoState_358_; lean_object* v_snapshotTasks_359_; lean_object* v_newDecls_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_369_; 
v___x_351_ = lean_st_ref_take(v___y_338_);
v_env_352_ = lean_ctor_get(v___x_351_, 0);
v_nextMacroScope_353_ = lean_ctor_get(v___x_351_, 1);
v_ngen_354_ = lean_ctor_get(v___x_351_, 2);
v_auxDeclNGen_355_ = lean_ctor_get(v___x_351_, 3);
v_traceState_356_ = lean_ctor_get(v___x_351_, 4);
v_messages_357_ = lean_ctor_get(v___x_351_, 6);
v_infoState_358_ = lean_ctor_get(v___x_351_, 7);
v_snapshotTasks_359_ = lean_ctor_get(v___x_351_, 8);
v_newDecls_360_ = lean_ctor_get(v___x_351_, 9);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_351_, 5);
lean_dec(v_unused_370_);
v___x_362_ = v___x_351_;
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_newDecls_360_);
lean_inc(v_snapshotTasks_359_);
lean_inc(v_infoState_358_);
lean_inc(v_messages_357_);
lean_inc(v_traceState_356_);
lean_inc(v_auxDeclNGen_355_);
lean_inc(v_ngen_354_);
lean_inc(v_nextMacroScope_353_);
lean_inc(v_env_352_);
lean_dec(v___x_351_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = l_Lean_Kernel_enableDiag(v_env_352_, v___y_344_);
lean_inc_ref(v___y_345_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 5, v___y_345_);
lean_ctor_set(v___x_362_, 0, v___x_364_);
v___x_366_ = v___x_362_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_nextMacroScope_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_ngen_354_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_auxDeclNGen_355_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_traceState_356_);
lean_ctor_set(v_reuseFailAlloc_368_, 5, v___y_345_);
lean_ctor_set(v_reuseFailAlloc_368_, 6, v_messages_357_);
lean_ctor_set(v_reuseFailAlloc_368_, 7, v_infoState_358_);
lean_ctor_set(v_reuseFailAlloc_368_, 8, v_snapshotTasks_359_);
lean_ctor_set(v_reuseFailAlloc_368_, 9, v_newDecls_360_);
v___x_366_ = v_reuseFailAlloc_368_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; 
v___x_367_ = lean_st_ref_set(v___y_338_, v___x_366_);
v___y_313_ = v___y_339_;
v___y_314_ = v___y_346_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_347_;
v___y_318_ = v___y_348_;
v___y_319_ = v___y_343_;
v___y_320_ = v___y_344_;
v___y_321_ = v___y_349_;
v___y_322_ = v___y_342_;
v___y_323_ = v___y_338_;
goto v___jp_312_;
}
}
}
else
{
v___y_313_ = v___y_339_;
v___y_314_ = v___y_346_;
v___y_315_ = v___y_340_;
v___y_316_ = v___y_341_;
v___y_317_ = v___y_347_;
v___y_318_ = v___y_348_;
v___y_319_ = v___y_343_;
v___y_320_ = v___y_344_;
v___y_321_ = v___y_349_;
v___y_322_ = v___y_342_;
v___y_323_ = v___y_338_;
goto v___jp_312_;
}
}
v___jp_371_:
{
lean_object* v___x_385_; lean_object* v_fileName_386_; lean_object* v_fileMap_387_; lean_object* v_currRecDepth_388_; lean_object* v_ref_389_; lean_object* v_currNamespace_390_; lean_object* v_openDecls_391_; lean_object* v_initHeartbeats_392_; lean_object* v_maxHeartbeats_393_; lean_object* v_quotContext_394_; lean_object* v_currMacroScope_395_; lean_object* v_cancelTk_x3f_396_; uint8_t v_suppressElabErrors_397_; lean_object* v_inheritedTraceOptions_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_411_; 
v___x_385_ = lean_st_ref_get(v___y_384_);
v_fileName_386_ = lean_ctor_get(v___y_383_, 0);
v_fileMap_387_ = lean_ctor_get(v___y_383_, 1);
v_currRecDepth_388_ = lean_ctor_get(v___y_383_, 3);
v_ref_389_ = lean_ctor_get(v___y_383_, 5);
v_currNamespace_390_ = lean_ctor_get(v___y_383_, 6);
v_openDecls_391_ = lean_ctor_get(v___y_383_, 7);
v_initHeartbeats_392_ = lean_ctor_get(v___y_383_, 8);
v_maxHeartbeats_393_ = lean_ctor_get(v___y_383_, 9);
v_quotContext_394_ = lean_ctor_get(v___y_383_, 10);
v_currMacroScope_395_ = lean_ctor_get(v___y_383_, 11);
v_cancelTk_x3f_396_ = lean_ctor_get(v___y_383_, 12);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v___y_383_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_398_ = lean_ctor_get(v___y_383_, 13);
v_isSharedCheck_411_ = !lean_is_exclusive(v___y_383_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_412_ = lean_ctor_get(v___y_383_, 4);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v___y_383_, 2);
lean_dec(v_unused_413_);
v___x_400_ = v___y_383_;
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_inheritedTraceOptions_398_);
lean_inc(v_cancelTk_x3f_396_);
lean_inc(v_currMacroScope_395_);
lean_inc(v_quotContext_394_);
lean_inc(v_maxHeartbeats_393_);
lean_inc(v_initHeartbeats_392_);
lean_inc(v_openDecls_391_);
lean_inc(v_currNamespace_390_);
lean_inc(v_ref_389_);
lean_inc(v_currRecDepth_388_);
lean_inc(v_fileMap_387_);
lean_inc(v_fileName_386_);
lean_dec(v___y_383_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_env_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v_env_402_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_385_);
v___x_403_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_372_, v___y_375_);
lean_inc_ref(v_inheritedTraceOptions_398_);
lean_inc(v_cancelTk_x3f_396_);
lean_inc(v_currMacroScope_395_);
lean_inc(v_quotContext_394_);
lean_inc(v_maxHeartbeats_393_);
lean_inc(v_initHeartbeats_392_);
lean_inc(v_openDecls_391_);
lean_inc(v_currNamespace_390_);
lean_inc(v_ref_389_);
lean_inc(v_currRecDepth_388_);
lean_inc_ref(v___y_372_);
lean_inc_ref(v_fileMap_387_);
lean_inc_ref(v_fileName_386_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 4, v___x_403_);
lean_ctor_set(v___x_400_, 2, v___y_372_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_fileName_386_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_fileMap_387_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v___y_372_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_currRecDepth_388_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v_ref_389_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v_currNamespace_390_);
lean_ctor_set(v_reuseFailAlloc_410_, 7, v_openDecls_391_);
lean_ctor_set(v_reuseFailAlloc_410_, 8, v_initHeartbeats_392_);
lean_ctor_set(v_reuseFailAlloc_410_, 9, v_maxHeartbeats_393_);
lean_ctor_set(v_reuseFailAlloc_410_, 10, v_quotContext_394_);
lean_ctor_set(v_reuseFailAlloc_410_, 11, v_currMacroScope_395_);
lean_ctor_set(v_reuseFailAlloc_410_, 12, v_cancelTk_x3f_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 13, v_inheritedTraceOptions_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*14 + 1, v_suppressElabErrors_397_);
v___x_405_ = v_reuseFailAlloc_410_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; uint8_t v___x_409_; 
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*14, v___y_373_);
v___x_406_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_407_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_372_, v___x_406_, v___y_377_);
v___x_408_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_407_, v___y_381_);
v___x_409_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_402_);
lean_dec_ref(v_env_402_);
if (v___x_409_ == 0)
{
if (v___x_408_ == 0)
{
lean_dec_ref(v___x_405_);
v___y_277_ = v___y_375_;
v___y_278_ = v___x_407_;
v___y_279_ = v___y_376_;
v___y_280_ = v___y_377_;
v___y_281_ = v___y_379_;
v___y_282_ = v___y_378_;
v___y_283_ = v___y_380_;
v___y_284_ = v___x_408_;
v___y_285_ = v___y_382_;
v_fileName_286_ = v_fileName_386_;
v_fileMap_287_ = v_fileMap_387_;
v_currRecDepth_288_ = v_currRecDepth_388_;
v_ref_289_ = v_ref_389_;
v_currNamespace_290_ = v_currNamespace_390_;
v_openDecls_291_ = v_openDecls_391_;
v_initHeartbeats_292_ = v_initHeartbeats_392_;
v_maxHeartbeats_293_ = v_maxHeartbeats_393_;
v_quotContext_294_ = v_quotContext_394_;
v_currMacroScope_295_ = v_currMacroScope_395_;
v_cancelTk_x3f_296_ = v_cancelTk_x3f_396_;
v_suppressElabErrors_297_ = v_suppressElabErrors_397_;
v_inheritedTraceOptions_298_ = v_inheritedTraceOptions_398_;
v___y_299_ = v___y_384_;
goto v___jp_276_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_398_);
lean_dec(v_cancelTk_x3f_396_);
lean_dec(v_currMacroScope_395_);
lean_dec(v_quotContext_394_);
lean_dec(v_maxHeartbeats_393_);
lean_dec(v_initHeartbeats_392_);
lean_dec(v_openDecls_391_);
lean_dec(v_currNamespace_390_);
lean_dec(v_ref_389_);
lean_dec(v_currRecDepth_388_);
lean_dec_ref(v_fileMap_387_);
lean_dec_ref(v_fileName_386_);
v___y_338_ = v___y_384_;
v___y_339_ = v___y_375_;
v___y_340_ = v___y_376_;
v___y_341_ = v___y_377_;
v___y_342_ = v___x_405_;
v___y_343_ = v___y_380_;
v___y_344_ = v___x_408_;
v___y_345_ = v___y_374_;
v___y_346_ = v___x_407_;
v___y_347_ = v___y_379_;
v___y_348_ = v___y_378_;
v___y_349_ = v___y_382_;
v___y_350_ = v___x_409_;
goto v___jp_337_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_398_);
lean_dec(v_cancelTk_x3f_396_);
lean_dec(v_currMacroScope_395_);
lean_dec(v_quotContext_394_);
lean_dec(v_maxHeartbeats_393_);
lean_dec(v_initHeartbeats_392_);
lean_dec(v_openDecls_391_);
lean_dec(v_currNamespace_390_);
lean_dec(v_ref_389_);
lean_dec(v_currRecDepth_388_);
lean_dec_ref(v_fileMap_387_);
lean_dec_ref(v_fileName_386_);
v___y_338_ = v___y_384_;
v___y_339_ = v___y_375_;
v___y_340_ = v___y_376_;
v___y_341_ = v___y_377_;
v___y_342_ = v___x_405_;
v___y_343_ = v___y_380_;
v___y_344_ = v___x_408_;
v___y_345_ = v___y_374_;
v___y_346_ = v___x_407_;
v___y_347_ = v___y_379_;
v___y_348_ = v___y_378_;
v___y_349_ = v___y_382_;
v___y_350_ = v___x_408_;
goto v___jp_337_;
}
}
}
}
v___jp_414_:
{
if (v___y_428_ == 0)
{
lean_object* v___x_429_; lean_object* v_env_430_; lean_object* v_nextMacroScope_431_; lean_object* v_ngen_432_; lean_object* v_auxDeclNGen_433_; lean_object* v_traceState_434_; lean_object* v_messages_435_; lean_object* v_infoState_436_; lean_object* v_snapshotTasks_437_; lean_object* v_newDecls_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_447_; 
v___x_429_ = lean_st_ref_take(v___y_422_);
v_env_430_ = lean_ctor_get(v___x_429_, 0);
v_nextMacroScope_431_ = lean_ctor_get(v___x_429_, 1);
v_ngen_432_ = lean_ctor_get(v___x_429_, 2);
v_auxDeclNGen_433_ = lean_ctor_get(v___x_429_, 3);
v_traceState_434_ = lean_ctor_get(v___x_429_, 4);
v_messages_435_ = lean_ctor_get(v___x_429_, 6);
v_infoState_436_ = lean_ctor_get(v___x_429_, 7);
v_snapshotTasks_437_ = lean_ctor_get(v___x_429_, 8);
v_newDecls_438_ = lean_ctor_get(v___x_429_, 9);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_429_, 5);
lean_dec(v_unused_448_);
v___x_440_ = v___x_429_;
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_newDecls_438_);
lean_inc(v_snapshotTasks_437_);
lean_inc(v_infoState_436_);
lean_inc(v_messages_435_);
lean_inc(v_traceState_434_);
lean_inc(v_auxDeclNGen_433_);
lean_inc(v_ngen_432_);
lean_inc(v_nextMacroScope_431_);
lean_inc(v_env_430_);
lean_dec(v___x_429_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = l_Lean_Kernel_enableDiag(v_env_430_, v___y_416_);
lean_inc_ref(v___y_421_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 5, v___y_421_);
lean_ctor_set(v___x_440_, 0, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_nextMacroScope_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_ngen_432_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_auxDeclNGen_433_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_traceState_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 5, v___y_421_);
lean_ctor_set(v_reuseFailAlloc_446_, 6, v_messages_435_);
lean_ctor_set(v_reuseFailAlloc_446_, 7, v_infoState_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 8, v_snapshotTasks_437_);
lean_ctor_set(v_reuseFailAlloc_446_, 9, v_newDecls_438_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_st_ref_set(v___y_422_, v___x_444_);
v___y_372_ = v___y_415_;
v___y_373_ = v___y_416_;
v___y_374_ = v___y_421_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_418_;
v___y_377_ = v___y_419_;
v___y_378_ = v___y_423_;
v___y_379_ = v___y_424_;
v___y_380_ = v___y_420_;
v___y_381_ = v___y_426_;
v___y_382_ = v___y_427_;
v___y_383_ = v___y_425_;
v___y_384_ = v___y_422_;
goto v___jp_371_;
}
}
}
else
{
v___y_372_ = v___y_415_;
v___y_373_ = v___y_416_;
v___y_374_ = v___y_421_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_418_;
v___y_377_ = v___y_419_;
v___y_378_ = v___y_423_;
v___y_379_ = v___y_424_;
v___y_380_ = v___y_420_;
v___y_381_ = v___y_426_;
v___y_382_ = v___y_427_;
v___y_383_ = v___y_425_;
v___y_384_ = v___y_422_;
goto v___jp_371_;
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
v___x_481_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_454_, v___x_480_);
lean_inc_ref(v___y_454_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 4, v___x_481_);
lean_ctor_set(v___x_477_, 2, v___y_454_);
v___x_483_ = v___x_477_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_fileName_463_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_fileMap_464_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v___y_454_);
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
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*14, v___y_453_);
v___x_484_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_485_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_454_, v___x_484_, v___y_456_);
v___x_486_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_485_, v___y_458_);
v___x_487_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_479_);
lean_dec_ref(v_env_479_);
if (v___x_487_ == 0)
{
if (v___x_486_ == 0)
{
v___y_372_ = v___x_485_;
v___y_373_ = v___x_486_;
v___y_374_ = v___y_450_;
v___y_375_ = v___x_480_;
v___y_376_ = v___y_451_;
v___y_377_ = v___y_452_;
v___y_378_ = v___y_455_;
v___y_379_ = v___y_456_;
v___y_380_ = v___y_457_;
v___y_381_ = v___y_458_;
v___y_382_ = v___y_459_;
v___y_383_ = v___x_483_;
v___y_384_ = v___y_461_;
goto v___jp_371_;
}
else
{
v___y_415_ = v___x_485_;
v___y_416_ = v___x_486_;
v___y_417_ = v___x_480_;
v___y_418_ = v___y_451_;
v___y_419_ = v___y_452_;
v___y_420_ = v___y_457_;
v___y_421_ = v___y_450_;
v___y_422_ = v___y_461_;
v___y_423_ = v___y_455_;
v___y_424_ = v___y_456_;
v___y_425_ = v___x_483_;
v___y_426_ = v___y_458_;
v___y_427_ = v___y_459_;
v___y_428_ = v___x_487_;
goto v___jp_414_;
}
}
else
{
v___y_415_ = v___x_485_;
v___y_416_ = v___x_486_;
v___y_417_ = v___x_480_;
v___y_418_ = v___y_451_;
v___y_419_ = v___y_452_;
v___y_420_ = v___y_457_;
v___y_421_ = v___y_450_;
v___y_422_ = v___y_461_;
v___y_423_ = v___y_455_;
v___y_424_ = v___y_456_;
v___y_425_ = v___x_483_;
v___y_426_ = v___y_458_;
v___y_427_ = v___y_459_;
v___y_428_ = v___x_486_;
goto v___jp_414_;
}
}
}
}
v___jp_492_:
{
if (v___y_505_ == 0)
{
lean_object* v___x_506_; lean_object* v_env_507_; lean_object* v_nextMacroScope_508_; lean_object* v_ngen_509_; lean_object* v_auxDeclNGen_510_; lean_object* v_traceState_511_; lean_object* v_messages_512_; lean_object* v_infoState_513_; lean_object* v_snapshotTasks_514_; lean_object* v_newDecls_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
v___x_506_ = lean_st_ref_take(v___y_498_);
v_env_507_ = lean_ctor_get(v___x_506_, 0);
v_nextMacroScope_508_ = lean_ctor_get(v___x_506_, 1);
v_ngen_509_ = lean_ctor_get(v___x_506_, 2);
v_auxDeclNGen_510_ = lean_ctor_get(v___x_506_, 3);
v_traceState_511_ = lean_ctor_get(v___x_506_, 4);
v_messages_512_ = lean_ctor_get(v___x_506_, 6);
v_infoState_513_ = lean_ctor_get(v___x_506_, 7);
v_snapshotTasks_514_ = lean_ctor_get(v___x_506_, 8);
v_newDecls_515_ = lean_ctor_get(v___x_506_, 9);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_506_, 5);
lean_dec(v_unused_525_);
v___x_517_ = v___x_506_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_newDecls_515_);
lean_inc(v_snapshotTasks_514_);
lean_inc(v_infoState_513_);
lean_inc(v_messages_512_);
lean_inc(v_traceState_511_);
lean_inc(v_auxDeclNGen_510_);
lean_inc(v_ngen_509_);
lean_inc(v_nextMacroScope_508_);
lean_inc(v_env_507_);
lean_dec(v___x_506_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = l_Lean_Kernel_enableDiag(v_env_507_, v___y_500_);
lean_inc_ref(v___y_499_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 5, v___y_499_);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_nextMacroScope_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_ngen_509_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_auxDeclNGen_510_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_traceState_511_);
lean_ctor_set(v_reuseFailAlloc_523_, 5, v___y_499_);
lean_ctor_set(v_reuseFailAlloc_523_, 6, v_messages_512_);
lean_ctor_set(v_reuseFailAlloc_523_, 7, v_infoState_513_);
lean_ctor_set(v_reuseFailAlloc_523_, 8, v_snapshotTasks_514_);
lean_ctor_set(v_reuseFailAlloc_523_, 9, v_newDecls_515_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_st_ref_set(v___y_498_, v___x_521_);
v___y_450_ = v___y_499_;
v___y_451_ = v___y_494_;
v___y_452_ = v___y_495_;
v___y_453_ = v___y_500_;
v___y_454_ = v___y_496_;
v___y_455_ = v___y_501_;
v___y_456_ = v___y_502_;
v___y_457_ = v___y_497_;
v___y_458_ = v___y_503_;
v___y_459_ = v___y_504_;
v___y_460_ = v___y_493_;
v___y_461_ = v___y_498_;
goto v___jp_449_;
}
}
}
else
{
v___y_450_ = v___y_499_;
v___y_451_ = v___y_494_;
v___y_452_ = v___y_495_;
v___y_453_ = v___y_500_;
v___y_454_ = v___y_496_;
v___y_455_ = v___y_501_;
v___y_456_ = v___y_502_;
v___y_457_ = v___y_497_;
v___y_458_ = v___y_503_;
v___y_459_ = v___y_504_;
v___y_460_ = v___y_493_;
v___y_461_ = v___y_498_;
goto v___jp_449_;
}
}
v___jp_526_:
{
lean_object* v___x_535_; 
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
lean_inc_ref(v___y_529_);
v___x_535_ = lean_infer_type(v___y_529_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc_n(v_a_536_, 2);
lean_dec_ref(v___x_535_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
v___x_537_ = lean_apply_6(v_checkType_268_, v_a_536_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, lean_box(0));
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; lean_object* v_env_539_; lean_object* v_nextMacroScope_540_; lean_object* v_ngen_541_; lean_object* v_auxDeclNGen_542_; lean_object* v_traceState_543_; lean_object* v_messages_544_; lean_object* v_infoState_545_; lean_object* v_snapshotTasks_546_; lean_object* v_newDecls_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v___x_537_);
v___x_538_ = lean_st_ref_take(v___y_534_);
v_env_539_ = lean_ctor_get(v___x_538_, 0);
v_nextMacroScope_540_ = lean_ctor_get(v___x_538_, 1);
v_ngen_541_ = lean_ctor_get(v___x_538_, 2);
v_auxDeclNGen_542_ = lean_ctor_get(v___x_538_, 3);
v_traceState_543_ = lean_ctor_get(v___x_538_, 4);
v_messages_544_ = lean_ctor_get(v___x_538_, 6);
v_infoState_545_ = lean_ctor_get(v___x_538_, 7);
v_snapshotTasks_546_ = lean_ctor_get(v___x_538_, 8);
v_newDecls_547_ = lean_ctor_get(v___x_538_, 9);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_538_, 5);
lean_dec(v_unused_602_);
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_601_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_newDecls_547_);
lean_inc(v_snapshotTasks_546_);
lean_inc(v_infoState_545_);
lean_inc(v_messages_544_);
lean_inc(v_traceState_543_);
lean_inc(v_auxDeclNGen_542_);
lean_inc(v_ngen_541_);
lean_inc(v_nextMacroScope_540_);
lean_inc(v_env_539_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_601_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_551_ = lean_array_to_list(v___y_530_);
lean_inc_n(v___y_527_, 3);
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v___y_527_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
lean_ctor_set(v___x_552_, 2, v_a_536_);
lean_inc(v___y_528_);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v___y_527_);
lean_ctor_set(v___x_553_, 1, v___y_528_);
v___x_554_ = l_Lean_markMeta(v_env_539_, v___y_527_);
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
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_nextMacroScope_540_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_ngen_541_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_auxDeclNGen_542_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_traceState_543_);
lean_ctor_set(v_reuseFailAlloc_600_, 5, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_600_, 6, v_messages_544_);
lean_ctor_set(v_reuseFailAlloc_600_, 7, v_infoState_545_);
lean_ctor_set(v_reuseFailAlloc_600_, 8, v_snapshotTasks_546_);
lean_ctor_set(v_reuseFailAlloc_600_, 9, v_newDecls_547_);
v___x_557_ = v_reuseFailAlloc_600_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_mctx_560_; lean_object* v_zetaDeltaFVarIds_561_; lean_object* v_postponed_562_; lean_object* v_diag_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_598_; 
v___x_558_ = lean_st_ref_set(v___y_534_, v___x_557_);
v___x_559_ = lean_st_ref_take(v___y_532_);
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
v___x_570_ = lean_st_ref_set(v___y_532_, v___x_569_);
v___x_571_ = lean_st_ref_get(v___y_534_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
v_checked_573_ = lean_ctor_get(v_env_572_, 2);
lean_inc_ref(v_checked_573_);
lean_dec_ref(v_env_572_);
v___x_574_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_575_ = l_Lean_traceBlock___redArg(v___x_574_, v_checked_573_, v___y_533_, v___y_534_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; lean_object* v_options_577_; lean_object* v_env_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; uint8_t v___x_588_; 
lean_dec_ref(v___x_575_);
v___x_576_ = lean_st_ref_get(v___y_534_);
v_options_577_ = lean_ctor_get(v___y_533_, 2);
v_env_578_ = lean_ctor_get(v___x_576_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_580_, 0, v___x_552_);
lean_ctor_set(v___x_580_, 1, v___y_529_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
lean_ctor_set(v___x_580_, 3, v___x_553_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*4, v_safety_269_);
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
if (v___x_588_ == 0)
{
if (v___x_587_ == 0)
{
v___y_450_ = v___x_555_;
v___y_451_ = v___y_527_;
v___y_452_ = v___x_582_;
v___y_453_ = v___x_587_;
v___y_454_ = v___x_585_;
v___y_455_ = v___x_581_;
v___y_456_ = v___x_583_;
v___y_457_ = v___y_531_;
v___y_458_ = v___x_586_;
v___y_459_ = v___y_532_;
v___y_460_ = v___y_533_;
v___y_461_ = v___y_534_;
goto v___jp_449_;
}
else
{
v___y_493_ = v___y_533_;
v___y_494_ = v___y_527_;
v___y_495_ = v___x_582_;
v___y_496_ = v___x_585_;
v___y_497_ = v___y_531_;
v___y_498_ = v___y_534_;
v___y_499_ = v___x_555_;
v___y_500_ = v___x_587_;
v___y_501_ = v___x_581_;
v___y_502_ = v___x_583_;
v___y_503_ = v___x_586_;
v___y_504_ = v___y_532_;
v___y_505_ = v___x_588_;
goto v___jp_492_;
}
}
else
{
v___y_493_ = v___y_533_;
v___y_494_ = v___y_527_;
v___y_495_ = v___x_582_;
v___y_496_ = v___x_585_;
v___y_497_ = v___y_531_;
v___y_498_ = v___y_534_;
v___y_499_ = v___x_555_;
v___y_500_ = v___x_587_;
v___y_501_ = v___x_581_;
v___y_502_ = v___x_583_;
v___y_503_ = v___x_586_;
v___y_504_ = v___y_532_;
v___y_505_ = v___x_587_;
goto v___jp_492_;
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v___x_553_);
lean_dec_ref(v___x_552_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_527_);
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
lean_dec(v_a_536_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_527_);
v_a_603_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_537_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_537_);
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
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_527_);
lean_dec_ref(v_checkType_268_);
v_a_611_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_535_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_535_);
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
lean_dec_ref(v___x_626_);
v___x_628_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_270_, v___y_621_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v_env_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_params_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_n(v_a_629_, 2);
lean_dec_ref(v___x_628_);
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
v___y_527_ = v___x_634_;
v___y_528_ = v___x_635_;
v___y_529_ = v_a_629_;
v___y_530_ = v_params_633_;
v___y_531_ = v___y_620_;
v___y_532_ = v___y_621_;
v___y_533_ = v___y_622_;
v___y_534_ = v___y_623_;
goto v___jp_526_;
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
lean_dec_ref(v___x_640_);
v___y_527_ = v___x_634_;
v___y_528_ = v___x_635_;
v___y_529_ = v_a_629_;
v___y_530_ = v_params_633_;
v___y_531_ = v___y_620_;
v___y_532_ = v___y_621_;
v___y_533_ = v___y_622_;
v___y_534_ = v___y_623_;
goto v___jp_526_;
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
lean_dec_ref(v_checkType_268_);
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
lean_dec_ref(v_checkType_268_);
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
lean_dec_ref(v_value_270_);
lean_dec_ref(v_checkType_268_);
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
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_mctx_679_; lean_object* v_zetaDeltaFVarIds_680_; lean_object* v_postponed_681_; lean_object* v_diag_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_691_; 
v___x_675_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_676_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_676_, 0, v___y_674_);
lean_ctor_set(v___x_676_, 1, v_nextMacroScope_666_);
lean_ctor_set(v___x_676_, 2, v_ngen_667_);
lean_ctor_set(v___x_676_, 3, v_auxDeclNGen_668_);
lean_ctor_set(v___x_676_, 4, v_traceState_669_);
lean_ctor_set(v___x_676_, 5, v___x_675_);
lean_ctor_set(v___x_676_, 6, v_messages_670_);
lean_ctor_set(v___x_676_, 7, v_infoState_671_);
lean_ctor_set(v___x_676_, 8, v_snapshotTasks_672_);
lean_ctor_set(v___x_676_, 9, v_newDecls_673_);
v___x_677_ = lean_st_ref_set(v___y_274_, v___x_676_);
v___x_678_ = lean_st_ref_take(v___y_272_);
v_mctx_679_ = lean_ctor_get(v___x_678_, 0);
v_zetaDeltaFVarIds_680_ = lean_ctor_get(v___x_678_, 2);
v_postponed_681_ = lean_ctor_get(v___x_678_, 3);
v_diag_682_ = lean_ctor_get(v___x_678_, 4);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_678_, 1);
lean_dec(v_unused_692_);
v___x_684_ = v___x_678_;
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_diag_682_);
lean_inc(v_postponed_681_);
lean_inc(v_zetaDeltaFVarIds_680_);
lean_inc(v_mctx_679_);
lean_dec(v___x_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_686_);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_mctx_679_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_zetaDeltaFVarIds_680_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_postponed_681_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_diag_682_);
v___x_688_ = v_reuseFailAlloc_690_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; 
v___x_689_ = lean_st_ref_set(v___y_272_, v___x_688_);
v___y_620_ = v___y_271_;
v___y_621_ = v___y_272_;
v___y_622_ = v___y_273_;
v___y_623_ = v___y_274_;
goto v___jp_619_;
}
}
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v_env_696_; lean_object* v_nextMacroScope_697_; lean_object* v_ngen_698_; lean_object* v_auxDeclNGen_699_; lean_object* v_traceState_700_; lean_object* v_messages_701_; lean_object* v_infoState_702_; lean_object* v_snapshotTasks_703_; lean_object* v_newDecls_704_; lean_object* v___x_705_; 
v___x_695_ = lean_st_ref_take(v___y_274_);
v_env_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref_n(v_env_696_, 2);
v_nextMacroScope_697_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_nextMacroScope_697_);
v_ngen_698_ = lean_ctor_get(v___x_695_, 2);
lean_inc_ref(v_ngen_698_);
v_auxDeclNGen_699_ = lean_ctor_get(v___x_695_, 3);
lean_inc_ref(v_auxDeclNGen_699_);
v_traceState_700_ = lean_ctor_get(v___x_695_, 4);
lean_inc_ref(v_traceState_700_);
v_messages_701_ = lean_ctor_get(v___x_695_, 6);
lean_inc_ref(v_messages_701_);
v_infoState_702_ = lean_ctor_get(v___x_695_, 7);
lean_inc_ref(v_infoState_702_);
v_snapshotTasks_703_ = lean_ctor_get(v___x_695_, 8);
lean_inc_ref(v_snapshotTasks_703_);
v_newDecls_704_ = lean_ctor_get(v___x_695_, 9);
lean_inc_ref(v_newDecls_704_);
lean_dec(v___x_695_);
v___x_705_ = l_Lean_Environment_importEnv_x3f(v_env_696_);
if (lean_obj_tag(v___x_705_) == 0)
{
v_nextMacroScope_666_ = v_nextMacroScope_697_;
v_ngen_667_ = v_ngen_698_;
v_auxDeclNGen_668_ = v_auxDeclNGen_699_;
v_traceState_669_ = v_traceState_700_;
v_messages_670_ = v_messages_701_;
v_infoState_671_ = v_infoState_702_;
v_snapshotTasks_672_ = v_snapshotTasks_703_;
v_newDecls_673_ = v_newDecls_704_;
v___y_674_ = v_env_696_;
goto v___jp_665_;
}
else
{
lean_object* v_val_706_; 
lean_dec_ref(v_env_696_);
v_val_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_val_706_);
lean_dec_ref(v___x_705_);
v_nextMacroScope_666_ = v_nextMacroScope_697_;
v_ngen_667_ = v_ngen_698_;
v_auxDeclNGen_668_ = v_auxDeclNGen_699_;
v_traceState_669_ = v_traceState_700_;
v_messages_670_ = v_messages_701_;
v_infoState_671_ = v_infoState_702_;
v_snapshotTasks_672_ = v_snapshotTasks_703_;
v_newDecls_673_ = v_newDecls_704_;
v___y_674_ = v_val_706_;
goto v___jp_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_715_, lean_object* v_checkType_716_, lean_object* v_safety_717_, lean_object* v_value_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v_checkMeta_boxed_724_; uint8_t v_safety_boxed_725_; lean_object* v_res_726_; 
v_checkMeta_boxed_724_ = lean_unbox(v_checkMeta_715_);
v_safety_boxed_725_ = lean_unbox(v_safety_717_);
v_res_726_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_724_, v_checkType_716_, v_safety_boxed_725_, v_value_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v_nextMacroScope_732_; lean_object* v_ngen_733_; lean_object* v_auxDeclNGen_734_; lean_object* v_traceState_735_; lean_object* v_messages_736_; lean_object* v_infoState_737_; lean_object* v_snapshotTasks_738_; lean_object* v_newDecls_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_765_; 
v___x_731_ = lean_st_ref_take(v___y_729_);
v_nextMacroScope_732_ = lean_ctor_get(v___x_731_, 1);
v_ngen_733_ = lean_ctor_get(v___x_731_, 2);
v_auxDeclNGen_734_ = lean_ctor_get(v___x_731_, 3);
v_traceState_735_ = lean_ctor_get(v___x_731_, 4);
v_messages_736_ = lean_ctor_get(v___x_731_, 6);
v_infoState_737_ = lean_ctor_get(v___x_731_, 7);
v_snapshotTasks_738_ = lean_ctor_get(v___x_731_, 8);
v_newDecls_739_ = lean_ctor_get(v___x_731_, 9);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; lean_object* v_unused_767_; 
v_unused_766_ = lean_ctor_get(v___x_731_, 5);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v___x_731_, 0);
lean_dec(v_unused_767_);
v___x_741_ = v___x_731_;
v_isShared_742_ = v_isSharedCheck_765_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_newDecls_739_);
lean_inc(v_snapshotTasks_738_);
lean_inc(v_infoState_737_);
lean_inc(v_messages_736_);
lean_inc(v_traceState_735_);
lean_inc(v_auxDeclNGen_734_);
lean_inc(v_ngen_733_);
lean_inc(v_nextMacroScope_732_);
lean_dec(v___x_731_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_765_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 5, v___x_743_);
lean_ctor_set(v___x_741_, 0, v_env_727_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_env_727_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_nextMacroScope_732_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_ngen_733_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_auxDeclNGen_734_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_traceState_735_);
lean_ctor_set(v_reuseFailAlloc_764_, 5, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_764_, 6, v_messages_736_);
lean_ctor_set(v_reuseFailAlloc_764_, 7, v_infoState_737_);
lean_ctor_set(v_reuseFailAlloc_764_, 8, v_snapshotTasks_738_);
lean_ctor_set(v_reuseFailAlloc_764_, 9, v_newDecls_739_);
v___x_745_ = v_reuseFailAlloc_764_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_mctx_748_; lean_object* v_zetaDeltaFVarIds_749_; lean_object* v_postponed_750_; lean_object* v_diag_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_762_; 
v___x_746_ = lean_st_ref_set(v___y_729_, v___x_745_);
v___x_747_ = lean_st_ref_take(v___y_728_);
v_mctx_748_ = lean_ctor_get(v___x_747_, 0);
v_zetaDeltaFVarIds_749_ = lean_ctor_get(v___x_747_, 2);
v_postponed_750_ = lean_ctor_get(v___x_747_, 3);
v_diag_751_ = lean_ctor_get(v___x_747_, 4);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_747_, 1);
lean_dec(v_unused_763_);
v___x_753_ = v___x_747_;
v_isShared_754_ = v_isSharedCheck_762_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_diag_751_);
lean_inc(v_postponed_750_);
lean_inc(v_zetaDeltaFVarIds_749_);
lean_inc(v_mctx_748_);
lean_dec(v___x_747_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_762_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_mctx_748_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_zetaDeltaFVarIds_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_postponed_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_diag_751_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = lean_st_ref_set(v___y_728_, v___x_757_);
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec(v___y_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_env_781_; lean_object* v_a_783_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_780_ = lean_st_ref_get(v___y_778_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_793_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_773_, v___y_776_, v___y_778_);
lean_dec_ref(v___x_793_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
v___x_794_ = lean_apply_5(v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, lean_box(0));
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_781_, v___y_776_, v___y_778_);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_796_, 0);
lean_dec(v_unused_804_);
v___x_798_ = v___x_796_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_dec(v___x_796_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_a_795_);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_795_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v___x_794_);
v_a_783_ = v_a_805_;
goto v___jp_782_;
}
v___jp_782_:
{
lean_object* v___x_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v___x_784_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_781_, v___y_776_, v___y_778_);
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
lean_ctor_set_tag(v___x_786_, 1);
lean_ctor_set(v___x_786_, 0, v_a_783_);
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_806_, lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_806_, v_x_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_814_, lean_object* v_checkType_815_, uint8_t v_safety_816_, uint8_t v_checkMeta_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_env_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_823_ = lean_st_ref_get(v_a_821_);
v_env_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_ref(v_env_824_);
lean_dec(v___x_823_);
v___x_825_ = lean_box(v_checkMeta_817_);
v___x_826_ = lean_box(v_safety_816_);
v___f_827_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_827_, 0, v___x_825_);
lean_closure_set(v___f_827_, 1, v_checkType_815_);
lean_closure_set(v___f_827_, 2, v___x_826_);
lean_closure_set(v___f_827_, 3, v_value_814_);
v___x_828_ = l_Lean_Environment_unlockAsync(v_env_824_);
v___x_829_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_828_, v___f_827_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_830_, lean_object* v_checkType_831_, lean_object* v_safety_832_, lean_object* v_checkMeta_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
uint8_t v_safety_boxed_839_; uint8_t v_checkMeta_boxed_840_; lean_object* v_res_841_; 
v_safety_boxed_839_ = lean_unbox(v_safety_832_);
v_checkMeta_boxed_840_ = lean_unbox(v_checkMeta_833_);
v_res_841_ = l_Lean_Meta_evalExprCore___redArg(v_value_830_, v_checkType_831_, v_safety_boxed_839_, v_checkMeta_boxed_840_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_842_, lean_object* v_value_843_, lean_object* v_checkType_844_, uint8_t v_safety_845_, uint8_t v_checkMeta_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Meta_evalExprCore___redArg(v_value_843_, v_checkType_844_, v_safety_845_, v_checkMeta_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_853_, lean_object* v_value_854_, lean_object* v_checkType_855_, lean_object* v_safety_856_, lean_object* v_checkMeta_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
uint8_t v_safety_boxed_863_; uint8_t v_checkMeta_boxed_864_; lean_object* v_res_865_; 
v_safety_boxed_863_ = lean_unbox(v_safety_856_);
v_checkMeta_boxed_864_ = lean_unbox(v_checkMeta_857_);
v_res_865_ = l_Lean_Meta_evalExprCore(v_00_u03b1_853_, v_value_854_, v_checkType_855_, v_safety_boxed_863_, v_checkMeta_boxed_864_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_880_, lean_object* v_constName_881_, uint8_t v_checkMeta_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_881_, v_checkMeta_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_889_, lean_object* v_constName_890_, lean_object* v_checkMeta_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v_checkMeta_boxed_897_; lean_object* v_res_898_; 
v_checkMeta_boxed_897_ = lean_unbox(v_checkMeta_891_);
v_res_898_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_889_, v_constName_890_, v_checkMeta_boxed_897_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_899_, lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_907_, lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_907_, v_msg_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_915_, v___y_917_, v___y_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_929_, lean_object* v_env_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_930_, v_x_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_938_, lean_object* v_env_939_, lean_object* v_x_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_938_, v_env_939_, v_x_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_955_, v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_962_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_966_, lean_object* v_type_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Meta_whnfD(v_type_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_987_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_Expr_isConstOf(v_a_974_, v_typeName_966_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_del_object(v___x_976_);
v___x_979_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_980_ = l_Lean_indentExpr(v_a_974_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_981_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_985_; 
lean_dec(v_a_974_);
v___x_983_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_983_);
v___x_985_ = v___x_976_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_973_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_973_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_996_, lean_object* v_type_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_996_, v_type_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v_typeName_996_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_1004_, lean_object* v_value_1005_, uint8_t v_safety_1006_, uint8_t v_checkMeta_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1013_, 0, v_typeName_1004_);
v___x_1014_ = l_Lean_Meta_evalExprCore___redArg(v_value_1005_, v___f_1013_, v_safety_1006_, v_checkMeta_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1015_, lean_object* v_value_1016_, lean_object* v_safety_1017_, lean_object* v_checkMeta_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
uint8_t v_safety_boxed_1024_; uint8_t v_checkMeta_boxed_1025_; lean_object* v_res_1026_; 
v_safety_boxed_1024_ = lean_unbox(v_safety_1017_);
v_checkMeta_boxed_1025_ = lean_unbox(v_checkMeta_1018_);
v_res_1026_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1015_, v_value_1016_, v_safety_boxed_1024_, v_checkMeta_boxed_1025_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1027_, lean_object* v_typeName_1028_, lean_object* v_value_1029_, uint8_t v_safety_1030_, uint8_t v_checkMeta_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1028_, v_value_1029_, v_safety_1030_, v_checkMeta_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_typeName_1039_, lean_object* v_value_1040_, lean_object* v_safety_1041_, lean_object* v_checkMeta_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
uint8_t v_safety_boxed_1048_; uint8_t v_checkMeta_boxed_1049_; lean_object* v_res_1050_; 
v_safety_boxed_1048_ = lean_unbox(v_safety_1041_);
v_checkMeta_boxed_1049_ = lean_unbox(v_checkMeta_1042_);
v_res_1050_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1038_, v_typeName_1039_, v_value_1040_, v_safety_boxed_1048_, v_checkMeta_boxed_1049_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
return v_res_1050_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1056_, lean_object* v_type_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
lean_inc_ref(v_expectedType_1056_);
lean_inc_ref(v_type_1057_);
v___x_1063_ = l_Lean_Meta_isExprDefEq(v_type_1057_, v_expectedType_1056_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1088_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_unbox(v_a_1064_);
lean_dec(v_a_1064_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_del_object(v___x_1066_);
v___x_1069_ = lean_box(0);
v___x_1070_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1071_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1057_, v_expectedType_1056_, v___x_1069_, v___x_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_1072_);
v___x_1075_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1074_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1075_;
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1071_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1071_);
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
else
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_dec_ref(v_type_1057_);
lean_dec_ref(v_expectedType_1056_);
v___x_1084_ = lean_box(0);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1084_);
v___x_1086_ = v___x_1066_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v_type_1057_);
lean_dec_ref(v_expectedType_1056_);
v_a_1089_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1063_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1063_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1097_, lean_object* v_type_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1097_, v_type_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1105_, lean_object* v_value_1106_, uint8_t v_safety_1107_, uint8_t v_checkMeta_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___f_1114_; lean_object* v___x_1115_; 
v___f_1114_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1114_, 0, v_expectedType_1105_);
v___x_1115_ = l_Lean_Meta_evalExprCore___redArg(v_value_1106_, v___f_1114_, v_safety_1107_, v_checkMeta_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1116_, lean_object* v_value_1117_, lean_object* v_safety_1118_, lean_object* v_checkMeta_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
uint8_t v_safety_boxed_1125_; uint8_t v_checkMeta_boxed_1126_; lean_object* v_res_1127_; 
v_safety_boxed_1125_ = lean_unbox(v_safety_1118_);
v_checkMeta_boxed_1126_ = lean_unbox(v_checkMeta_1119_);
v_res_1127_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1116_, v_value_1117_, v_safety_boxed_1125_, v_checkMeta_boxed_1126_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1128_, lean_object* v_expectedType_1129_, lean_object* v_value_1130_, uint8_t v_safety_1131_, uint8_t v_checkMeta_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1129_, v_value_1130_, v_safety_1131_, v_checkMeta_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_expectedType_1140_, lean_object* v_value_1141_, lean_object* v_safety_1142_, lean_object* v_checkMeta_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
uint8_t v_safety_boxed_1149_; uint8_t v_checkMeta_boxed_1150_; lean_object* v_res_1151_; 
v_safety_boxed_1149_ = lean_unbox(v_safety_1142_);
v_checkMeta_boxed_1150_ = lean_unbox(v_checkMeta_1143_);
v_res_1151_ = l_Lean_Meta_evalExpr(v_00_u03b1_1139_, v_expectedType_1140_, v_value_1141_, v_safety_boxed_1149_, v_checkMeta_boxed_1150_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
return v_res_1151_;
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

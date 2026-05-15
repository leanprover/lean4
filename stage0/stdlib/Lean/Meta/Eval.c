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
lean_object* v___y_277_; uint8_t v___y_278_; lean_object* v___y_279_; uint8_t v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v_fileName_286_; lean_object* v_fileMap_287_; lean_object* v_currRecDepth_288_; lean_object* v_ref_289_; lean_object* v_currNamespace_290_; lean_object* v_openDecls_291_; lean_object* v_initHeartbeats_292_; lean_object* v_maxHeartbeats_293_; lean_object* v_quotContext_294_; lean_object* v_currMacroScope_295_; lean_object* v_cancelTk_x3f_296_; uint8_t v_suppressElabErrors_297_; lean_object* v_inheritedTraceOptions_298_; lean_object* v___y_299_; lean_object* v___y_313_; uint8_t v___y_314_; lean_object* v___y_315_; uint8_t v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; uint8_t v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_338_; uint8_t v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; uint8_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; uint8_t v___y_348_; lean_object* v___y_349_; uint8_t v___y_350_; lean_object* v___y_371_; uint8_t v___y_372_; uint8_t v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_414_; uint8_t v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; uint8_t v___y_421_; uint8_t v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; uint8_t v___y_427_; lean_object* v___y_448_; lean_object* v___y_449_; uint8_t v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_491_; lean_object* v___y_492_; uint8_t v___y_493_; uint8_t v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; uint8_t v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; uint8_t v___y_503_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v_nextMacroScope_662_; lean_object* v_ngen_663_; lean_object* v_auxDeclNGen_664_; lean_object* v_traceState_665_; lean_object* v_messages_666_; lean_object* v_infoState_667_; lean_object* v_snapshotTasks_668_; lean_object* v___y_669_; lean_object* v___x_688_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_688_ = lean_st_ref_get(v___y_274_);
lean_inc_ref(v_value_270_);
v___x_701_ = l_Lean_Expr_getUsedConstants(v_value_270_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_array_get_size(v___x_701_);
v___x_704_ = lean_nat_dec_lt(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_dec_ref(v___x_701_);
lean_dec(v___x_688_);
goto v___jp_689_;
}
else
{
if (v___x_704_ == 0)
{
lean_dec_ref(v___x_701_);
lean_dec(v___x_688_);
goto v___jp_689_;
}
else
{
lean_object* v_env_705_; size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v_env_705_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_env_705_);
lean_dec(v___x_688_);
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_703_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(v_env_705_, v___x_701_, v___x_706_, v___x_707_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v_env_705_);
if (v___x_708_ == 0)
{
goto v___jp_689_;
}
else
{
v___y_616_ = v___y_271_;
v___y_617_ = v___y_272_;
v___y_618_ = v___y_273_;
v___y_619_ = v___y_274_;
goto v___jp_615_;
}
}
}
v___jp_276_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_282_, v___y_283_);
v___x_301_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_301_, 0, v_fileName_286_);
lean_ctor_set(v___x_301_, 1, v_fileMap_287_);
lean_ctor_set(v___x_301_, 2, v___y_282_);
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
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*14, v___y_278_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*14 + 1, v_suppressElabErrors_297_);
v___x_302_ = l_Lean_addAndCompile(v___y_281_, v___y_285_, v___y_280_, v___x_301_, v___y_299_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_302_);
v___x_303_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v___y_277_, v_checkMeta_267_, v___y_284_, v___y_279_, v___x_301_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___x_301_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_284_);
return v___x_303_;
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec_ref(v___x_301_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_279_);
lean_dec(v___y_277_);
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
lean_object* v___x_351_; lean_object* v_env_352_; lean_object* v_nextMacroScope_353_; lean_object* v_ngen_354_; lean_object* v_auxDeclNGen_355_; lean_object* v_traceState_356_; lean_object* v_messages_357_; lean_object* v_infoState_358_; lean_object* v_snapshotTasks_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
v___x_351_ = lean_st_ref_take(v___y_345_);
v_env_352_ = lean_ctor_get(v___x_351_, 0);
v_nextMacroScope_353_ = lean_ctor_get(v___x_351_, 1);
v_ngen_354_ = lean_ctor_get(v___x_351_, 2);
v_auxDeclNGen_355_ = lean_ctor_get(v___x_351_, 3);
v_traceState_356_ = lean_ctor_get(v___x_351_, 4);
v_messages_357_ = lean_ctor_get(v___x_351_, 6);
v_infoState_358_ = lean_ctor_get(v___x_351_, 7);
v_snapshotTasks_359_ = lean_ctor_get(v___x_351_, 8);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_351_, 5);
lean_dec(v_unused_369_);
v___x_361_ = v___x_351_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snapshotTasks_359_);
lean_inc(v_infoState_358_);
lean_inc(v_messages_357_);
lean_inc(v_traceState_356_);
lean_inc(v_auxDeclNGen_355_);
lean_inc(v_ngen_354_);
lean_inc(v_nextMacroScope_353_);
lean_inc(v_env_352_);
lean_dec(v___x_351_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = l_Lean_Kernel_enableDiag(v_env_352_, v___y_339_);
lean_inc_ref(v___y_346_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 5, v___y_346_);
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_nextMacroScope_353_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_ngen_354_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_auxDeclNGen_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_traceState_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 5, v___y_346_);
lean_ctor_set(v_reuseFailAlloc_367_, 6, v_messages_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 7, v_infoState_358_);
lean_ctor_set(v_reuseFailAlloc_367_, 8, v_snapshotTasks_359_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_st_ref_set(v___y_345_, v___x_365_);
v___y_313_ = v___y_340_;
v___y_314_ = v___y_339_;
v___y_315_ = v___y_341_;
v___y_316_ = v___y_342_;
v___y_317_ = v___y_343_;
v___y_318_ = v___y_344_;
v___y_319_ = v___y_349_;
v___y_320_ = v___y_347_;
v___y_321_ = v___y_348_;
v___y_322_ = v___y_338_;
v___y_323_ = v___y_345_;
goto v___jp_312_;
}
}
}
else
{
v___y_313_ = v___y_340_;
v___y_314_ = v___y_339_;
v___y_315_ = v___y_341_;
v___y_316_ = v___y_342_;
v___y_317_ = v___y_343_;
v___y_318_ = v___y_344_;
v___y_319_ = v___y_349_;
v___y_320_ = v___y_347_;
v___y_321_ = v___y_348_;
v___y_322_ = v___y_338_;
v___y_323_ = v___y_345_;
goto v___jp_312_;
}
}
v___jp_370_:
{
lean_object* v___x_384_; lean_object* v_fileName_385_; lean_object* v_fileMap_386_; lean_object* v_currRecDepth_387_; lean_object* v_ref_388_; lean_object* v_currNamespace_389_; lean_object* v_openDecls_390_; lean_object* v_initHeartbeats_391_; lean_object* v_maxHeartbeats_392_; lean_object* v_quotContext_393_; lean_object* v_currMacroScope_394_; lean_object* v_cancelTk_x3f_395_; uint8_t v_suppressElabErrors_396_; lean_object* v_inheritedTraceOptions_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_410_; 
v___x_384_ = lean_st_ref_get(v___y_383_);
v_fileName_385_ = lean_ctor_get(v___y_382_, 0);
v_fileMap_386_ = lean_ctor_get(v___y_382_, 1);
v_currRecDepth_387_ = lean_ctor_get(v___y_382_, 3);
v_ref_388_ = lean_ctor_get(v___y_382_, 5);
v_currNamespace_389_ = lean_ctor_get(v___y_382_, 6);
v_openDecls_390_ = lean_ctor_get(v___y_382_, 7);
v_initHeartbeats_391_ = lean_ctor_get(v___y_382_, 8);
v_maxHeartbeats_392_ = lean_ctor_get(v___y_382_, 9);
v_quotContext_393_ = lean_ctor_get(v___y_382_, 10);
v_currMacroScope_394_ = lean_ctor_get(v___y_382_, 11);
v_cancelTk_x3f_395_ = lean_ctor_get(v___y_382_, 12);
v_suppressElabErrors_396_ = lean_ctor_get_uint8(v___y_382_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_397_ = lean_ctor_get(v___y_382_, 13);
v_isSharedCheck_410_ = !lean_is_exclusive(v___y_382_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; lean_object* v_unused_412_; 
v_unused_411_ = lean_ctor_get(v___y_382_, 4);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v___y_382_, 2);
lean_dec(v_unused_412_);
v___x_399_ = v___y_382_;
v_isShared_400_ = v_isSharedCheck_410_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_inheritedTraceOptions_397_);
lean_inc(v_cancelTk_x3f_395_);
lean_inc(v_currMacroScope_394_);
lean_inc(v_quotContext_393_);
lean_inc(v_maxHeartbeats_392_);
lean_inc(v_initHeartbeats_391_);
lean_inc(v_openDecls_390_);
lean_inc(v_currNamespace_389_);
lean_inc(v_ref_388_);
lean_inc(v_currRecDepth_387_);
lean_inc(v_fileMap_386_);
lean_inc(v_fileName_385_);
lean_dec(v___y_382_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_410_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_env_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_env_401_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_env_401_);
lean_dec(v___x_384_);
v___x_402_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_381_, v___y_377_);
lean_inc_ref(v_inheritedTraceOptions_397_);
lean_inc(v_cancelTk_x3f_395_);
lean_inc(v_currMacroScope_394_);
lean_inc(v_quotContext_393_);
lean_inc(v_maxHeartbeats_392_);
lean_inc(v_initHeartbeats_391_);
lean_inc(v_openDecls_390_);
lean_inc(v_currNamespace_389_);
lean_inc(v_ref_388_);
lean_inc(v_currRecDepth_387_);
lean_inc_ref(v___y_381_);
lean_inc_ref(v_fileMap_386_);
lean_inc_ref(v_fileName_385_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 4, v___x_402_);
lean_ctor_set(v___x_399_, 2, v___y_381_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_fileName_385_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_fileMap_386_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v___y_381_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_currRecDepth_387_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v_ref_388_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_currNamespace_389_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_openDecls_390_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v_initHeartbeats_391_);
lean_ctor_set(v_reuseFailAlloc_409_, 9, v_maxHeartbeats_392_);
lean_ctor_set(v_reuseFailAlloc_409_, 10, v_quotContext_393_);
lean_ctor_set(v_reuseFailAlloc_409_, 11, v_currMacroScope_394_);
lean_ctor_set(v_reuseFailAlloc_409_, 12, v_cancelTk_x3f_395_);
lean_ctor_set(v_reuseFailAlloc_409_, 13, v_inheritedTraceOptions_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_409_, sizeof(void*)*14 + 1, v_suppressElabErrors_396_);
v___x_404_ = v_reuseFailAlloc_409_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; uint8_t v___x_408_; 
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*14, v___y_372_);
v___x_405_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
v___x_406_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_381_, v___x_405_, v___y_380_);
v___x_407_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_406_, v___y_376_);
v___x_408_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_401_);
lean_dec_ref(v_env_401_);
if (v___x_408_ == 0)
{
if (v___x_407_ == 0)
{
lean_dec_ref(v___x_404_);
v___y_277_ = v___y_371_;
v___y_278_ = v___x_407_;
v___y_279_ = v___y_374_;
v___y_280_ = v___y_373_;
v___y_281_ = v___y_375_;
v___y_282_ = v___x_406_;
v___y_283_ = v___y_377_;
v___y_284_ = v___y_379_;
v___y_285_ = v___y_380_;
v_fileName_286_ = v_fileName_385_;
v_fileMap_287_ = v_fileMap_386_;
v_currRecDepth_288_ = v_currRecDepth_387_;
v_ref_289_ = v_ref_388_;
v_currNamespace_290_ = v_currNamespace_389_;
v_openDecls_291_ = v_openDecls_390_;
v_initHeartbeats_292_ = v_initHeartbeats_391_;
v_maxHeartbeats_293_ = v_maxHeartbeats_392_;
v_quotContext_294_ = v_quotContext_393_;
v_currMacroScope_295_ = v_currMacroScope_394_;
v_cancelTk_x3f_296_ = v_cancelTk_x3f_395_;
v_suppressElabErrors_297_ = v_suppressElabErrors_396_;
v_inheritedTraceOptions_298_ = v_inheritedTraceOptions_397_;
v___y_299_ = v___y_383_;
goto v___jp_276_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_397_);
lean_dec(v_cancelTk_x3f_395_);
lean_dec(v_currMacroScope_394_);
lean_dec(v_quotContext_393_);
lean_dec(v_maxHeartbeats_392_);
lean_dec(v_initHeartbeats_391_);
lean_dec(v_openDecls_390_);
lean_dec(v_currNamespace_389_);
lean_dec(v_ref_388_);
lean_dec(v_currRecDepth_387_);
lean_dec_ref(v_fileMap_386_);
lean_dec_ref(v_fileName_385_);
v___y_338_ = v___x_404_;
v___y_339_ = v___x_407_;
v___y_340_ = v___y_371_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_373_;
v___y_343_ = v___y_375_;
v___y_344_ = v___x_406_;
v___y_345_ = v___y_383_;
v___y_346_ = v___y_378_;
v___y_347_ = v___y_379_;
v___y_348_ = v___y_380_;
v___y_349_ = v___y_377_;
v___y_350_ = v___x_408_;
goto v___jp_337_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_397_);
lean_dec(v_cancelTk_x3f_395_);
lean_dec(v_currMacroScope_394_);
lean_dec(v_quotContext_393_);
lean_dec(v_maxHeartbeats_392_);
lean_dec(v_initHeartbeats_391_);
lean_dec(v_openDecls_390_);
lean_dec(v_currNamespace_389_);
lean_dec(v_ref_388_);
lean_dec(v_currRecDepth_387_);
lean_dec_ref(v_fileMap_386_);
lean_dec_ref(v_fileName_385_);
v___y_338_ = v___x_404_;
v___y_339_ = v___x_407_;
v___y_340_ = v___y_371_;
v___y_341_ = v___y_374_;
v___y_342_ = v___y_373_;
v___y_343_ = v___y_375_;
v___y_344_ = v___x_406_;
v___y_345_ = v___y_383_;
v___y_346_ = v___y_378_;
v___y_347_ = v___y_379_;
v___y_348_ = v___y_380_;
v___y_349_ = v___y_377_;
v___y_350_ = v___x_407_;
goto v___jp_337_;
}
}
}
}
v___jp_413_:
{
if (v___y_427_ == 0)
{
lean_object* v___x_428_; lean_object* v_env_429_; lean_object* v_nextMacroScope_430_; lean_object* v_ngen_431_; lean_object* v_auxDeclNGen_432_; lean_object* v_traceState_433_; lean_object* v_messages_434_; lean_object* v_infoState_435_; lean_object* v_snapshotTasks_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
v___x_428_ = lean_st_ref_take(v___y_424_);
v_env_429_ = lean_ctor_get(v___x_428_, 0);
v_nextMacroScope_430_ = lean_ctor_get(v___x_428_, 1);
v_ngen_431_ = lean_ctor_get(v___x_428_, 2);
v_auxDeclNGen_432_ = lean_ctor_get(v___x_428_, 3);
v_traceState_433_ = lean_ctor_get(v___x_428_, 4);
v_messages_434_ = lean_ctor_get(v___x_428_, 6);
v_infoState_435_ = lean_ctor_get(v___x_428_, 7);
v_snapshotTasks_436_ = lean_ctor_get(v___x_428_, 8);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_428_, 5);
lean_dec(v_unused_446_);
v___x_438_ = v___x_428_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snapshotTasks_436_);
lean_inc(v_infoState_435_);
lean_inc(v_messages_434_);
lean_inc(v_traceState_433_);
lean_inc(v_auxDeclNGen_432_);
lean_inc(v_ngen_431_);
lean_inc(v_nextMacroScope_430_);
lean_inc(v_env_429_);
lean_dec(v___x_428_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = l_Lean_Kernel_enableDiag(v_env_429_, v___y_422_);
lean_inc_ref(v___y_419_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 5, v___y_419_);
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_nextMacroScope_430_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_ngen_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_auxDeclNGen_432_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_traceState_433_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v___y_419_);
lean_ctor_set(v_reuseFailAlloc_444_, 6, v_messages_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 7, v_infoState_435_);
lean_ctor_set(v_reuseFailAlloc_444_, 8, v_snapshotTasks_436_);
v___x_442_ = v_reuseFailAlloc_444_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; 
v___x_443_ = lean_st_ref_set(v___y_424_, v___x_442_);
v___y_371_ = v___y_414_;
v___y_372_ = v___y_422_;
v___y_373_ = v___y_415_;
v___y_374_ = v___y_416_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_418_;
v___y_377_ = v___y_425_;
v___y_378_ = v___y_419_;
v___y_379_ = v___y_420_;
v___y_380_ = v___y_421_;
v___y_381_ = v___y_426_;
v___y_382_ = v___y_423_;
v___y_383_ = v___y_424_;
goto v___jp_370_;
}
}
}
else
{
v___y_371_ = v___y_414_;
v___y_372_ = v___y_422_;
v___y_373_ = v___y_415_;
v___y_374_ = v___y_416_;
v___y_375_ = v___y_417_;
v___y_376_ = v___y_418_;
v___y_377_ = v___y_425_;
v___y_378_ = v___y_419_;
v___y_379_ = v___y_420_;
v___y_380_ = v___y_421_;
v___y_381_ = v___y_426_;
v___y_382_ = v___y_423_;
v___y_383_ = v___y_424_;
goto v___jp_370_;
}
}
v___jp_447_:
{
lean_object* v___x_460_; lean_object* v_fileName_461_; lean_object* v_fileMap_462_; lean_object* v_currRecDepth_463_; lean_object* v_ref_464_; lean_object* v_currNamespace_465_; lean_object* v_openDecls_466_; lean_object* v_initHeartbeats_467_; lean_object* v_maxHeartbeats_468_; lean_object* v_quotContext_469_; lean_object* v_currMacroScope_470_; lean_object* v_cancelTk_x3f_471_; uint8_t v_suppressElabErrors_472_; lean_object* v_inheritedTraceOptions_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_487_; 
v___x_460_ = lean_st_ref_get(v___y_459_);
v_fileName_461_ = lean_ctor_get(v___y_458_, 0);
v_fileMap_462_ = lean_ctor_get(v___y_458_, 1);
v_currRecDepth_463_ = lean_ctor_get(v___y_458_, 3);
v_ref_464_ = lean_ctor_get(v___y_458_, 5);
v_currNamespace_465_ = lean_ctor_get(v___y_458_, 6);
v_openDecls_466_ = lean_ctor_get(v___y_458_, 7);
v_initHeartbeats_467_ = lean_ctor_get(v___y_458_, 8);
v_maxHeartbeats_468_ = lean_ctor_get(v___y_458_, 9);
v_quotContext_469_ = lean_ctor_get(v___y_458_, 10);
v_currMacroScope_470_ = lean_ctor_get(v___y_458_, 11);
v_cancelTk_x3f_471_ = lean_ctor_get(v___y_458_, 12);
v_suppressElabErrors_472_ = lean_ctor_get_uint8(v___y_458_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_473_ = lean_ctor_get(v___y_458_, 13);
v_isSharedCheck_487_ = !lean_is_exclusive(v___y_458_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; lean_object* v_unused_489_; 
v_unused_488_ = lean_ctor_get(v___y_458_, 4);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v___y_458_, 2);
lean_dec(v_unused_489_);
v___x_475_ = v___y_458_;
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_inheritedTraceOptions_473_);
lean_inc(v_cancelTk_x3f_471_);
lean_inc(v_currMacroScope_470_);
lean_inc(v_quotContext_469_);
lean_inc(v_maxHeartbeats_468_);
lean_inc(v_initHeartbeats_467_);
lean_inc(v_openDecls_466_);
lean_inc(v_currNamespace_465_);
lean_inc(v_ref_464_);
lean_inc(v_currRecDepth_463_);
lean_inc(v_fileMap_462_);
lean_inc(v_fileName_461_);
lean_dec(v___y_458_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_env_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v_env_477_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_env_477_);
lean_dec(v___x_460_);
v___x_478_ = l_Lean_maxRecDepth;
v___x_479_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(v___y_457_, v___x_478_);
lean_inc_ref(v___y_457_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_479_);
lean_ctor_set(v___x_475_, 2, v___y_457_);
v___x_481_ = v___x_475_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_fileName_461_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_fileMap_462_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v___y_457_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_currRecDepth_463_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v_ref_464_);
lean_ctor_set(v_reuseFailAlloc_486_, 6, v_currNamespace_465_);
lean_ctor_set(v_reuseFailAlloc_486_, 7, v_openDecls_466_);
lean_ctor_set(v_reuseFailAlloc_486_, 8, v_initHeartbeats_467_);
lean_ctor_set(v_reuseFailAlloc_486_, 9, v_maxHeartbeats_468_);
lean_ctor_set(v_reuseFailAlloc_486_, 10, v_quotContext_469_);
lean_ctor_set(v_reuseFailAlloc_486_, 11, v_currMacroScope_470_);
lean_ctor_set(v_reuseFailAlloc_486_, 12, v_cancelTk_x3f_471_);
lean_ctor_set(v_reuseFailAlloc_486_, 13, v_inheritedTraceOptions_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*14 + 1, v_suppressElabErrors_472_);
v___x_481_ = v_reuseFailAlloc_486_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; uint8_t v___x_485_; 
lean_ctor_set_uint8(v___x_481_, sizeof(void*)*14, v___y_452_);
v___x_482_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_483_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v___y_457_, v___x_482_, v___y_450_);
v___x_484_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_483_, v___y_453_);
v___x_485_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_477_);
lean_dec_ref(v_env_477_);
if (v___x_485_ == 0)
{
if (v___x_484_ == 0)
{
v___y_371_ = v___y_448_;
v___y_372_ = v___x_484_;
v___y_373_ = v___y_450_;
v___y_374_ = v___y_449_;
v___y_375_ = v___y_451_;
v___y_376_ = v___y_453_;
v___y_377_ = v___x_478_;
v___y_378_ = v___y_455_;
v___y_379_ = v___y_454_;
v___y_380_ = v___y_456_;
v___y_381_ = v___x_483_;
v___y_382_ = v___x_481_;
v___y_383_ = v___y_459_;
goto v___jp_370_;
}
else
{
v___y_414_ = v___y_448_;
v___y_415_ = v___y_450_;
v___y_416_ = v___y_449_;
v___y_417_ = v___y_451_;
v___y_418_ = v___y_453_;
v___y_419_ = v___y_455_;
v___y_420_ = v___y_454_;
v___y_421_ = v___y_456_;
v___y_422_ = v___x_484_;
v___y_423_ = v___x_481_;
v___y_424_ = v___y_459_;
v___y_425_ = v___x_478_;
v___y_426_ = v___x_483_;
v___y_427_ = v___x_485_;
goto v___jp_413_;
}
}
else
{
v___y_414_ = v___y_448_;
v___y_415_ = v___y_450_;
v___y_416_ = v___y_449_;
v___y_417_ = v___y_451_;
v___y_418_ = v___y_453_;
v___y_419_ = v___y_455_;
v___y_420_ = v___y_454_;
v___y_421_ = v___y_456_;
v___y_422_ = v___x_484_;
v___y_423_ = v___x_481_;
v___y_424_ = v___y_459_;
v___y_425_ = v___x_478_;
v___y_426_ = v___x_483_;
v___y_427_ = v___x_484_;
goto v___jp_413_;
}
}
}
}
v___jp_490_:
{
if (v___y_503_ == 0)
{
lean_object* v___x_504_; lean_object* v_env_505_; lean_object* v_nextMacroScope_506_; lean_object* v_ngen_507_; lean_object* v_auxDeclNGen_508_; lean_object* v_traceState_509_; lean_object* v_messages_510_; lean_object* v_infoState_511_; lean_object* v_snapshotTasks_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_521_; 
v___x_504_ = lean_st_ref_take(v___y_501_);
v_env_505_ = lean_ctor_get(v___x_504_, 0);
v_nextMacroScope_506_ = lean_ctor_get(v___x_504_, 1);
v_ngen_507_ = lean_ctor_get(v___x_504_, 2);
v_auxDeclNGen_508_ = lean_ctor_get(v___x_504_, 3);
v_traceState_509_ = lean_ctor_get(v___x_504_, 4);
v_messages_510_ = lean_ctor_get(v___x_504_, 6);
v_infoState_511_ = lean_ctor_get(v___x_504_, 7);
v_snapshotTasks_512_ = lean_ctor_get(v___x_504_, 8);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v___x_504_, 5);
lean_dec(v_unused_522_);
v___x_514_ = v___x_504_;
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snapshotTasks_512_);
lean_inc(v_infoState_511_);
lean_inc(v_messages_510_);
lean_inc(v_traceState_509_);
lean_inc(v_auxDeclNGen_508_);
lean_inc(v_ngen_507_);
lean_inc(v_nextMacroScope_506_);
lean_inc(v_env_505_);
lean_dec(v___x_504_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = l_Lean_Kernel_enableDiag(v_env_505_, v___y_494_);
lean_inc_ref(v___y_497_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 5, v___y_497_);
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_nextMacroScope_506_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_ngen_507_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_auxDeclNGen_508_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v_traceState_509_);
lean_ctor_set(v_reuseFailAlloc_520_, 5, v___y_497_);
lean_ctor_set(v_reuseFailAlloc_520_, 6, v_messages_510_);
lean_ctor_set(v_reuseFailAlloc_520_, 7, v_infoState_511_);
lean_ctor_set(v_reuseFailAlloc_520_, 8, v_snapshotTasks_512_);
v___x_518_ = v_reuseFailAlloc_520_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
v___x_519_ = lean_st_ref_set(v___y_501_, v___x_518_);
v___y_448_ = v___y_491_;
v___y_449_ = v___y_492_;
v___y_450_ = v___y_493_;
v___y_451_ = v___y_495_;
v___y_452_ = v___y_494_;
v___y_453_ = v___y_496_;
v___y_454_ = v___y_498_;
v___y_455_ = v___y_497_;
v___y_456_ = v___y_499_;
v___y_457_ = v___y_500_;
v___y_458_ = v___y_502_;
v___y_459_ = v___y_501_;
goto v___jp_447_;
}
}
}
else
{
v___y_448_ = v___y_491_;
v___y_449_ = v___y_492_;
v___y_450_ = v___y_493_;
v___y_451_ = v___y_495_;
v___y_452_ = v___y_494_;
v___y_453_ = v___y_496_;
v___y_454_ = v___y_498_;
v___y_455_ = v___y_497_;
v___y_456_ = v___y_499_;
v___y_457_ = v___y_500_;
v___y_458_ = v___y_502_;
v___y_459_ = v___y_501_;
goto v___jp_447_;
}
}
v___jp_523_:
{
lean_object* v___x_532_; 
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
lean_inc_ref(v___y_525_);
v___x_532_ = lean_infer_type(v___y_525_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_n(v_a_533_, 2);
lean_dec_ref(v___x_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
v___x_534_ = lean_apply_6(v_checkType_268_, v_a_533_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, lean_box(0));
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v___x_535_; lean_object* v_env_536_; lean_object* v_nextMacroScope_537_; lean_object* v_ngen_538_; lean_object* v_auxDeclNGen_539_; lean_object* v_traceState_540_; lean_object* v_messages_541_; lean_object* v_infoState_542_; lean_object* v_snapshotTasks_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v___x_534_);
v___x_535_ = lean_st_ref_take(v___y_531_);
v_env_536_ = lean_ctor_get(v___x_535_, 0);
v_nextMacroScope_537_ = lean_ctor_get(v___x_535_, 1);
v_ngen_538_ = lean_ctor_get(v___x_535_, 2);
v_auxDeclNGen_539_ = lean_ctor_get(v___x_535_, 3);
v_traceState_540_ = lean_ctor_get(v___x_535_, 4);
v_messages_541_ = lean_ctor_get(v___x_535_, 6);
v_infoState_542_ = lean_ctor_get(v___x_535_, 7);
v_snapshotTasks_543_ = lean_ctor_get(v___x_535_, 8);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v___x_535_, 5);
lean_dec(v_unused_598_);
v___x_545_ = v___x_535_;
v_isShared_546_ = v_isSharedCheck_597_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snapshotTasks_543_);
lean_inc(v_infoState_542_);
lean_inc(v_messages_541_);
lean_inc(v_traceState_540_);
lean_inc(v_auxDeclNGen_539_);
lean_inc(v_ngen_538_);
lean_inc(v_nextMacroScope_537_);
lean_inc(v_env_536_);
lean_dec(v___x_535_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_597_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_547_ = lean_array_to_list(v___y_527_);
lean_inc_n(v___y_524_, 3);
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v___y_524_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
lean_ctor_set(v___x_548_, 2, v_a_533_);
lean_inc(v___y_526_);
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v___y_524_);
lean_ctor_set(v___x_549_, 1, v___y_526_);
v___x_550_ = l_Lean_markMeta(v_env_536_, v___y_524_);
v___x_551_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 5, v___x_551_);
lean_ctor_set(v___x_545_, 0, v___x_550_);
v___x_553_ = v___x_545_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_nextMacroScope_537_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_ngen_538_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_auxDeclNGen_539_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_traceState_540_);
lean_ctor_set(v_reuseFailAlloc_596_, 5, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_596_, 6, v_messages_541_);
lean_ctor_set(v_reuseFailAlloc_596_, 7, v_infoState_542_);
lean_ctor_set(v_reuseFailAlloc_596_, 8, v_snapshotTasks_543_);
v___x_553_ = v_reuseFailAlloc_596_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_mctx_556_; lean_object* v_zetaDeltaFVarIds_557_; lean_object* v_postponed_558_; lean_object* v_diag_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_594_; 
v___x_554_ = lean_st_ref_set(v___y_531_, v___x_553_);
v___x_555_ = lean_st_ref_take(v___y_529_);
v_mctx_556_ = lean_ctor_get(v___x_555_, 0);
v_zetaDeltaFVarIds_557_ = lean_ctor_get(v___x_555_, 2);
v_postponed_558_ = lean_ctor_get(v___x_555_, 3);
v_diag_559_ = lean_ctor_get(v___x_555_, 4);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v___x_555_, 1);
lean_dec(v_unused_595_);
v___x_561_ = v___x_555_;
v_isShared_562_ = v_isSharedCheck_594_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_diag_559_);
lean_inc(v_postponed_558_);
lean_inc(v_zetaDeltaFVarIds_557_);
lean_inc(v_mctx_556_);
lean_dec(v___x_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_594_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_mctx_556_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_zetaDeltaFVarIds_557_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_postponed_558_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_diag_559_);
v___x_565_ = v_reuseFailAlloc_593_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_env_568_; lean_object* v_checked_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_566_ = lean_st_ref_set(v___y_529_, v___x_565_);
v___x_567_ = lean_st_ref_get(v___y_531_);
v_env_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_568_);
lean_dec(v___x_567_);
v_checked_569_ = lean_ctor_get(v_env_568_, 2);
lean_inc_ref(v_checked_569_);
lean_dec_ref(v_env_568_);
v___x_570_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4));
v___x_571_ = l_Lean_traceBlock___redArg(v___x_570_, v_checked_569_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_572_; lean_object* v_options_573_; lean_object* v_env_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; uint8_t v___x_584_; 
lean_dec_ref(v___x_571_);
v___x_572_ = lean_st_ref_get(v___y_531_);
v_options_573_ = lean_ctor_get(v___y_530_, 2);
v_env_574_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_env_574_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_576_, 0, v___x_548_);
lean_ctor_set(v___x_576_, 1, v___y_525_);
lean_ctor_set(v___x_576_, 2, v___x_575_);
lean_ctor_set(v___x_576_, 3, v___x_549_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*4, v_safety_269_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = 1;
v___x_579_ = 0;
v___x_580_ = l_Lean_Elab_async;
lean_inc_ref(v_options_573_);
v___x_581_ = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(v_options_573_, v___x_580_, v___x_579_);
v___x_582_ = l_Lean_diagnostics;
v___x_583_ = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(v___x_581_, v___x_582_);
v___x_584_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_574_);
lean_dec_ref(v_env_574_);
if (v___x_584_ == 0)
{
if (v___x_583_ == 0)
{
v___y_448_ = v___y_524_;
v___y_449_ = v___y_529_;
v___y_450_ = v___x_579_;
v___y_451_ = v___x_577_;
v___y_452_ = v___x_583_;
v___y_453_ = v___x_582_;
v___y_454_ = v___y_528_;
v___y_455_ = v___x_551_;
v___y_456_ = v___x_578_;
v___y_457_ = v___x_581_;
v___y_458_ = v___y_530_;
v___y_459_ = v___y_531_;
goto v___jp_447_;
}
else
{
v___y_491_ = v___y_524_;
v___y_492_ = v___y_529_;
v___y_493_ = v___x_579_;
v___y_494_ = v___x_583_;
v___y_495_ = v___x_577_;
v___y_496_ = v___x_582_;
v___y_497_ = v___x_551_;
v___y_498_ = v___y_528_;
v___y_499_ = v___x_578_;
v___y_500_ = v___x_581_;
v___y_501_ = v___y_531_;
v___y_502_ = v___y_530_;
v___y_503_ = v___x_584_;
goto v___jp_490_;
}
}
else
{
v___y_491_ = v___y_524_;
v___y_492_ = v___y_529_;
v___y_493_ = v___x_579_;
v___y_494_ = v___x_583_;
v___y_495_ = v___x_577_;
v___y_496_ = v___x_582_;
v___y_497_ = v___x_551_;
v___y_498_ = v___y_528_;
v___y_499_ = v___x_578_;
v___y_500_ = v___x_581_;
v___y_501_ = v___y_531_;
v___y_502_ = v___y_530_;
v___y_503_ = v___x_583_;
goto v___jp_490_;
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
v_a_585_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_571_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_571_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
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
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_a_533_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
v_a_599_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_534_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_534_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v_checkType_268_);
v_a_607_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_532_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_532_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
v___jp_615_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_st_ref_get(v___y_619_);
v___x_621_ = ((lean_object*)(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6));
v___x_622_ = l_Lean_Core_mkFreshUserName(v___x_621_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___x_622_);
v___x_624_ = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(v_value_270_, v___y_617_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v_env_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_params_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc_n(v_a_625_, 2);
lean_dec_ref(v___x_624_);
v_env_626_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_env_626_);
lean_dec(v___x_620_);
v___x_627_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
v___x_628_ = l_Lean_collectLevelParams(v___x_627_, v_a_625_);
v_params_629_ = lean_ctor_get(v___x_628_, 2);
lean_inc_ref(v_params_629_);
lean_dec_ref(v___x_628_);
v___x_630_ = l_Lean_mkPrivateName(v_env_626_, v_a_623_);
lean_dec_ref(v_env_626_);
v___x_631_ = lean_box(0);
v___x_632_ = l_Lean_Expr_hasMVar(v_a_625_);
if (v___x_632_ == 0)
{
v___y_524_ = v___x_630_;
v___y_525_ = v_a_625_;
v___y_526_ = v___x_631_;
v___y_527_ = v_params_629_;
v___y_528_ = v___y_616_;
v___y_529_ = v___y_617_;
v___y_530_ = v___y_618_;
v___y_531_ = v___y_619_;
goto v___jp_523_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_633_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
lean_inc(v_a_625_);
v___x_634_ = l_Lean_indentExpr(v_a_625_);
v___x_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_635_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec_ref(v___x_636_);
v___y_524_ = v___x_630_;
v___y_525_ = v_a_625_;
v___y_526_ = v___x_631_;
v___y_527_ = v_params_629_;
v___y_528_ = v___y_616_;
v___y_529_ = v___y_617_;
v___y_530_ = v___y_618_;
v___y_531_ = v___y_619_;
goto v___jp_523_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v___x_630_);
lean_dec_ref(v_params_629_);
lean_dec(v_a_625_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_checkType_268_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_a_623_);
lean_dec(v___x_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_checkType_268_);
v_a_645_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_624_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_624_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v___x_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_value_270_);
lean_dec_ref(v_checkType_268_);
v_a_653_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_622_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_622_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
v___jp_661_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_mctx_674_; lean_object* v_zetaDeltaFVarIds_675_; lean_object* v_postponed_676_; lean_object* v_diag_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_686_; 
v___x_670_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
v___x_671_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_671_, 0, v___y_669_);
lean_ctor_set(v___x_671_, 1, v_nextMacroScope_662_);
lean_ctor_set(v___x_671_, 2, v_ngen_663_);
lean_ctor_set(v___x_671_, 3, v_auxDeclNGen_664_);
lean_ctor_set(v___x_671_, 4, v_traceState_665_);
lean_ctor_set(v___x_671_, 5, v___x_670_);
lean_ctor_set(v___x_671_, 6, v_messages_666_);
lean_ctor_set(v___x_671_, 7, v_infoState_667_);
lean_ctor_set(v___x_671_, 8, v_snapshotTasks_668_);
v___x_672_ = lean_st_ref_set(v___y_274_, v___x_671_);
v___x_673_ = lean_st_ref_take(v___y_272_);
v_mctx_674_ = lean_ctor_get(v___x_673_, 0);
v_zetaDeltaFVarIds_675_ = lean_ctor_get(v___x_673_, 2);
v_postponed_676_ = lean_ctor_get(v___x_673_, 3);
v_diag_677_ = lean_ctor_get(v___x_673_, 4);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_673_, 1);
lean_dec(v_unused_687_);
v___x_679_ = v___x_673_;
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_diag_677_);
lean_inc(v_postponed_676_);
lean_inc(v_zetaDeltaFVarIds_675_);
lean_inc(v_mctx_674_);
lean_dec(v___x_673_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_mctx_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_zetaDeltaFVarIds_675_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_postponed_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_diag_677_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; 
v___x_684_ = lean_st_ref_set(v___y_272_, v___x_683_);
v___y_616_ = v___y_271_;
v___y_617_ = v___y_272_;
v___y_618_ = v___y_273_;
v___y_619_ = v___y_274_;
goto v___jp_615_;
}
}
}
v___jp_689_:
{
lean_object* v___x_690_; lean_object* v_env_691_; lean_object* v_nextMacroScope_692_; lean_object* v_ngen_693_; lean_object* v_auxDeclNGen_694_; lean_object* v_traceState_695_; lean_object* v_messages_696_; lean_object* v_infoState_697_; lean_object* v_snapshotTasks_698_; lean_object* v___x_699_; 
v___x_690_ = lean_st_ref_take(v___y_274_);
v_env_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref_n(v_env_691_, 2);
v_nextMacroScope_692_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_nextMacroScope_692_);
v_ngen_693_ = lean_ctor_get(v___x_690_, 2);
lean_inc_ref(v_ngen_693_);
v_auxDeclNGen_694_ = lean_ctor_get(v___x_690_, 3);
lean_inc_ref(v_auxDeclNGen_694_);
v_traceState_695_ = lean_ctor_get(v___x_690_, 4);
lean_inc_ref(v_traceState_695_);
v_messages_696_ = lean_ctor_get(v___x_690_, 6);
lean_inc_ref(v_messages_696_);
v_infoState_697_ = lean_ctor_get(v___x_690_, 7);
lean_inc_ref(v_infoState_697_);
v_snapshotTasks_698_ = lean_ctor_get(v___x_690_, 8);
lean_inc_ref(v_snapshotTasks_698_);
lean_dec(v___x_690_);
v___x_699_ = l_Lean_Environment_importEnv_x3f(v_env_691_);
if (lean_obj_tag(v___x_699_) == 0)
{
v_nextMacroScope_662_ = v_nextMacroScope_692_;
v_ngen_663_ = v_ngen_693_;
v_auxDeclNGen_664_ = v_auxDeclNGen_694_;
v_traceState_665_ = v_traceState_695_;
v_messages_666_ = v_messages_696_;
v_infoState_667_ = v_infoState_697_;
v_snapshotTasks_668_ = v_snapshotTasks_698_;
v___y_669_ = v_env_691_;
goto v___jp_661_;
}
else
{
lean_object* v_val_700_; 
lean_dec_ref(v_env_691_);
v_val_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref(v___x_699_);
v_nextMacroScope_662_ = v_nextMacroScope_692_;
v_ngen_663_ = v_ngen_693_;
v_auxDeclNGen_664_ = v_auxDeclNGen_694_;
v_traceState_665_ = v_traceState_695_;
v_messages_666_ = v_messages_696_;
v_infoState_667_ = v_infoState_697_;
v_snapshotTasks_668_ = v_snapshotTasks_698_;
v___y_669_ = v_val_700_;
goto v___jp_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* v_checkMeta_709_, lean_object* v_checkType_710_, lean_object* v_safety_711_, lean_object* v_value_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v_checkMeta_boxed_718_; uint8_t v_safety_boxed_719_; lean_object* v_res_720_; 
v_checkMeta_boxed_718_ = lean_unbox(v_checkMeta_709_);
v_safety_boxed_719_ = lean_unbox(v_safety_711_);
v_res_720_ = l_Lean_Meta_evalExprCore___redArg___lam__0(v_checkMeta_boxed_718_, v_checkType_710_, v_safety_boxed_719_, v_value_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* v_env_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v_nextMacroScope_726_; lean_object* v_ngen_727_; lean_object* v_auxDeclNGen_728_; lean_object* v_traceState_729_; lean_object* v_messages_730_; lean_object* v_infoState_731_; lean_object* v_snapshotTasks_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_758_; 
v___x_725_ = lean_st_ref_take(v___y_723_);
v_nextMacroScope_726_ = lean_ctor_get(v___x_725_, 1);
v_ngen_727_ = lean_ctor_get(v___x_725_, 2);
v_auxDeclNGen_728_ = lean_ctor_get(v___x_725_, 3);
v_traceState_729_ = lean_ctor_get(v___x_725_, 4);
v_messages_730_ = lean_ctor_get(v___x_725_, 6);
v_infoState_731_ = lean_ctor_get(v___x_725_, 7);
v_snapshotTasks_732_ = lean_ctor_get(v___x_725_, 8);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; lean_object* v_unused_760_; 
v_unused_759_ = lean_ctor_get(v___x_725_, 5);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v___x_725_, 0);
lean_dec(v_unused_760_);
v___x_734_ = v___x_725_;
v_isShared_735_ = v_isSharedCheck_758_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_snapshotTasks_732_);
lean_inc(v_infoState_731_);
lean_inc(v_messages_730_);
lean_inc(v_traceState_729_);
lean_inc(v_auxDeclNGen_728_);
lean_inc(v_ngen_727_);
lean_inc(v_nextMacroScope_726_);
lean_dec(v___x_725_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_758_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 5, v___x_736_);
lean_ctor_set(v___x_734_, 0, v_env_721_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_env_721_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_nextMacroScope_726_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_ngen_727_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_auxDeclNGen_728_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v_traceState_729_);
lean_ctor_set(v_reuseFailAlloc_757_, 5, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_757_, 6, v_messages_730_);
lean_ctor_set(v_reuseFailAlloc_757_, 7, v_infoState_731_);
lean_ctor_set(v_reuseFailAlloc_757_, 8, v_snapshotTasks_732_);
v___x_738_ = v_reuseFailAlloc_757_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_mctx_741_; lean_object* v_zetaDeltaFVarIds_742_; lean_object* v_postponed_743_; lean_object* v_diag_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_755_; 
v___x_739_ = lean_st_ref_set(v___y_723_, v___x_738_);
v___x_740_ = lean_st_ref_take(v___y_722_);
v_mctx_741_ = lean_ctor_get(v___x_740_, 0);
v_zetaDeltaFVarIds_742_ = lean_ctor_get(v___x_740_, 2);
v_postponed_743_ = lean_ctor_get(v___x_740_, 3);
v_diag_744_ = lean_ctor_get(v___x_740_, 4);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v___x_740_, 1);
lean_dec(v_unused_756_);
v___x_746_ = v___x_740_;
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_diag_744_);
lean_inc(v_postponed_743_);
lean_inc(v_zetaDeltaFVarIds_742_);
lean_inc(v_mctx_741_);
lean_dec(v___x_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_obj_once(&l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3, &l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_mctx_741_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_zetaDeltaFVarIds_742_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_postponed_743_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_diag_744_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_st_ref_set(v___y_722_, v___x_750_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* v_env_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* v_env_766_, lean_object* v_x_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; lean_object* v_env_774_; lean_object* v_a_776_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_773_ = lean_st_ref_get(v___y_771_);
v_env_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc_ref(v_env_774_);
lean_dec(v___x_773_);
v___x_786_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_766_, v___y_769_, v___y_771_);
lean_dec_ref(v___x_786_);
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_769_);
lean_inc_ref(v___y_768_);
v___x_787_ = lean_apply_5(v_x_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, lean_box(0));
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref(v___x_787_);
v___x_789_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_774_, v___y_769_, v___y_771_);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_797_);
v___x_791_ = v___x_789_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_dec(v___x_789_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_a_788_);
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_788_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_787_);
v_a_776_ = v_a_798_;
goto v___jp_775_;
}
v___jp_775_:
{
lean_object* v___x_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v___x_777_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_774_, v___y_769_, v___y_771_);
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
lean_ctor_set_tag(v___x_779_, 1);
lean_ctor_set(v___x_779_, 0, v_a_776_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* v_env_799_, lean_object* v_x_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_799_, v_x_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* v_value_807_, lean_object* v_checkType_808_, uint8_t v_safety_809_, uint8_t v_checkMeta_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; lean_object* v_env_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_816_ = lean_st_ref_get(v_a_814_);
v_env_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_ref(v_env_817_);
lean_dec(v___x_816_);
v___x_818_ = lean_box(v_checkMeta_810_);
v___x_819_ = lean_box(v_safety_809_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_820_, 0, v___x_818_);
lean_closure_set(v___f_820_, 1, v_checkType_808_);
lean_closure_set(v___f_820_, 2, v___x_819_);
lean_closure_set(v___f_820_, 3, v_value_807_);
v___x_821_ = l_Lean_Environment_unlockAsync(v_env_817_);
v___x_822_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v___x_821_, v___f_820_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* v_value_823_, lean_object* v_checkType_824_, lean_object* v_safety_825_, lean_object* v_checkMeta_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
uint8_t v_safety_boxed_832_; uint8_t v_checkMeta_boxed_833_; lean_object* v_res_834_; 
v_safety_boxed_832_ = lean_unbox(v_safety_825_);
v_checkMeta_boxed_833_ = lean_unbox(v_checkMeta_826_);
v_res_834_ = l_Lean_Meta_evalExprCore___redArg(v_value_823_, v_checkType_824_, v_safety_boxed_832_, v_checkMeta_boxed_833_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* v_00_u03b1_835_, lean_object* v_value_836_, lean_object* v_checkType_837_, uint8_t v_safety_838_, uint8_t v_checkMeta_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_evalExprCore___redArg(v_value_836_, v_checkType_837_, v_safety_838_, v_checkMeta_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* v_00_u03b1_846_, lean_object* v_value_847_, lean_object* v_checkType_848_, lean_object* v_safety_849_, lean_object* v_checkMeta_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
uint8_t v_safety_boxed_856_; uint8_t v_checkMeta_boxed_857_; lean_object* v_res_858_; 
v_safety_boxed_856_ = lean_unbox(v_safety_849_);
v_checkMeta_boxed_857_ = lean_unbox(v_checkMeta_850_);
v_res_858_ = l_Lean_Meta_evalExprCore(v_00_u03b1_846_, v_value_847_, v_checkType_848_, v_safety_boxed_856_, v_checkMeta_boxed_857_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* v_00_u03b1_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* v_00_u03b1_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(v_00_u03b1_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* v_00_u03b1_873_, lean_object* v_constName_874_, uint8_t v_checkMeta_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(v_constName_874_, v_checkMeta_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* v_00_u03b1_882_, lean_object* v_constName_883_, lean_object* v_checkMeta_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v_checkMeta_boxed_890_; lean_object* v_res_891_; 
v_checkMeta_boxed_890_ = lean_unbox(v_checkMeta_884_);
v_res_891_ = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(v_00_u03b1_882_, v_constName_883_, v_checkMeta_boxed_890_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* v_00_u03b1_892_, lean_object* v_msg_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v_msg_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* v_00_u03b1_900_, lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(v_00_u03b1_900_, v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* v_env_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(v_env_908_, v___y_910_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* v_env_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(v_env_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* v_00_u03b1_922_, lean_object* v_env_923_, lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(v_env_923_, v_x_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* v_00_u03b1_931_, lean_object* v_env_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(v_00_u03b1_931_, v_env_932_, v_x_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* v_00_u03b1_940_, lean_object* v_x_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(v_x_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* v_00_u03b1_948_, lean_object* v_x_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(v_00_u03b1_948_, v_x_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_955_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* v_typeName_959_, lean_object* v_type_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_whnfD(v_type_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_980_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_980_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_980_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_980_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
uint8_t v___x_971_; 
v___x_971_ = l_Lean_Expr_isConstOf(v_a_967_, v_typeName_959_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_del_object(v___x_969_);
v___x_972_ = lean_obj_once(&l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1, &l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
v___x_973_ = l_Lean_indentExpr(v_a_967_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_974_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v_a_967_);
v___x_976_ = lean_box(0);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_976_);
v___x_978_ = v___x_969_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_966_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_966_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* v_typeName_989_, lean_object* v_type_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Meta_evalExpr_x27___redArg___lam__0(v_typeName_989_, v_type_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v_typeName_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* v_typeName_997_, lean_object* v_value_998_, uint8_t v_safety_999_, uint8_t v_checkMeta_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___f_1006_; lean_object* v___x_1007_; 
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1006_, 0, v_typeName_997_);
v___x_1007_ = l_Lean_Meta_evalExprCore___redArg(v_value_998_, v___f_1006_, v_safety_999_, v_checkMeta_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* v_typeName_1008_, lean_object* v_value_1009_, lean_object* v_safety_1010_, lean_object* v_checkMeta_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
uint8_t v_safety_boxed_1017_; uint8_t v_checkMeta_boxed_1018_; lean_object* v_res_1019_; 
v_safety_boxed_1017_ = lean_unbox(v_safety_1010_);
v_checkMeta_boxed_1018_ = lean_unbox(v_checkMeta_1011_);
v_res_1019_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1008_, v_value_1009_, v_safety_boxed_1017_, v_checkMeta_boxed_1018_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* v_00_u03b1_1020_, lean_object* v_typeName_1021_, lean_object* v_value_1022_, uint8_t v_safety_1023_, uint8_t v_checkMeta_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_evalExpr_x27___redArg(v_typeName_1021_, v_value_1022_, v_safety_1023_, v_checkMeta_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_typeName_1032_, lean_object* v_value_1033_, lean_object* v_safety_1034_, lean_object* v_checkMeta_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
uint8_t v_safety_boxed_1041_; uint8_t v_checkMeta_boxed_1042_; lean_object* v_res_1043_; 
v_safety_boxed_1041_ = lean_unbox(v_safety_1034_);
v_checkMeta_boxed_1042_ = lean_unbox(v_checkMeta_1035_);
v_res_1043_ = l_Lean_Meta_evalExpr_x27(v_00_u03b1_1031_, v_typeName_1032_, v_value_1033_, v_safety_boxed_1041_, v_checkMeta_boxed_1042_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1043_;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* v_expectedType_1049_, lean_object* v_type_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
lean_inc_ref(v_expectedType_1049_);
lean_inc_ref(v_type_1050_);
v___x_1056_ = l_Lean_Meta_isExprDefEq(v_type_1050_, v_expectedType_1049_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1081_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1081_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1081_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_unbox(v_a_1057_);
lean_dec(v_a_1057_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_del_object(v___x_1059_);
v___x_1062_ = lean_box(0);
v___x_1063_ = ((lean_object*)(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0));
v___x_1064_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_type_1050_, v_expectedType_1049_, v___x_1062_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = lean_obj_once(&l_Lean_Meta_evalExpr___redArg___lam__0___closed__2, &l_Lean_Meta_evalExpr___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_a_1065_);
v___x_1068_ = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(v___x_1067_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1068_;
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1064_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1064_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
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
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec_ref(v_type_1050_);
lean_dec_ref(v_expectedType_1049_);
v___x_1077_ = lean_box(0);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1077_);
v___x_1079_ = v___x_1059_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_type_1050_);
lean_dec_ref(v_expectedType_1049_);
v_a_1082_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1056_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1056_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* v_expectedType_1090_, lean_object* v_type_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Meta_evalExpr___redArg___lam__0(v_expectedType_1090_, v_type_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* v_expectedType_1098_, lean_object* v_value_1099_, uint8_t v_safety_1100_, uint8_t v_checkMeta_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___f_1107_; lean_object* v___x_1108_; 
v___f_1107_ = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1107_, 0, v_expectedType_1098_);
v___x_1108_ = l_Lean_Meta_evalExprCore___redArg(v_value_1099_, v___f_1107_, v_safety_1100_, v_checkMeta_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* v_expectedType_1109_, lean_object* v_value_1110_, lean_object* v_safety_1111_, lean_object* v_checkMeta_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
uint8_t v_safety_boxed_1118_; uint8_t v_checkMeta_boxed_1119_; lean_object* v_res_1120_; 
v_safety_boxed_1118_ = lean_unbox(v_safety_1111_);
v_checkMeta_boxed_1119_ = lean_unbox(v_checkMeta_1112_);
v_res_1120_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1109_, v_value_1110_, v_safety_boxed_1118_, v_checkMeta_boxed_1119_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* v_00_u03b1_1121_, lean_object* v_expectedType_1122_, lean_object* v_value_1123_, uint8_t v_safety_1124_, uint8_t v_checkMeta_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_evalExpr___redArg(v_expectedType_1122_, v_value_1123_, v_safety_1124_, v_checkMeta_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_expectedType_1133_, lean_object* v_value_1134_, lean_object* v_safety_1135_, lean_object* v_checkMeta_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
uint8_t v_safety_boxed_1142_; uint8_t v_checkMeta_boxed_1143_; lean_object* v_res_1144_; 
v_safety_boxed_1142_ = lean_unbox(v_safety_1135_);
v_checkMeta_boxed_1143_ = lean_unbox(v_checkMeta_1136_);
v_res_1144_ = l_Lean_Meta_evalExpr(v_00_u03b1_1132_, v_expectedType_1133_, v_value_1134_, v_safety_boxed_1142_, v_checkMeta_boxed_1143_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1144_;
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
